import Lean.Elab.Tactic
import AbsDen.IrisExtensions

/-! # A compositional solver for `NonExpansive`

`NonExpansive f` is established from the non-expansiveness of `f`'s parts. The
`ne_solve` tactic walks the goal: it introduces a `∀`, closes a leaf by instance
synthesis (every `-n>` combinator and the env operations populate the
`NonExpansive`/`NonExpansive₂` database), and otherwise dispatches on the head of
the function body to the matching composition rule.

Dispatching on the head (rather than blindly back-tracking through `refine`)
matters: the conclusions of `ne_homCod`/`ne_optionElimBranch` are higher-order,
so trying them against a non-matching goal makes unification deep-`whnf` the
`Domain` operations. Inspecting the head first applies exactly one rule. This is
the `fun_prop`/`mono` shape, specialised to `NonExpansive` and small enough not
to need a general framework. -/

open Iris Iris.COFE OFE

namespace AbsDen

variable {α β γ δ : Type} [OFE α] [OFE β] [OFE γ] [OFE δ]

/-- Compose two non-expansive maps. -/
theorem ne_comp {g : β → γ} {h : α → β}
    (hg : NonExpansive g) (hh : NonExpansive h) : NonExpansive (fun a => g (h a)) :=
  NonExpansive.comp hg hh

/-- Apply a binary non-expansive map to two non-expansive maps. -/
theorem ne_comp₂ {g : β → γ → δ} {h₁ : α → β} {h₂ : α → γ}
    (hg : NonExpansive₂ g) (h₁' : NonExpansive h₁) (h₂' : NonExpansive h₂) :
    NonExpansive (fun a => g (h₁ a) (h₂ a)) :=
  ⟨fun _ _ _ e => hg.ne (h₁'.ne e) (h₂'.ne e)⟩

/-- A morphism-valued non-expansive map (a closure handed to `fn`/`bind`):
    pointwise non-expansiveness in the captured argument suffices. -/
theorem ne_homCod {F : α → β → γ} {pf : ∀ x, NonExpansive (fun a => F x a)}
    (h : ∀ a, NonExpansive (fun x => F x a)) :
    NonExpansive (fun x => (Hom.mk (fun a => F x a) (pf x) : β -n> γ)) :=
  ⟨fun {_ _ _} e a => (h a).ne e⟩

/-- `Option.elim` with a morphism branch is non-expansive in the option and the
    branch (default fixed). The branch must be a morphism: as the option's value
    moves, the branch is applied at distinct points. -/
instance ne_optionElim (s : β) :
    NonExpansive₂ (fun (o : Option α) (f : α -n> β) => o.elim s f) :=
  ⟨fun {_ o o'} ho {f f'} hf => by
    rcases o with _ | a <;> rcases o' with _ | a'
    · exact OFE.dist_eqv.refl _
    · exact ho.elim
    · exact ho.elim
    · exact OFE.Dist.trans (hf a) (f'.ne.ne ho)⟩

/-- `Option.elim` with a default and a branch that may depend on the captured
    argument. Reduces to non-expansiveness of the scrutinee and of the branch. -/
theorem ne_optionElimBranch {o : α → Option β} {s : γ} {F : α → β → γ}
    (ho : NonExpansive o) (hx : ∀ b, NonExpansive (fun a => F a b))
    (ha : ∀ a, NonExpansive (fun b => F a b)) :
    NonExpansive (fun a => Option.elim (o a) s (fun b => F a b)) :=
  ne_comp₂ (ne_optionElim s) ho (ne_homCod (pf := ha) hx)

/-- `Option.getD` is non-expansive in the option and the default. -/
instance ne_getD : NonExpansive₂ (Option.getD : Option α → α → α) := by
  refine ⟨fun {_ o o'} ho {s s'} hs => ?_⟩
  rcases o with _ | a <;> rcases o' with _ | a'
  · exact hs
  · exact ho.elim
  · exact ho.elim
  · exact some_dist_some.mp ho

/-- `ite` at a fixed condition is non-expansive in both branches. -/
instance ne_ite (c : Prop) [Decidable c] :
    NonExpansive₂ (fun (a b : α) => if c then a else b) :=
  ⟨fun {_ _ _} ha {_ _} hb => by split <;> assumption⟩

/-- `n`-close lists have equal length: list distance is pointwise. -/
theorem List.dist_length_eq {ι : Type _} [OFE ι] {n : Nat} {l l' : List ι}
    (h : l ≡{n}≡ l') : l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The arity test of a `case` branch: the length of the varying list is
    dist-invariant, so `ite` dispatches to its branches (drives the guard in
    `eval`'s alternatives). -/
theorem ne_iteLength {k : Nat} {s : β} {F : List α → β} (hF : NonExpansive F) :
    NonExpansive (fun ds : List α => if ds.length = k then F ds else s) :=
  ⟨fun {_ ds ds'} h => by
    rw [List.dist_length_eq h]
    exact (ne_ite (ds'.length = k)).ne (hF.ne h) (OFE.dist_eqv.refl s)⟩

/-- `ite` at a condition the captured argument does not vary is non-expansive
    when its branches are. -/
theorem ne_iteFix {c : Prop} [Decidable c] {F G : α → β}
    (hF : NonExpansive F) (hG : NonExpansive G) :
    NonExpansive (fun a => if c then F a else G a) :=
  ⟨fun {_ _ _} h => (ne_ite c).ne (hF.ne h) (hG.ne h)⟩

/-- Mapping a captured-argument-dependent function over a fixed list is
    non-expansive when each element is (drives `case`'s alternative list). -/
theorem ne_listMap {ι : Type} {F : α → ι → β} {xs : List ι}
    (h : ∀ a, NonExpansive (fun x => F x a)) :
    NonExpansive (fun x => xs.map (fun a => F x a)) := by
  refine ⟨fun {_ _ _} e => ?_⟩
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a _ ih => exact List.Forall₂.cons ((h a).ne e) ih

/-! ## The `ne_solve` tactic -/

open Lean Meta Elab Tactic

/-- The head symbol of the body of the function in a `NonExpansive _` goal. -/
private def neBodyHead (ty : Expr) : MetaM (Option Name) := do
  match ty.getAppFnArgs with
  | (``Iris.OFE.NonExpansive, args) =>
      if h : args.size = 5 then
        match ← whnf args[4] with
        | .lam _ _ body _ => return body.getAppFn.constName?
        | _ => return none
      else return none
  | _ => return none

/-- Discharge a `NonExpansive` goal compositionally (see the module comment). -/
private partial def neSolveCore (mvar : MVarId) : MetaM Unit := mvar.withContext do
  let ty ← instantiateMVars (← mvar.getType)
  if ty.isForall then
    return ← neSolveCore (← mvar.intro1).2
  if ← (try let v ← synthInstance ty; mvar.assign v; pure true catch _ => pure false) then
    return
  let apply' (n : Name) : MetaM (List MVarId) := do mvar.apply (← mkConstWithFreshMVarLevels n)
  match ← neBodyHead ty with
  | some ``Option.elim => (← apply' ``ne_optionElimBranch).forM neSolveCore
  | some ``List.map => (← apply' ``ne_listMap).forM neSolveCore
  | some ``ite =>
      -- the arity guard tests the varying list's length; any other `ite`'s
      -- condition is fixed by the captured argument
      if (← whnf ty.getAppArgs[0]!).isAppOf ``List then
        (← apply' ``ne_iteLength).forM neSolveCore
      else
        (← apply' ``ne_iteFix).forM neSolveCore
  | some ``Iris.OFE.Hom.mk => (← apply' ``ne_homCod).forM neSolveCore
  | _ =>
      let s ← saveState
      try (← apply' ``ne_comp₂).forM neSolveCore
      catch _ => restoreState s; (← apply' ``ne_comp).forM neSolveCore

elab "ne_solve" : tactic => liftMetaTactic fun g => do neSolveCore g; pure []

open Lean.Parser.Term in
macro:max "ofe_fun" f:basicFun : term => `(Hom.mk (fun $f:basicFun) (by ne_solve))

/-! ## `ofe_norm`: a cbv/simp engine whose relation is `≡`, congruence is `NonExpansive`

`ofe_norm [rules]` normalises the left side of an `≡` goal by the `≡`-oriented
`rules` (one-layer reductions such as the trace `_run` rules). Every proof it
builds is an `OFE.Equiv`: a redex is rewritten by a rule (`Trans` of `≡`), and a
rewrite under a subterm is justified by `NonExpansive.eqv` (a non-expansive `f`
sends `a ≡ a'` to `f a ≡ f a'`). `Eq` never appears. It reaches head normal form;
a redex guarded by `Later` stays a thunk. -/

/-- `a ≡ a`. -/
private def mkOfeRefl (a : Expr) : MetaM Expr := mkAppOptM ``OFE.Equiv.rfl #[none, none, some a]

/-- Transitivity of `≡`. -/
private def mkOfeTrans (h₁ h₂ : Expr) : MetaM Expr := mkAppM ``OFE.Equiv.trans #[h₁, h₂]

/-- Rewrite `e` at the head with one `≡`-rule: returns `(reduct, e ≡ reduct)`. -/
private def tryOfeRule (rule : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let c ← mkConstWithFreshMVarLevels rule
  let (mvars, _, body) ← forallMetaTelescope (← inferType c)
  match body.getAppFnArgs with
  | (``OFE.Equiv, args) =>
      if h : args.size = 4 then
        if ← isDefEq args[2] e then
          return some (← instantiateMVars args[3], ← instantiateMVars (mkAppN c mvars))
        else return none
      else return none
  | _ => return none

/-- Lift `pa : a ≡ a'` to `f a ≡ f a'` when `f` is non-expansive. -/
private def tryOfeCongr (f a a' pa : Expr) : MetaM (Option Expr) := do
  try return some (← mkAppOptM ``Iris.OFE.NonExpansive.eqv
        #[none, none, none, none, some f, none, some a, some a', some pa])
  catch _ => return none

/-- Normalise `e` under `≡`: head reduction by `rules`, then non-expansive
    congruence into the last argument. Returns `(normalForm, e ≡ normalForm)`. -/
private partial def ofeNorm (rules : Array Name) (e : Expr) : MetaM (Expr × Expr) := do
  for r in rules do
    if let some (rhs, prf) ← tryOfeRule r e then
      let (nf, prf2) ← ofeNorm rules rhs
      return (nf, ← mkOfeTrans prf prf2)
  if e.isApp then
    let f := e.appFn!
    let a := e.appArg!
    -- Only descend into an argument that itself carries an OFE.
    if ← (do try let _ ← mkOfeRefl a; pure true catch _ => pure false) then
      let (a', pa) ← ofeNorm rules a
      unless ← isDefEq a a' do
        if let some congr ← tryOfeCongr f a a' pa then
          let (nf, prf2) ← ofeNorm rules (mkApp f a')
          return (nf, ← mkOfeTrans congr prf2)
  return (e, ← mkOfeRefl e)

/-- Normalise the left side of an `≡` goal with the given `≡`-rules; closes the
    goal when the normal form equals the right side, else leaves `nf ≡ rhs`. -/
elab "ofe_norm" "[" rules:ident,* "]" : tactic => do
  let ruleNames ← rules.getElems.toList.mapM (fun r => realizeGlobalConstNoOverload r.raw)
  liftMetaTactic fun mvar => do
    match (← instantiateMVars (← mvar.getType)).getAppFnArgs with
    | (``OFE.Equiv, args) =>
        if h : args.size = 4 then
          let (nf, prf) ← ofeNorm ruleNames.toArray args[2]
          if ← isDefEq nf args[2] then throwError "ofe_norm: no reduction"
          let newGoal ← mkFreshExprMVar (← mkAppM ``OFE.Equiv #[nf, args[3]])
          mvar.assign (← mkOfeTrans prf newGoal)
          if ← isDefEq nf args[3] then
            newGoal.mvarId!.assign (← mkOfeRefl nf); return []
          return [newGoal.mvarId!]
        else throwError "ofe_norm: goal is not `≡`"
    | _ => throwError "ofe_norm: goal is not `≡`"

end AbsDen
