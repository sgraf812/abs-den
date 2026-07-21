import AbsDen.Semantics
import Iris.BI
import Iris.BI.SIProp
import Iris.ProofMode

/-! # A reusable unary logical relation on a semantic domain

Ported from `AbsDen/LR.lean`. There the domain is a presheaf `D : Nat → Type`
and predicates are `World.Pred D n` (level-indexed, downward-closed). Here the
domain is a single OFE `D` and `eval : Env D -n> D` never restricts the
environment, so the level plumbing collapses: predicates are step-indexed
propositions `D -n> SProp` (their non-expansiveness *is* the old naturality)
and the structure fields are `SProp` entailments, where `SProp` is any
step-indexed BI (`Sbi`), such as `SiProp` or `UPred M`. -/

open Iris Iris.BI Iris.BI.BigAndL Iris.COFE OFE

/-- `persistently` on `SiProp` is the identity, so it commutes with universal
    quantification. -/
instance : BIPersistentlyForall SiProp where
  persistently_sForall_2 Ψ :=
    BI.sForall_intro fun p hp =>
      (and_intro (forall_elim p) (pure_intro hp)).trans imp_elim_left

namespace AbsDen

/-- `≡` inside `iprop` is internal equality: the proposition whose stage `n`
    is `a ≡{n}≡ b`. -/
macro_rules
  | `(iprop($a ≡ $b)) => ``(Iris.internalEq $a $b)

variable {SProp : Type} [Sbi SProp]
variable {D : Type} [OFE D] [Domain D]

/-! ## Look-step value shape -/

/-- `a` is a look-wrapped thunk `Domain.step (.look x) a'`, internally (up to
    the step index), so the shape is a non-expansive predicate and value data
    can carry it. -/
def IsLookShape : D -n> SProp :=
  ⟨fun a => iprop(∃ (x : Var) (a' : D), a ≡ Domain.step (.look x) a'),
   ⟨fun {_ _ _} h => by
     apply exists_ne; intro x
     apply exists_ne; intro a'
     apply NonExpansive₂.ne (f := internalEq) h (OFE.dist_eqv.refl _)⟩⟩

/-- `IsLookShape` congruence, packaged for clients that assemble `Dist` proofs
    by hand. -/
theorem IsLookShape_ne {n} {a a' : D} (h : a ≡{n}≡ a') :
    (IsLookShape a : SProp) ≡{n}≡ IsLookShape a' :=
  IsLookShape.ne.ne h

/-- A `P`-good value that is also look-shaped (what env entries carry). -/
def IsLookup (P : D -n> SProp) (a : D) : SProp :=
  iprop(P a ∧ IsLookShape a)

/-! ## Per-case closure conditions -/

namespace Parametric

/-- `f` maps `IsLookup P` inputs to `P` outputs. -/
def Fn (P : D -n> SProp) (f : D -n> D) : SProp :=
  iprop(∀ a, IsLookup P a → P (f a))

/-- Every field of `ds` is `IsLookup P`. -/
def Con (P : D -n> SProp) (ds : List D) : SProp :=
  [∧list] a ∈ ds, IsLookup P a

/-- Every alternative of a `case` maps `Con P` field-lists to `P` results;
    the middle component is the alternative's arity. -/
def Alts (P : D -n> SProp) (alts : List (ConTag × Nat × (List D -n> D))) : SProp :=
  [∧list] a ∈ alts, iprop(∀ ds, Con P ds → P (a.2.2 ds))

/-- Alternatives as the evaluator builds them: each branch arity-guarded and
    stepped by `.case2`, its arity riding along for the domain's `select`. -/
def stepAlts (alts : List (ConTag × Nat × (List D -n> D))) :
    List (ConTag × Nat × (List D -n> D)) :=
  alts.map fun p => (p.1, p.2.1, ofe_fun ds =>
    if ds.length = p.2.1 then Domain.step .case2 (p.2.2 ds) else Domain.stuck)

/-- `Fn` is non-expansive in the function. -/
theorem Fn_ne {n} (P : D -n> SProp) {f f' : D -n> D} (h : f ≡{n}≡ f') :
    Fn P f ≡{n}≡ Fn P f' := by
  apply forall_ne; intro a
  apply imp_ne.ne
  · apply OFE.dist_eqv.refl
  · exact P.ne.ne (h a)

/-- `Fn` is non-expansive in the predicate. -/
theorem Fn_ne_pred {n} {P P' : D -n> SProp} (h : P ≡{n}≡ P') (f : D -n> D) :
    Fn P f ≡{n}≡ Fn P' f := by
  apply forall_ne; intro a
  apply imp_ne.ne
  · apply and_ne.ne
    · exact h a
    · apply OFE.dist_eqv.refl
  · exact h (f a)

/-- `Con` is non-expansive in the field list. -/
theorem Con_ne {n} (P : D -n> SProp) {ds ds' : List D} (h : ds ≡{n}≡ ds') :
    Con P ds ≡{n}≡ Con P ds' := by
  induction h with
  | nil => apply OFE.dist_eqv.refl
  | cons hx _ ih =>
    apply and_ne.ne
    · apply and_ne.ne
      · exact P.ne.ne hx
      · exact IsLookShape.ne.ne hx
    · exact ih

/-- `Con` is non-expansive in the predicate. -/
theorem Con_ne_pred {n} {P P' : D -n> SProp} (h : P ≡{n}≡ P') (ds : List D) :
    Con P ds ≡{n}≡ Con P' ds := by
  induction ds with
  | nil => apply OFE.dist_eqv.refl
  | cons a ds ih =>
    apply and_ne.ne
    · apply and_ne.ne
      · exact h a
      · apply OFE.dist_eqv.refl
    · exact ih

/-- Pointwise weakening of the per-field lookup predicate lifts to `Con`. -/
theorem Con_mono {P P' : D -n> SProp} (h : ∀ a : D, IsLookup P a ⊢ IsLookup P' a)
    (ds : List D) : Con P ds ⊢ Con P' ds := by
  induction ds with
  | nil => exact .rfl
  | cons a ds ih => exact and_mono (h a) ih

/-- The empty field-list is `Con`-good. -/
theorem Con_nil (P : D -n> SProp) : Con P [] ⊣⊢ (True : SProp) := by
  simp only [Con]; exact bigAndL_nil

/-- `Con` peels off its head. -/
theorem Con_cons (P : D -n> SProp) (a : D) (ds : List D) :
    Con P (a :: ds) ⊣⊢ IsLookup P a ∧ Con P ds := by
  simp only [Con]; exact bigAndL_cons

end Parametric

/-! ## The logical relation -/

/-- A unary logical relation on the semantic domain `D`. `P` is the defining
    predicate; `IsThunk` is what `bind`'s `rhs`/`body` receive on input.
    Each closure field mirrors one `eval` clause. -/
structure LR (SProp : Type) (D : Type) [Sbi SProp] [OFE D] [Domain D] where
  P            : D -n> SProp
  IsThunk      : D -n> SProp
  IsThunk_to_P : ∀ (x : Var) (a : D), IsThunk a ⊢ P (Domain.step (.look x) a)
  stuck        : ⊢ P Domain.stuck
  fn           : ∀ (x : Var) (f : D -n> D),
    Parametric.Fn P f ⊢ P (Domain.fn x ((Domain.step .app2).comp f))
  con          : ∀ (K : ConTag) (ds : List D), Parametric.Con P ds ⊢ P (Domain.con K ds)
  apply   : ∀ (dv da : D),
    P dv ∧ IsLookup P da ⊢ P (Domain.step .app1 (Domain.apply dv da))
  select  : ∀ (dv : D) (alts : List (ConTag × Nat × (List D -n> D))),
    P dv ∧ Parametric.Alts P alts
      ⊢ P (Domain.step .case1 (Domain.select dv (Parametric.stepAlts alts)))
  bind  : ∀ (rhs body : D -n> D),
    (∀ a, IsThunk a → P (rhs a)) ∧ (∀ a, IsThunk a → P (body a))
      ⊢ P (Domain.step .let1 (Domain.bind rhs body))

namespace LR

variable {SProp : Type} [Sbi SProp]
variable {D : Type} [OFE D] [Domain D]

/-! ## Generic helpers -/

/-- Weaken an emp-valid entailment against any premise (affinity). -/
theorem of_empValid [BIAffine SProp] {Q : SProp} (h : ⊢ Q) {P : SProp} : P ⊢ Q :=
  true_intro.trans (true_emp.1.trans h)

/-- An emp-valid proposition holds boxed against any premise: `emp` is
    intuitionistic. -/
theorem of_empValid_box [BIAffine SProp] {Q : SProp} (h : ⊢ Q) {P : SProp} : P ⊢ iprop(□ Q) :=
  true_intro.trans (true_emp.1.trans (intuitionistically_emp.2.trans (intuitionistically_mono h)))

/-- A literal look-wrapping is look-shaped. -/
theorem IsLookShape_intro (x : Var) (a : D) :
    ⊢ (IsLookShape (Domain.step (.look x) a) : SProp) := by
  refine .trans ?_ (exists_intro x)
  refine .trans ?_ (exists_intro a)
  exact internalEq.refl

/-- Package a `P`-value at a look-wrapping into an `IsLookup`. -/
theorem IsLookup_look_intro [BIAffine SProp] {X : SProp} {P : D -n> SProp} {x : Var} {a : D}
    (h : X ⊢ P (Domain.step (.look x) a)) :
    X ⊢ IsLookup P (Domain.step (.look x) a) :=
  and_intro h (of_empValid (IsLookShape_intro x a))

/-! ## Derived coherences -/

/-- Forcing an `IsLookup` yields a `P`. -/
theorem IsLookup_to_P (P : D -n> SProp) (a : D) : IsLookup P a ⊢ P a := by
  simp only [IsLookup]; exact and_elim_l

/-! ## Env-level closure -/

/-- An environment is good when every entry is `IsLookup lr.P`. -/
def EnvOk (lr : LR SProp D) (ρ : Env D) : SProp :=
  iprop(∀ (x : Var) (a : D), ⌜ρ.get x = some a⌝ → IsLookup lr.P a)

/-- The empty env is good. -/
theorem envOk_empty (lr : LR SProp D) : ⊢ lr.EnvOk (Env.empty : Env D) := by
  simp only [EnvOk]
  refine forall_intro fun x => forall_intro fun a => imp_intro ?_
  refine pure_elim _ and_elim_r (fun hx => ?_)
  simp only [Env.get, Env.empty] at hx
  exact absurd hx (by simp)

/-- A bound entry of a good env is `IsLookup lr.P`. -/
theorem envOk_get (lr : LR SProp D) (ρ : Env D) (x : Var) (a : D) (h : ρ.get x = some a) :
    lr.EnvOk ρ ⊢ IsLookup lr.P a := by
  simp only [EnvOk]
  refine .trans (forall_elim x) ?_
  refine .trans (forall_elim a) ?_
  exact (and_intro .rfl (pure_intro h)).trans imp_elim_left

/-- Binding an `IsLookup`-value extends a good env. -/
theorem envOk_extend (lr : LR SProp D) (ρ : Env D) (x : Var) (a : D) :
    lr.EnvOk ρ ∧ IsLookup lr.P a ⊢ lr.EnvOk (ρ[x ↦ a]) := by
  simp only [EnvOk]
  refine forall_intro fun y => forall_intro fun b => imp_intro ?_
  refine pure_elim _ and_elim_r (fun hb => ?_)
  simp only [Env.get, Env.extend] at hb
  split at hb
  · obtain rfl := Option.some.inj hb
    exact and_elim_l.trans and_elim_r
  · exact (and_elim_l.trans and_elim_l).trans (envOk_get lr ρ y b hb)

/-- Binding a `Con`-good list extends a good env. -/
theorem envOk_extendMany (lr : LR SProp D) (ρ : Env D) (xs : List Var) (ds : List D) :
    lr.EnvOk ρ ∧ Parametric.Con lr.P ds ⊢ lr.EnvOk ρ[xs ↦* ds] := by
  induction xs generalizing ρ ds with
  | nil => exact and_elim_l
  | cons x xs ih =>
    cases ds with
    | nil => exact and_elim_l
    | cons v vs =>
      simp only [Env.extendMany]
      refine .trans (and_mono_right (Parametric.Con_cons lr.P v vs).1) ?_
      refine .trans (and_intro ?_ (and_elim_r.trans and_elim_r)) (ih (ρ[x ↦ v]) vs)
      exact (and_mono_right and_elim_l).trans (envOk_extend lr ρ x v)

/-- A successful `getMany` from a good env yields a `Con`-good list. -/
theorem envOk_getMany (lr : LR SProp D) (ρ : Env D) :
    (xs : List Var) → (ds : List D) → ρ.getMany xs = some ds →
      (lr.EnvOk ρ ⊢ Parametric.Con lr.P ds)
  | [], ds, h => by
    simp only [Env.getMany, Option.some.injEq] at h
    subst h
    exact true_intro.trans (Parametric.Con_nil lr.P).2
  | x :: xs, ds, h => by
    simp only [Env.getMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, hx, ds', hds', rfl⟩ := h
    refine .trans (and_intro (envOk_get lr ρ x a hx) (envOk_getMany lr ρ xs ds' hds'))
      (Parametric.Con_cons lr.P a ds').2

/-! ## Fundamental lemma -/

/-- **Fundamental Lemma.** A good env sends `eval e` into `lr.P`. -/
theorem fundamental [BIAffine SProp] (lr : LR SProp D) :
    (e : Exp) → (ρ : Env D) → (lr.EnvOk ρ ⊢ lr.P (eval e ρ))
  | .ref x, ρ => by
    simp only [eval]
    cases h : ρ.get x with
    | none => exact of_empValid lr.stuck
    | some a => exact (envOk_get lr ρ x a h).trans (IsLookup_to_P lr.P a)
  | .conapp K xs, ρ => by
    simp only [eval]
    cases h : ρ[xs]? with
    | none => exact of_empValid lr.stuck
    | some ds =>
      refine .trans ?_ (lr.con K ds)
      exact envOk_getMany lr ρ xs ds h
  | .lam x body, ρ => by
    simp only [eval]
    refine .trans ?_ (lr.fn x (ofe_fun a => eval body ρ[x ↦ a]))
    simp only [Parametric.Fn]
    refine forall_intro fun a => imp_intro ?_
    refine .trans ?_ (fundamental lr body (ρ[x ↦ a]))
    exact envOk_extend lr ρ x a
  | .app e x, ρ => by
    simp only [eval]
    cases h : ρ.get x with
    | none => exact of_empValid lr.stuck
    | some a =>
      refine .trans ?_ (lr.apply (eval e ρ) a)
      exact and_intro (fundamental lr e ρ) (envOk_get lr ρ x a h)
  | .«case» eₛ alts, ρ => by
    simp only [eval]
    have halts : (alts.attach.map (fun alt =>
        (alt.1.con, alt.1.vars.length, ofe_fun ds =>
          if ds.length = alt.1.vars.length then
            Domain.step .case2 (eval alt.1.rhs ρ[alt.1.vars ↦* ds])
          else Domain.stuck)))
        = Parametric.stepAlts (alts.attach.map (fun alt =>
            (alt.1.con, alt.1.vars.length,
              ofe_fun ds => eval alt.1.rhs ρ[alt.1.vars ↦* ds]))) := by
      simp only [Parametric.stepAlts, List.map_map]
      rfl
    rw [halts]
    refine .trans ?_ (lr.select (eval eₛ ρ) _)
    refine and_intro (fundamental lr eₛ ρ) ?_
    simp only [Parametric.Alts]
    refine bigAndL_intro (fun k a hget => ?_)
    rw [List.getElem?_map] at hget
    obtain ⟨alt, _, rfl⟩ := Option.map_eq_some_iff.mp hget
    refine forall_intro fun ds => imp_intro ?_
    refine .trans ?_ (fundamental lr alt.1.rhs ρ[alt.1.vars ↦* ds])
    exact envOk_extendMany lr ρ alt.1.vars ds
  | .«let» x e₁ e₂, ρ => by
    simp only [eval]
    refine .trans ?_ (lr.bind _ _)
    refine and_intro ?_ ?_
    · refine forall_intro fun a => imp_intro ?_
      refine .trans ?_ (fundamental lr e₁ (ρ[x ↦ Domain.step (.look x) a]))
      refine .trans ?_ (envOk_extend lr ρ x (Domain.step (.look x) a))
      exact and_intro and_elim_l (and_elim_r.trans (IsLookup_look_intro (lr.IsThunk_to_P x a)))
    · refine forall_intro fun a => imp_intro ?_
      refine .trans ?_ (fundamental lr e₂ (ρ[x ↦ Domain.step (.look x) a]))
      refine .trans ?_ (envOk_extend lr ρ x (Domain.step (.look x) a))
      exact and_intro and_elim_l (and_elim_r.trans (IsLookup_look_intro (lr.IsThunk_to_P x a)))
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

end LR

end AbsDen
