import AbsDen.Semantics

/-! # Abstract semantic domains

Mirrors `AbsDen/AbstractDomain.lean`: an `AbstractDomain` is a plain `Type` with
the denotational operations (no metric, no Kripke threading), as used by
approximating analyses. Any such type becomes a `Domain` over its *discrete* OFE
(where `-n>` is just `→`), so the generic `eval` applies; a directly-recursive
`evalConst` is provided and proved equal to that `eval` instance. -/

open Iris Iris.COFE OFE

namespace AbsDen

/-- An abstract semantic domain: a plain type with the denotational operations,
    each potentially approximating. -/
class AbstractDomain (D : Type) where
  step   : Event → D → D
  stuck  : D
  fn     : Var → (D → D) → D
  apply  : D → D → D
  con    : ConTag → List D → D
  select : D → List (ConTag × Nat × (List D → D)) → D
  bind   : (D → D) → (D → D) → D

/-- The discrete OFE on a plain type: `a ≡{n}≡ b ↔ a = b`. -/
def Discrete (D : Type) : Type := D
instance : COFE (Discrete D) := COFE.ofDiscrete Eq Eq_Equivalence

/-- Over a discrete OFE every function is non-expansive. -/
def discreteHom {A B : Type} (f : A → B) : Discrete A -n> Discrete B :=
  ⟨f, ⟨fun {_ _ _} h => congrArg f h⟩⟩

theorem forall₂_eq {α : Type} {l l' : List α} (h : List.Forall₂ Eq l l') : l = l' := by
  induction h with
  | nil => rfl
  | cons he _ ih => exact he ▸ ih ▸ rfl

/-- The alternatives carried by `Domain.select` over a discrete OFE are determined
    up to equality by their dist, so they translate to `AbstractDomain.select`'s
    plain alternatives uniquely. -/
theorem altsMap_eq {D : Type} {n}
    {alts alts' : List (ConTag × Nat × (List (Discrete D) -n> Discrete D))} (h : alts ≡{n}≡ alts') :
    alts.map (fun p => (p.1, p.2.1, p.2.2.f))
      = alts'.map (fun p => (p.1, p.2.1, p.2.2.f)) := by
  induction h with
  | nil => rfl
  | @cons a b _ _ hab _ ih =>
      have htag : a.1 = b.1 := hab.1
      have har : a.2.1 = b.2.1 := hab.2.1
      have hfn : a.2.2.f = b.2.2.f := funext (fun x => hab.2.2 x)
      simp only [List.map_cons, ih, htag, har, hfn]

/-- Any `AbstractDomain D` is a `Domain` over `D`'s discrete OFE: the operations
    carry over unchanged, non-expansive because the metric is discrete. -/
instance instDomainDiscrete [AbstractDomain D] : Domain (Discrete D) where
  step ev := discreteHom (AbstractDomain.step (D := D) ev)
  stuck := AbstractDomain.stuck (D := D)
  fn x := ⟨fun f => AbstractDomain.fn (D := D) x ⇑f,
    ⟨fun {_ _ _} h => congrArg (AbstractDomain.fn (D := D) x) (funext h)⟩⟩
  apply := ⟨fun v => ⟨fun a => AbstractDomain.apply (D := D) v a, ⟨fun {_ _ _} h => congrArg _ h⟩⟩,
    ⟨fun {_ _ _} h => fun a => congrArg (fun w => AbstractDomain.apply (D := D) w a) h⟩⟩
  con K := ⟨fun ds => AbstractDomain.con (D := D) K ds,
    ⟨fun {_ _ _} h => congrArg _ (forall₂_eq h)⟩⟩
  select := ⟨fun dv =>
      ⟨fun alts => AbstractDomain.select (D := D) dv (alts.map (fun p => (p.1, p.2.1, p.2.2.f))),
        ⟨fun {_ _ _} h => congrArg (AbstractDomain.select (D := D) dv) (altsMap_eq h)⟩⟩,
    ⟨fun {_ _ _} h => fun alts =>
      congrArg (fun w => AbstractDomain.select (D := D) w
        (alts.map (fun p => (p.1, p.2.1, p.2.2.f)))) h⟩⟩
  bind := ⟨fun rhs => ⟨fun body => AbstractDomain.bind (D := D) ⇑rhs ⇑body,
      ⟨fun {_ _ _} h => congrArg _ (funext h)⟩⟩,
    ⟨fun {_ _ _} h => fun body => congrArg (fun r => AbstractDomain.bind (D := D) r ⇑body) (funext h)⟩⟩

/-! The instance operations are the abstract ones (definitionally), as simp rules. -/

@[simp] theorem disc_step [AbstractDomain D] (ev : Event) (a : Discrete D) :
    Domain.step ev a = AbstractDomain.step (D := D) ev a := rfl
@[simp] theorem disc_stuck [AbstractDomain D] :
    (Domain.stuck : Discrete D) = AbstractDomain.stuck (D := D) := rfl
@[simp] theorem disc_fn [AbstractDomain D] (x : Var) (f : Discrete D -n> Discrete D) :
    Domain.fn x f = AbstractDomain.fn (D := D) x ⇑f := rfl
@[simp] theorem disc_apply [AbstractDomain D] (v a : Discrete D) :
    Domain.apply v a = AbstractDomain.apply (D := D) v a := rfl
@[simp] theorem disc_con [AbstractDomain D] (K : ConTag) (ds : List (Discrete D)) :
    Domain.con K ds = AbstractDomain.con (D := D) K ds := rfl
@[simp] theorem disc_bind [AbstractDomain D] (r b : Discrete D -n> Discrete D) :
    Domain.bind r b = AbstractDomain.bind (D := D) ⇑r ⇑b := rfl
@[simp] theorem disc_select [AbstractDomain D] (dv : Discrete D)
    (alts : List (ConTag × Nat × (List (Discrete D) -n> Discrete D))) :
    Domain.select dv alts
      = AbstractDomain.select (D := D) dv (alts.map (fun p => (p.1, p.2.1, p.2.2.f))) :=
  rfl

/-- The denotational interpreter specialised to an `AbstractDomain`: no metric, no
    Kripke threading, ordinary structural recursion on `Exp`. -/
def evalConst [AbstractDomain D] : Exp → Env D → D
  | .ref x, ρ => (ρ.get x).getD AbstractDomain.stuck
  | .lam x body, ρ =>
      AbstractDomain.fn x (fun a => AbstractDomain.step .app2 (evalConst body ρ[x ↦ a]))
  | .app e x, ρ => (ρ.get x).elim AbstractDomain.stuck
      (fun a => AbstractDomain.step .app1 (AbstractDomain.apply (evalConst e ρ) a))
  | .conapp K xs, ρ => ρ[xs]?.elim AbstractDomain.stuck (AbstractDomain.con K)
  | .«case» eₛ alts, ρ => AbstractDomain.step .case1 (AbstractDomain.select (evalConst eₛ ρ)
      (alts.attach.map (fun alt =>
        (alt.1.con, alt.1.vars.length, fun ds =>
          if ds.length = alt.1.vars.length then
            AbstractDomain.step .case2 (evalConst alt.1.rhs ρ[alt.1.vars ↦* ds])
          else AbstractDomain.stuck))))
  | .«let» x e₁ e₂, ρ => AbstractDomain.step .let1 (AbstractDomain.bind
      (fun a => evalConst e₁ ρ[x ↦ AbstractDomain.step (.look x) a])
      (fun a => evalConst e₂ ρ[x ↦ AbstractDomain.step (.look x) a]))
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- `evalConst` agrees with the generic `eval` at the discrete-OFE instance.
    Proved by functional induction on `evalConst` (`Exp` is mutually inductive,
    so plain `induction` does not apply); each clause's recursive calls come with
    their induction hypotheses. -/
theorem evalConst_eq_eval [AbstractDomain D] (e : Exp) (ρ : Env D) :
    evalConst e ρ = eval (d := Discrete D) e ρ := by
  induction e, ρ using evalConst.induct <;>
    simp_all [evalConst, eval, List.map_map, Function.comp_def] <;> rfl

end AbsDen
