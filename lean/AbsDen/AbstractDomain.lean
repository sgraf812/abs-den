import AbsDen.Semantics

/-!
# Abstract semantic domain

An **abstract** semantic domain is a plain `Type` equipped with the denotational
operations. Unlike a concrete `Domain D` (`D : Nat → Type`, Kripke-style with
the `world(_)`-shape and naturality of `step`), an `AbstractDomain D` has

```
fn : (D → D) → D    apply : D → D → D    bind : (D → D) → (D → D) → D    …
```

These operations are inherently *approximative*: there is no injective
representation of `D → D` as a `D`-value, so any `AbstractDomain` instance
must choose a sound approximation (e.g., function summaries, finite-lattice
widening, partial-evaluation joins).

A `Domain (World.Const D)` instance is derived for any `AbstractDomain D`,
so abstract analyses can plug straight into the generic Kripke interpreter
`eval`. A directly-defined `evalConst` is provided as the simpler-to-reason-
about counterpart, equivalent to `eval` via `World.Const D` (proved
elsewhere by structural induction on `Exp`).
-/

/-- An abstract semantic domain: a `Type` with the denotational operations,
    each potentially approximating. -/
class AbstractDomain (D : Type) where
  step   : Event → D → D
  stuck  : D
  fn     : (D → D) → D
  apply  : D → D → D
  con    : ConTag → List D → D
  select : D → List (ConTag × (List D → D)) → D
  bind   : (D → D) → (D → D) → D

/-- Any `AbstractDomain D` lifts to a (concrete) `Domain (World.Const D)`:
    the Kripke threading is trivial because `World.Const D n = D` at every
    level, and `World.restrictStep` is the identity. -/
instance {D : Type} [cd : AbstractDomain D] : Domain (World.Const D) where
  step _ _ ev _ _ d := cd.step ev d
  stuck := cd.stuck
  fn _ _ f := cd.fn (fun d => f _ (Nat.le_refl _) d)
  apply _ _ dv _ _ da := cd.apply dv da
  con _ _ K _ _ ds := cd.con K ds
  select _ _ dv _ _ alts :=
    cd.select dv (alts.map fun (K, f) => (K, fun ds => f _ (Nat.le_refl _) ds))
  bind m₁ _ rhs m₂ _ body :=
    cd.bind
      (fun d => rhs m₁ (Nat.le_refl _) d)
      (fun d => body m₂ (Nat.le_refl _) d)
  natural_step _ := fun _ => rfl

/-! ## Direct (non-Kripke) interpreter for `AbstractDomain` -/

/-- The denotational interpreter, specialised to an `AbstractDomain`.
    No Kripke threading: the type of `D` is just `Type`. -/
def evalConst {D : Type} [AbstractDomain D] : Exp → Env D → D
  | .ref x, ρ => match ρ.find? x with
    | some entry => entry
    | none => AbstractDomain.stuck
  | .lam x body, ρ =>
    AbstractDomain.fn (fun entry =>
      AbstractDomain.step .app2 (evalConst body (ρ.bind x entry)))
  | .app e₁ x, ρ => match ρ.find? x with
    | some entry =>
      AbstractDomain.step .app1 (AbstractDomain.apply (evalConst e₁ ρ) entry)
    | none => AbstractDomain.stuck
  | .conapp K xs, ρ => match ρ.pmapList xs with
    | some ds => AbstractDomain.con K ds
    | none => AbstractDomain.stuck
  | .case' eₛ alts, ρ =>
    AbstractDomain.step .case1 (
      AbstractDomain.select (evalConst eₛ ρ)
        (alts.map fun alt =>
          (alt.con, fun ds =>
            AbstractDomain.step .case2 (evalConst alt.rhs (ρ.bindMany alt.vars ds)))))
  | .let' x e₁ e₂, ρ =>
    let rhs : D → D := fun dx =>
      evalConst e₁ (ρ.bind x (AbstractDomain.step (.look x) dx))
    let body : D → D := fun dx =>
      AbstractDomain.step .let1
        (evalConst e₂ (ρ.bind x (AbstractDomain.step (.look x) dx)))
    AbstractDomain.bind rhs body
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf; first | omega | skip
  · have := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have : sizeOf alt.rhs < sizeOf alt := by cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega

/-! ## Equivalence with the Kripke `eval` -/

/-- `World.restrict` on `World.Comp Env (World.Const D)` at level `n → n` is
    the identity. The proof routes through `World.restrict_self`. For now
    we only need the `m = n` case — the general `m ≤ n` case would require
    a HashMap-level `Functor.map id = id` lemma, which we don't have. -/
private theorem env_const_restrict (D : Type) {n : Nat}
    (ρ : Env (World.Const D n)) :
    @World.restrict (World.Comp Env (World.Const D)) _ n n ρ (Nat.le_refl n) = ρ :=
  @World.restrict_self (World.Comp Env (World.Const D)) _ n ρ

/-- The simple `AbstractDomain` interpreter agrees with the Kripke `eval`
    specialised to `World.Const D` at every level. Proof: structural
    induction on `e`, using that `World.restrict` on `World.Comp Env
    (World.Const D)` is the identity. -/
theorem evalConst_eq_eval {D : Type} [AbstractDomain D] :
    ∀ (e : Exp) {n : Nat} (ρ : Env D),
      evalConst e ρ = eval (D := World.Const D) e n (Nat.le_refl n) ρ
  | .ref x, n, ρ => by
    simp only [evalConst, eval]
    cases ρ.find? x <;> rfl
  | .lam x body, n, ρ => by
    simp only [evalConst, eval, Domain.fn']
    show AbstractDomain.fn _ = AbstractDomain.fn _
    congr 1; funext entry
    simp only [Domain.step']
    show AbstractDomain.step _ _ = AbstractDomain.step _ _
    congr 1
    rw [env_const_restrict]
    exact evalConst_eq_eval body ((ρ.bind x entry))
  | .app e₁ x, n, ρ => by
    simp only [evalConst, eval]
    cases ρ.find? x with
    | none => rfl
    | some entry =>
      simp only [Domain.step', Domain.apply']
      show AbstractDomain.step _ _ = AbstractDomain.step _ _
      congr 1
      show AbstractDomain.apply _ _ = AbstractDomain.apply _ _
      congr 1
      exact evalConst_eq_eval e₁ ρ
  | .conapp K xs, n, ρ => by
    simp only [evalConst, eval]
    cases ρ.pmapList xs <;> rfl
  | .case' eₛ alts, n, ρ => by
    simp only [evalConst, eval, Domain.step', Domain.select']
    show AbstractDomain.step _ _ = AbstractDomain.step _ _
    congr 1
    show AbstractDomain.select _ _ = AbstractDomain.select _ _
    congr 1
    · exact evalConst_eq_eval eₛ ρ
    · rw [List.map_map]
      apply List.map_congr_left
      intro alt halt_mem
      simp only [Function.comp]
      congr 1; funext ds
      show AbstractDomain.step _ _ = AbstractDomain.step _ _
      congr 1
      rw [env_const_restrict]
      exact evalConst_eq_eval alt.rhs (ρ.bindMany alt.vars ds)
  | .let' x e₁ e₂, n, ρ => by
    simp only [evalConst, eval, Domain.bind', Domain.step']
    show AbstractDomain.bind _ _ = AbstractDomain.bind _ _
    congr 1
    · funext dx
      simp only []
      rw [env_const_restrict]
      exact evalConst_eq_eval e₁ _
    · funext dx
      simp only []
      show AbstractDomain.step _ _ = AbstractDomain.step _ _
      congr 1
      rw [env_const_restrict]
      exact evalConst_eq_eval e₂ _
termination_by e _ _ => sizeOf e
decreasing_by
  all_goals simp_wf; first | omega | skip
  · have := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have : sizeOf alt.rhs < sizeOf alt := by cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega
