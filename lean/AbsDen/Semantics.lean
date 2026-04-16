import AbsDen.Syntax
import AbsDen.Env
import AbsDen.World

/-!
# Denotational interpreter

The interpreter is generic, parameterized by a family `D : Nat → Type` satisfying
the type class `Domain D`.

Environment entries are `EnvEntry D n = Var × Later D n`.
The `look` event is baked into the entry at `let` binding sites, not at
reference sites, matching Agda's `Σ D is-env`.
-/

/-! ## Semantic operations -/

/-- Global elements of a step-indexed family. -/
abbrev El (F : Nat → Type) := {n : Nat} → F n

/-- Environment entry: `Var × ▹D`. -/
abbrev EnvEntry (D : Nat → Type) : Nat → Type := world(Var × ▹D)

/-- Semantic domain: a World with denotational operations. -/
class Domain (D : Nat → Type) extends World D where
  step   : El world(Event → D → D)
  stuck  : El D
  fn     : El world((D → D) → D)
  apply  : El world(D → D → D)
  con    : El world(ConTag → List D → D)
  select : El world(D → List (ConTag × (List D → D)) → D)
  bind   : El world((D → D) → (D → D) → D)

/-! ## Domain helpers at the current stage -/

namespace Domain

def step' {D : Nat → Type} [Domain D] {n : Nat} (e : Event) (d : D n) : D n :=
  Domain.step n (Nat.le_refl n) e n (Nat.le_refl n) d

def fn' {D : Nat → Type} [Domain D] {n : Nat} (f : world(D → D) n) : D n :=
  Domain.fn n (Nat.le_refl n) f

def apply' {D : Nat → Type} [Domain D] {n : Nat} (dv : D n) (da : D n) : D n :=
  Domain.apply n (Nat.le_refl n) dv n (Nat.le_refl n) da

def con' {D : Nat → Type} [Domain D] {n : Nat} (K : ConTag) (ds : List (D n)) : D n :=
  Domain.con n (Nat.le_refl n) K n (Nat.le_refl n) ds

def select' {D : Nat → Type} [Domain D] {n : Nat}
    (dv : D n) (alts : List (ConTag × world(List D → D) n)) : D n :=
  Domain.select n (Nat.le_refl n) dv n (Nat.le_refl n) alts

def bind' {D : Nat → Type} [Domain D] {n : Nat}
    (rhs : World.Function D D n)
    (body : World.Function D D n) : D n :=
  Domain.bind n (Nat.le_refl n) rhs n (Nat.le_refl n) body

end Domain

/-! ## The generic interpreter -/

/-- Postfix notation for World.restrict: `ρ↓` restricts to the current step. -/
macro:max x:term "↓" : term => `(World.restrict $x)

/-- The generic denotational interpreter. -/
def eval {D : Nat → Type} [Domain D] : (e : Exp) → El world(Env D → D)
  | .ref x => fun _ _ ρ => match ρ.find? x with
    | some entry => entry
    | none => Domain.stuck
  | .lam x body => fun k _ ρ =>
    Domain.fn' (fun j hj entry => Domain.step' .app2 (eval body j (Nat.le_refl j) ((ρ↓).bind x entry)))
  | .app e₁ x => fun k _ ρ => match ρ.find? x with
    | some entry =>
      Domain.step' .app1 (Domain.apply' (eval e₁ k (Nat.le_refl k) ρ) entry)
    | none => Domain.stuck
  | .conapp K xs => fun _ _ ρ => match ρ.pmapList xs with
    | some ds => Domain.con' K ds
    | none => Domain.stuck
  | .case' eₛ alts => fun k _ ρ =>
    Domain.step' .case1 (
      Domain.select' (eval eₛ k (Nat.le_refl k) ρ)
        (alts.map fun alt =>
          (alt.con, fun j hj ds =>
            Domain.step' .case2 (eval alt.rhs j (Nat.le_refl j) ((ρ↓).bindMany alt.vars ds)))))
  | .let' x e₁ e₂ => fun k _ ρ =>
    let rhs : World.Function D D k := fun j hj dx =>
      eval e₁ j (Nat.le_refl j) ((ρ↓).bind x (Domain.step' (.look x) dx))
    let body : World.Function D D k :=
      fun j hj dx =>
        Domain.step' .let1 (eval e₂ j (Nat.le_refl j) ((ρ↓).bind x (Domain.step' (.look x) dx)))
    Domain.bind' rhs body
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  · have h_list : sizeOf alt < sizeOf alts := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have h_rhs : sizeOf alt.rhs < sizeOf alt := by
      cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega
