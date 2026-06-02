import AbsDen.Syntax
import AbsDen.Env
import AbsDen.World

/-!
# Denotational interpreter (well-scoped)

The interpreter is generic over a family `D : Nat → Type` with a `Domain D`
instance. The environment is the well-scoped `Env D m`, so variable lookup is
total.
-/

/-! ## Semantic operations -/

/-- Global elements of a step-indexed family. -/
abbrev El (F : Nat → Type) := {n : Nat} → F n

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

mutual

/-- The generic denotational interpreter. -/
def eval {D : Nat → Type} [Domain D] : {m : Nat} → (e : Exp m) →
    El (World.Function (Env D m) D)
  | _, .ref x => fun _ _ ρ => ρ.lookup x
  | _, .lam _ body => fun _ _ ρ =>
    Domain.fn' (fun j _ entry =>
      Domain.step' .app2 (eval body j (Nat.le_refl j) ((ρ↓).bind entry)))
  | _, .app e₁ x => fun k _ ρ =>
    Domain.step' .app1 (Domain.apply' (eval e₁ k (Nat.le_refl k) ρ) (ρ.lookup x))
  | _, .conapp K xs => fun _ _ ρ =>
    Domain.con' K (ρ.mapList xs)
  | _, .case' eₛ alts => fun k _ ρ =>
    Domain.step' .case1
      (Domain.select' (eval eₛ k (Nat.le_refl k) ρ) (evalAlts ρ alts))
  | _, .let' name e₁ e₂ => fun k _ ρ =>
    let rhs : World.Function D D k := fun j _ dx =>
      eval e₁ j (Nat.le_refl j) ((ρ↓).bind (Domain.step' (.look name) dx))
    let body : World.Function D D k :=
      fun j _ dx =>
        Domain.step' .let1
          (eval e₂ j (Nat.le_refl j) ((ρ↓).bind (Domain.step' (.look name) dx)))
    Domain.bind' rhs body

/-- Build the `select` argument from an `AltList`. The `.case2` step is emitted
    unconditionally so the trace always starts with a visible event; arity
    mismatches reduce to `stuck` *under* the step. -/
def evalAlts {D : Nat → Type} [Domain D] {m k : Nat} (ρ : Env D m k) :
    AltList m → List (ConTag × world(List D → D) k)
  | .nil => []
  | .cons c vs rhs rest =>
    (c, fun j _ ds =>
      Domain.step' .case2
        (if h : ds.length = vs.length then
          eval rhs j (Nat.le_refl j) (h ▸ (ρ↓).bindMany ds)
        else Domain.stuck))
    :: evalAlts ρ rest

end
