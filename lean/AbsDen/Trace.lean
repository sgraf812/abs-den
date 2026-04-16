import AbsDen.Syntax
import AbsDen.World

/-!
# Trace type `T`

The trace type is defined via `World.Fix` with signature `T.Sig V`:
```
T.Sig V T = world(V ⊕ Event × T)
```
This gives `T V ≅ V ⊕ (Event × ▹(T V))` at each step.
-/

inductive T.F (V X : Nat → Type) (n : Nat) where
  | ret (v : V n)
  | step (ev : Event) (t : X n)
  | invis (t : X n)
  deriving World

deriving instance LocalFunctor for T.F

/-- The signature functor for traces. -/
abbrev T.Sig (V : Nat → Type) := T.F.Rep V

/-- `T V` is the guarded fixpoint: `T V ≅ V ⊕ (Event × ▹(T V))`. -/
def T (V : Nat → Type) : Nat → Type := World.Fix (T.Sig V)

instance T.F.instLocalFunctor_X (V : Nat → Type) [World V] :
    LocalFunctor (fun X => T.F.Rep V X) := by
  derive_local_functor

instance T.F.instLocalFunctor_V (X : Nat → Type) [World X] :
    LocalFunctor (fun V => T.F.Rep V X) := by
  derive_local_functor

instance : LocalFunctor T :=
  World.Fix.instLocalFunctor T.F.Rep
    (fun V => T.F.instLocalFunctor_X V) (fun X => T.F.instLocalFunctor_V X)

namespace T

/-- Unfold: `T V n → T.F V (Later (T V)) n`. -/
def unfold {V : Nat → Type} [World V] {n : Nat} : T V n → T.F V (Later (T V)) n :=
  T.F.ofRep V _ ∘ World.Fix.unfold

/-- Fold: `T.F V (Later (T V)) n → T V n`. -/
def fold {V : Nat → Type} [World V] {n : Nat} : T.F V (Later (T V)) n → T V n :=
  World.Fix.fold ∘ T.F.toRep V _

def ret {V : Nat → Type} [World V] {n : Nat} (v : V n) : T V n := fold (.ret v)
def step {V : Nat → Type} [World V] {n : Nat} (e : Event) (dl : Later (T V) n) : T V n :=
  fold (.step e dl)

/-- Bind: push a continuation through the trace structure.
    When the trace returns a value, apply `k` to continue. -/
def bind {V : Nat → Type} [World V] {n : Nat} (t : T V n) (k : world(V → T V) n) : T V n :=
  match unfold t with
  | .ret v => k n (Nat.le_refl n) v
  | .step ev dl => fold (.step ev (Later.hmap n (fun i _hi t' => bind t' (World.restrict k)) dl))
  | .invis dl => fold (.invis (Later.hmap n (fun i _hi t' => bind t' (World.restrict k)) dl))

end T

/-! ## Value type (shared between ByName and ByNeed) -/

inductive Value.F (D : Nat → Type) (n : Nat) where
  | stuck : Value.F D n
  | fn : world(D → D) n → Value.F D n
  | con : ConTag → world(List D) n → Value.F D n
  deriving World

deriving instance LocalFunctor for Value.F

instance {n : Nat} {D : Nat → Type} : Inhabited (Value.F D n) := ⟨.stuck⟩
