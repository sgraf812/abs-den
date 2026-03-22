/-!
# Concrete instances: T, Value, D, ByName, ByNeed

Ported from Concrete.agda. All types are stage-indexed.
-/
import AbsDen.Syntax
import AbsDen.Env
import AbsDen.ToposOfTrees
import AbsDen.Semantics

open Psh

/-! ## The trace monad T -/

/-- The trace monad, stage-indexed.
    At stage 0, we can only return (no steps possible since Later is PUnit).
    At stage n+1, we can step with a delayed continuation at stage n. -/
inductive T (V : Nat → Type) : Nat → Type where
  | ret : V n → T V n
  | step : Event → Laterₜ (T V) n → T V n

namespace T

def bind {V W : Nat → Type} : T V n → (V n → T W n) → T W n
  | .ret a, k => k a
  | .step e t, k =>
    .step e (match n with
      | 0 => PUnit.unit
      | _ + 1 => T.bind t (k ∘ sorry)) -- need to handle stage mismatch
    sorry

end T

/-! ## Value and D as guarded recursive types

In the presheaf model, we define Value and D by well-founded recursion
on the stage index, avoiding the need for NO_POSITIVITY_CHECK.

At stage 0, Value is trivial (no computation possible).
At stage n+1, Value can refer to D at stage n under the Later. -/

/-- Guarded recursive Value type, stage-indexed. -/
inductive Value (τ : Nat → Type → Type) : Nat → Type where
  | stuck : Value τ n
  | fn : (IsEnv (fun n => τ n (Value τ n)) n → τ n (Value τ n)) → Value τ n
  | con : Con → List (IsEnv (fun n => τ n (Value τ n)) n) → Value τ n

-- For now, stub out the rest. The key definitions are the type class instances.

/-! ## ByName -/

/-- ByName wraps τ directly: `ByName τ V n = τ n V`. No heap passing. -/
structure ByName (V : Nat → Type) (n : Nat) where
  get : T V n

namespace ByName

instance : Trace (fun n => ByName V n) where
  step e t := ⟨.step e (match n with
    | 0 => PUnit.unit
    | _ + 1 => (t : ByName V _).get)⟩

-- The ByName bind instance: `bind rhs body` calls `body` with a
-- thunk that re-evaluates `rhs` each time (call-by-name).
-- bind rhs body = body (fix (λ d▹. rhs d▹))

end ByName

/-! ## ByNeed -/

-- Addr for heap addresses
abbrev Addr := Nat

-- Heap maps addresses to delayed D values
-- In the presheaf model, heap entries at stage n+1 contain D values at stage n.

/-! ## TODO: Complete ByNeed implementation

The ByNeed implementation requires:
1. A stage-indexed heap: `Heap n = Std.HashMap Addr (Laterₜ D n)`
2. A state monad transformer over T
3. `fetch` using `flipTick` instead of the postulate
4. `memo` for memoisation
5. `bindByNeed` tying it all together

The key insight for eliminating flip-tick:
In `step (look x) (fetch a)`, `fetch a` needs to bind the heap `μ`
before accessing the delayed entry `μ[a]`. Since Heap is essentially
`Addr → Laterₜ D n` and Addr is a constant type (Nat), we can use
`flipTick` to commute the heap binding past the Later.
-/
