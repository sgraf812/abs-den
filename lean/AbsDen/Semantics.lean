/-!
# Denotational interpreter and type class algebra

Ported from Semantics.agda. The generic interpreter is parameterized by
type classes `Trace` and `Domain`. `HasBind` has been merged into `Domain`
(as in the paper).

All types are stage-indexed: a "value" at stage `n` is `D n`, and the
later modality is handled via the `Psh` infrastructure from `ToposOfTrees`.
-/
import AbsDen.Syntax
import AbsDen.Env
import AbsDen.ToposOfTrees

open Psh in

/-! ## Events (trace labels) -/

inductive Event where
  | look : Var → Event
  | update : Event
  | app1 : Event
  | app2 : Event
  | case1 : Event
  | case2 : Event
  | let1 : Event
deriving Repr, BEq

/-! ## Type class definitions

We work with stage-indexed types `D : Nat → Type` throughout.
The "later" of `D` at stage `n` is `Laterₜ D n`:
  - At stage 0: `PUnit`
  - At stage `n+1`: `D n`
-/

/-- The `Trace` class provides a `step` operation that consumes an event
    and a delayed value, producing a value. -/
class Trace (D : Nat → Type) where
  step : Event → Laterₜ D n → D n

/-- The predicate characterising environment elements:
    an element `d : D n` is an "env element" if it has the form
    `step (look x) d▹` for some variable `x` and delayed `d▹`. -/
structure IsEnv (D : Nat → Type) [Trace D] (n : Nat) where
  val : D n
  var : Var
  delayed : Laterₜ D n
  eq : val = Trace.step (Event.look var) delayed

/-- The `Domain` class provides the semantic operations.
    `HasBind` is merged in (as `bind`). -/
class Domain (D : Nat → Type) [Trace D] where
  stuck : D n
  fn : (IsEnv D n → D n) → D n
  apply : D n → IsEnv D n → D n
  con : Con → List (IsEnv D n) → D n
  select : D n → List (Con × (List (IsEnv D n) → D n)) → D n
  bind : Laterₜ (fun n => Laterₜ D n → D n) n → (Laterₜ D n → D n) → D n

/-! ## The generic interpreter -/

/-- The denotational interpreter, defined via guarded recursion (`fix`).
    Parameterised over `D` with `Trace` and `Domain` instances. -/
def eval {D : Nat → Type} [Trace D] [Domain D] (e : Exp) (ρ : Env (IsEnv D n)) : D n :=
  Psh.fix
    (Psh.mk (fun n => Exp → Env (IsEnv D n) → D n) (fun f e ρ => sorry))
    (fun n recurse => sem n recurse)
    n e ρ
where
  sem (n : Nat) (recurse : Laterₜ (fun n => Exp → Env (IsEnv D n) → D n) n)
      : Exp → Env (IsEnv D n) → D n
    | .ref x, ρ =>
      match ρ.lookup x with
      | none => Domain.stuck
      | some ⟨d, _, _, _⟩ => d
    | .lam x body, ρ =>
      Domain.fn (fun d => Trace.step .app2 (mapSem recurse (fun rec => rec body (ρ.bind x d))))
    | .app e x, ρ =>
      match ρ.lookup x with
      | none => Domain.stuck
      | some d => Trace.step .app1 (mapSem recurse (fun rec => Domain.apply (rec e ρ) d))
    | .let' x e₁ e₂, ρ =>
      Domain.bind
        (mapSem recurse (fun rec d₁ =>
          rec e₁ (ρ.bind x (IsEnv.mk (Trace.step (.look x) d₁) x d₁ rfl))))
        (fun d₁ => Trace.step .let1 (mapSem recurse (fun rec =>
          rec e₂ (ρ.bind x (IsEnv.mk (Trace.step (.look x) d₁) x d₁ rfl)))))
    | .conapp K xs, ρ =>
      match ρ.pmapList xs with
      | none => Domain.stuck
      | some ds => Domain.con K ds
    | .case' eₛ alts, ρ =>
      Trace.step .case1 (mapSem recurse (fun rec =>
        Domain.select (rec eₛ ρ) (alts.map (fun alt =>
          (alt.con, fun ds => Trace.step .case2
            (mapSem recurse (fun rec => rec alt.rhs (ρ.bindMany alt.vars ds))))))))
  mapSem {A : Type} (recurse : Laterₜ (fun n => Exp → Env (IsEnv D n) → D n) n)
      (f : (Exp → Env (IsEnv D n) → D n) → A) : Laterₜ (fun _ => A) n :=
    match n with
    | 0 => PUnit.unit
    | _ + 1 => f recurse
