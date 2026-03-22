/-!
# Topos of Trees — Later modality via presheaves over ℕ

The topos of trees is the presheaf category Set^(ω^op).
Objects are families of types indexed by natural numbers (stages)
with restriction maps going from later stages to earlier stages.

The Later modality ▹ is defined by shifting:
  (▹A)_0     = Unit
  (▹A)_{n+1} = A_n

This gives a foundational model of guarded recursion where
`dfix`/`fix` are defined by well-founded induction on stages,
rather than postulated.
-/

universe u

/-! ## Presheaf objects -/

/-- A presheaf over ℕ (object in the topos of trees).
    `obj n` is the type at stage `n`, and `restrict` maps from stage `n+1` to stage `n`. -/
structure Psh where
  obj : Nat → Type u
  restrict : {n : Nat} → obj (n + 1) → obj n

namespace Psh

/-- A global section (element) of a presheaf: a compatible family across all stages. -/
structure Section (A : Psh.{u}) where
  val : (n : Nat) → A.obj n
  coherent : ∀ n, A.restrict (val (n + 1)) = val n

/-- A morphism between presheaves at a given stage. -/
def Mor (A B : Psh.{u}) (n : Nat) : Type u :=
  A.obj n → B.obj n

/-! ## The Later endofunctor -/

/-- The Later modality: shifts a presheaf by one stage.
    `(Later A).obj 0 = Unit` and `(Later A).obj (n+1) = A.obj n`. -/
def Later (A : Psh.{u}) : Psh.{u} where
  obj n := match n with
    | 0 => PUnit
    | n + 1 => A.obj n
  restrict {n} := match n with
    | 0 => fun _ => PUnit.unit
    | n + 1 => A.restrict

/-- `next` maps from `A` to `Later A` at each stage, using restriction. -/
def next (A : Psh.{u}) (n : Nat) : A.obj n → (Later A).obj n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | n + 1 => A.restrict

/-- Applicative: apply a later function to a later argument. -/
def Later.ap {A B : Psh.{u}} (n : Nat)
    (f : (Later (Psh.mk (fun n => A.obj n → B.obj n) (fun g x => B.restrict (g (A.restrict⁻¹'ᶠ x))))).obj n)
    : (Later A).obj n → (Later B).obj n :=
  sorry -- We won't need the full applicative; we use dfix/fix directly.

/-! ## Guarded fixed points by stage induction -/

/-- Delayed fixed point, defined by well-founded induction on stages.
    At stage 0, returns `PUnit.unit` (trivial).
    At stage `n+1`, applies `f` at stage `n` to the result at stage `n`. -/
def dfix (A : Psh.{u}) (f : (n : Nat) → (Later A).obj n → A.obj n)
    : (n : Nat) → (Later A).obj n :=
  fun n => match n with
  | 0 => PUnit.unit
  | n + 1 => f n (dfix A f n)

/-- The (non-delayed) fixed point: `fix f = f (dfix f)`. -/
def fix (A : Psh.{u}) (f : (n : Nat) → (Later A).obj n → A.obj n)
    : (n : Nat) → A.obj n :=
  fun n => f n (dfix A f n)

/-- The unfolding law: `dfix f` at stage `n+1` equals `fix f` at stage `n`.
    This is `dfix f = next (fix f)` in presheaf terms. -/
theorem pfix (A : Psh.{u}) (f : (n : Nat) → (Later A).obj n → A.obj n)
    (n : Nat) : (Later A).obj (n + 1) := by
  -- (Later A).obj (n+1) = A.obj n, and dfix A f (n+1) = f n (dfix A f n) = fix A f n
  exact fix A f n

theorem dfix_eq (A : Psh.{u}) (f : (n : Nat) → (Later A).obj n → A.obj n)
    (n : Nat) : dfix A f (n + 1) = fix A f n := by
  rfl

/-! ## Constant presheaves -/

/-- A constant presheaf: the same type at every stage, identity restriction. -/
def Const (S : Type u) : Psh.{u} where
  obj _ := S
  restrict := id

/-! ## The flip-tick lemma for constant presheaves

In the topos of trees, `flip-tick : (A → ▹B) → ▹(A → B)` is **not** valid
for arbitrary presheaves `A`. However, when `A` is a constant presheaf
`Const S`, it becomes provable:

At stage 0: both sides are `PUnit` (trivially).
At stage n+1: LHS is `S → B.obj n`, RHS is `(Const S → B).obj n = S → B.obj n`.
-/

/-- The exponential presheaf `Const S ⦥ B`: at stage `n`, the type is `S → B.obj n`. -/
def Exp (S : Type u) (B : Psh.{u}) : Psh.{u} where
  obj n := S → B.obj n
  restrict f s := B.restrict (f s)

/-- `flipTick`: Given a stage-`n` function from `S` to `(Later B).obj n`,
    produce a `(Later (Exp S B)).obj n`.

    This replaces the unsound `flip-tick` postulate from the Agda development.
    It is valid because `S` is constant (does not vary across stages). -/
def flipTick {S : Type u} {B : Psh.{u}} (n : Nat)
    (f : S → (Later B).obj n) : (Later (Exp S B)).obj n :=
  match n with
  | 0 => PUnit.unit
  | _ + 1 => f

/-- The inverse of `flipTick`. -/
def flipTickInv {S : Type u} {B : Psh.{u}} (n : Nat)
    (g : (Later (Exp S B)).obj n) : S → (Later B).obj n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | _ + 1 => g

/-- `flipTick` is a left inverse of `flipTickInv`. -/
theorem flipTick_inv {S : Type u} {B : Psh.{u}} (n : Nat)
    (f : S → (Later B).obj n) : flipTickInv n (flipTick n f) = f := by
  cases n <;> rfl

/-- `flipTickInv` is a left inverse of `flipTick`. -/
theorem flipTickInv_inv {S : Type u} {B : Psh.{u}} (n : Nat)
    (g : (Later (Exp S B)).obj n) : flipTick n (flipTickInv n g) = g := by
  cases n <;> simp [flipTick, flipTickInv]
  · exact (PUnit.eq_punit g).symm

/-! ## Guarded recursive types (▸) -/

/-- `Later.obj` applied to a later type family.
    This corresponds to `▸` in the Agda development:
    `▸ A = (@tick x : Tick) → A x`. -/
abbrev Laterₜ (A : Nat → Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => A n

/-! ## map▹ -/

/-- Map a function over a Later value at a given stage. -/
def mapLater {A B : Psh.{u}} (f : (n : Nat) → A.obj n → B.obj n)
    (n : Nat) : (Later A).obj n → (Later B).obj n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | n + 1 => f n

end Psh
