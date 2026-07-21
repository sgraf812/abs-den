import Std.Data.HashMap
import Init.Data.Order.Classes
import Init.Data.Order.Lemmas
import AbsDen.AbstractDomain

/-! # Usage analysis

The summary-based usage analysis of *Abstracting Denotational Interpreters*
(`StaticAnalysis.lhs`): the usage lattice `U`, usage environments `Uses`, the
finite abstract domain `UD = UT UValue` with its `AbstractDomain` instance
(hence a `Domain` over `UD`'s discrete OFE), and the analysis `evalUsg` as the
generic interpreter instantiated at `UD`. The `#guard`s at the bottom pin the
paper's example analyses. -/

namespace AbsDen

/-! ## Order theory and Kleene iteration (`Order.hs`) -/

/-- A join-semilattice with a least element. -/
class Lat (a : Type) extends BEq a where
  /-- The least element. -/
  bottom : a
  /-- The least upper bound of two elements. -/
  join : a → a → a

export Lat (bottom)

@[inherit_doc] scoped infixl:68 " ⊔ " => Lat.join

/-- The approximation order induced by the join: `x ⊑ y ↔ x ⊔ y == y`. -/
def Lat.le [Lat a] (x y : a) : Bool := (x ⊔ y) == y

@[inherit_doc] scoped infix:50 " ⊑ " => Lat.le

/-- The `Prop`-valued order induced by the `Bool` approximation order `⊑`. -/
instance instLELat [Lat a] : LE a := ⟨fun x y => (x ⊑ y) = true⟩

theorem le_iff_le [Lat a] {x y : a} : x ≤ y ↔ (x ⊑ y) = true := Iff.rfl

instance [Lat a] : DecidableLE a := fun x y =>
  inferInstanceAs (Decidable ((x ⊑ y) = true))

/-- The join as the order's `Max`, tying into the `Std.LawfulOrderSup`
    vocabulary. -/
instance (priority := low) [Lat a] : Max a := ⟨(· ⊔ ·)⟩

/-- The least upper bound of a list. -/
def lub [Lat a] (xs : List a) : a := xs.foldr (· ⊔ ·) bottom

instance (priority := low) [Lat a] : Inhabited a := ⟨bottom⟩

/-- The lattice has finite height: a strict ascent raises `height`, which
    `heightBound` caps, so inflationary iteration stabilizes. -/
class FiniteHeight (a : Type) [Lat a] where
  height : a → Nat
  heightBound : Nat
  height_le : ∀ x : a, height x ≤ heightBound
  height_lt : ∀ x y : a, (x ⊑ y) = true → (y ⊑ x) = false → height x < height y

/-- The climbing headroom above `x`; strict ascent shrinks it. -/
def FiniteHeight.gap [Lat a] [FiniteHeight a] (x : a) : Nat :=
  FiniteHeight.heightBound (a := a) - FiniteHeight.height x

theorem FiniteHeight.gap_lt [Lat a] [FiniteHeight a] {x y : a}
    (hxy : (x ⊑ y) = true) (hyx : (y ⊑ x) = false) : gap y < gap x := by
  have hlt := FiniteHeight.height_lt x y hxy hyx
  have hle := FiniteHeight.height_le y
  simp only [gap]
  omega

/-- Least pre-fixpoint by inflationary Kleene iteration from `bottom`: ascend
    `x ↦ x ⊔ f x` until it stabilizes, which the finite height guarantees.
    The result satisfies `f x ⊑ x` (`kleeneFix_prefix`); for monotone `f` it
    is the least fixpoint. -/
def kleeneFix.go [Lat a] [Std.IsPreorder a] [Std.LawfulOrderSup a] [FiniteHeight a]
    (f : a → a) (x : a) : a :=
  if h : ((x ⊔ f x) ⊑ x) = true then x else kleeneFix.go f (x ⊔ f x)
termination_by FiniteHeight.gap x
decreasing_by
  exact FiniteHeight.gap_lt (le_iff_le.mp (Std.left_le_max (a := x) (b := f x)))
    (eq_false_of_ne_true h)

@[inherit_doc kleeneFix.go]
def kleeneFix [Lat a] [Std.IsPreorder a] [Std.LawfulOrderSup a] [FiniteHeight a]
    (f : a → a) : a := kleeneFix.go f bottom

/-! ## The usage lattice `U` and `U`-modules -/

/-- Usage cardinality: a variable is looked up at most 0 times, at most 1 time,
    or an unknown number of times. -/
inductive U where
  | u0 | u1 | uω
  deriving BEq, DecidableEq, Repr

/-- The join induced by `u0 ⊏ u1 ⊏ uω`. -/
def U.join : U → U → U
  | .u0, u => u
  | u, .u0 => u
  | .u1, .u1 => .u1
  | _, _ => .uω

instance : Lat U where
  bottom := .u0
  join := U.join

/-- A `U`-module: usage addition and scalar multiplication by a usage. -/
class UVec (a : Type) where
  /-- Add the usages of two evaluations that both happen. -/
  add : a → a → a
  /-- Scale a usage by how often the evaluation happens. -/
  smul : U → a → a

instance [UVec a] : Add a := ⟨UVec.add⟩
instance [UVec a] : HMul U a a := ⟨UVec.smul⟩

/-- `u1 + u1 = uω`; any other addition is the join. -/
def U.add : U → U → U
  | .u1, .u1 => .uω
  | v1, v2 => v1 ⊔ v2

/-- `u0` annihilates, `u1` is the identity, `uω` saturates. -/
def U.mul : U → U → U
  | .u0, _ => .u0
  | _, .u0 => .u0
  | .u1, u => u
  | .uω, _ => .uω

instance : UVec U where
  add := U.add
  smul := U.mul

/-! ## Usage environments `Uses` -/

/-- A usage environment: how often each variable is looked up, as a finite map
    reading absent keys as `u0`. Equality thins entries mapped to `u0`, so such a
    key counts as absent. -/
structure Uses where
  ofMap ::
  toMap : Std.HashMap Var U
  deriving Repr

/-- Drop the `u0` entries; the canonical representative for equality. -/
def Uses.thin (φ : Uses) : Std.HashMap Var U := φ.toMap.filter (fun _ u => u != .u0)

/-- Two environments are equal when their `u0`-thinned maps agree. -/
instance : BEq Uses := ⟨fun a b => a.thin == b.thin⟩

/-- The empty usage environment: every variable is absent. -/
def Uses.emp : Uses := ⟨∅⟩

instance : Membership Var Uses := ⟨fun φ x => x ∈ φ.toMap⟩

@[simp] theorem Uses.mem_iff {φ : Uses} {x : Var} : x ∈ φ ↔ x ∈ φ.toMap := Iff.rfl

instance : GetElem? Uses Var U (fun φ x => x ∈ φ) where
  getElem φ x h := φ.toMap[x]'h
  getElem? φ x := φ.toMap[x]?
  getElem! φ x := φ.toMap[x]!

@[simp] theorem Uses.getElem?_toMap (φ : Uses) (x : Var) : φ[x]? = φ.toMap[x]? := rfl

/-- Read the usage of `x`; absent keys are `u0`. -/
def Uses.get (φ : Uses) (x : Var) : U := φ.toMap.getD x .u0

@[inherit_doc] scoped infixl:74 " !? " => Uses.get

/-- The usage environment recording usage `u` of the single variable `x`. -/
def Uses.singenv (x : Var) (u : U) : Uses :=
  if u == .u0 then Uses.emp else ⟨(∅ : Std.HashMap Var U).insert x u⟩

/-- Set the usage of `x` to `u`, erasing the entry when `u` is `u0`. -/
def Uses.ext (φ : Uses) (x : Var) (u : U) : Uses :=
  if u == .u0 then ⟨φ.toMap.erase x⟩ else ⟨φ.toMap.insert x u⟩

/-- Combine two usage environments key-wise with `f`; a key present on one side
    only keeps its usage. -/
def Uses.merge (f : U → U → U) (φ₁ φ₂ : Uses) : Uses :=
  ⟨φ₂.toMap.fold (init := φ₁.toMap) fun acc x u₂ =>
    acc.alter x fun
      | none => some u₂
      | some u₁ => some (f u₁ u₂)⟩

/-- Scale every usage in the environment. -/
def Uses.smul (u : U) (φ : Uses) : Uses :=
  if u == .u0 then Uses.emp else ⟨φ.toMap.map (fun _ v => u * v)⟩

instance : UVec Uses where
  add := Uses.merge U.add
  smul := Uses.smul

instance : Lat Uses where
  bottom := Uses.emp
  join := Uses.merge U.join

/-! ## Value summaries `UValue` -/

/-- A function summary: for each argument position in turn, how often the
    function uses that argument. `rep u` is the infinite repetition
    `cons u (cons u ...)`, so `rep u` and `cons u (rep u)` denote the same
    summary; every operation respects this identity. -/
inductive UValue where
  | cons : U → UValue → UValue
  | rep : U → UValue
  deriving Repr

/-- View a summary as head usage and tail, reading `rep u` as `cons u (rep u)`. -/
def peel : UValue → U × UValue
  | .rep u => (u, .rep u)
  | .cons u v => (u, v)

/-- Equality of summaries modulo `rep u = cons u (rep u)`. -/
def UValue.beq : UValue → UValue → Bool
  | .rep u1, .rep u2 => u1 == u2
  | .cons u1 v1, .cons u2 v2 => u1 == u2 && UValue.beq v1 v2
  | .cons u1 v1, .rep u2 => u1 == u2 && UValue.beq v1 (.rep u2)
  | .rep u1, .cons u2 v2 => u1 == u2 && UValue.beq (.rep u1) v2
  termination_by v1 v2 => sizeOf v1 + sizeOf v2

instance : BEq UValue := ⟨UValue.beq⟩

/-- The position-wise join of two summaries. -/
def UValue.join : UValue → UValue → UValue
  | .rep u1, .rep u2 => .rep (u1 ⊔ u2)
  | .cons u1 v1, .cons u2 v2 => .cons (u1 ⊔ u2) (UValue.join v1 v2)
  | .cons u1 v1, .rep u2 => .cons (u1 ⊔ u2) (UValue.join v1 (.rep u2))
  | .rep u1, .cons u2 v2 => .cons (u1 ⊔ u2) (UValue.join (.rep u1) v2)
  termination_by v1 v2 => sizeOf v1 + sizeOf v2

instance : Lat UValue where
  bottom := .rep .u0
  join := UValue.join

/-! ## Bounded summaries

`UValue` has unbounded ascending chains whose limits are not summaries (the
alternating `cons u1 (cons u0 …)`), so it is not chain complete and the analysis
does not terminate on higher-order recursion. Bounding the number of leading
`cons` cells to a constant `k` cuts the domain down to finitely many summaries,
which is a complete lattice with decidable equality. The order development is
carried out over this bounded subtype. -/

/-- The number of leading `cons` cells before the repeating tail. -/
def UValue.length : UValue → Nat
  | .rep _ => 0
  | .cons _ v => v.length + 1

/-- Joining keeps the longer leading prefix. -/
theorem UValue.length_join (a b : UValue) :
    (UValue.join a b).length = max a.length b.length := by
  fun_induction UValue.join a b <;> simp_all [UValue.length] <;> omega

/-- Summaries with at most `k` leading `cons` cells: a finite sublattice. -/
abbrev UValuek (k : Nat) : Type := {v : UValue // v.length ≤ k}

instance (k : Nat) : BEq (UValuek k) := ⟨fun a b => a.val == b.val⟩

instance (k : Nat) : Lat (UValuek k) where
  bottom := ⟨.rep .u0, Nat.zero_le k⟩
  join a b := ⟨a.val ⊔ b.val, by
    rw [show a.val ⊔ b.val = UValue.join a.val b.val from rfl, UValue.length_join]
    exact Nat.max_le.mpr ⟨a.property, b.property⟩⟩

/-! ## Usage traces `UT` and the domain `UD` -/

/-- A usage trace: a usage environment paired with a value. It abstracts the
    dynamic trace `T` by squashing all `Look x` events into the single entry
    `φ !? x` and discarding all other events. -/
structure UT (v : Type) where
  uses : Uses
  val : v
  deriving BEq, Repr

/-- Sequence two usage computations, adding their usage environments. -/
def UT.bind : UT α → (α → UT β) → UT β
  | ⟨φ1, a⟩, k => let ⟨φ2, b⟩ := k a; ⟨φ1 + φ2, b⟩

instance : Monad UT where
  pure a := ⟨Uses.emp, a⟩
  bind := UT.bind

/-- The usage-analysis domain: usage traces over summaries. -/
abbrev UD := UT UValue

/-- The component-wise join of two usage traces. -/
def UD.join : UD → UD → UD
  | ⟨φ1, v1⟩, ⟨φ2, v2⟩ => ⟨φ1 ⊔ φ2, v1 ⊔ v2⟩

instance : Lat UD where
  bottom := ⟨bottom, bottom⟩
  join := UD.join

/-! ## The `Domain UD` instance (via `AbstractDomain`) -/

/-- Record a variable lookup; every other event is invisible to usage. -/
def UD.step : Event → UD → UD
  | .look x, ⟨φ, v⟩ => ⟨Uses.singenv x .u1 + φ, v⟩
  | _, τ => τ

/-- A stuck expression evaluates nothing. -/
def UD.stuck : UD := bottom

/-- The proxy for a single use of the binder `x` with an unknown argument
    value. -/
def UD.fn.proxy (x : Var) : UD := ⟨Uses.singenv x .u1, .rep .uω⟩

/-- Summarise a lambda: run the body on a proxy for the binder `x`, read off
    the binder's usage as the next summary entry, and drop the binder from the
    usage environment. Distinct binder names keep the probe's reading of `x`
    attributable to the argument alone. -/
def UD.fn (x : Var) (f : UD → UD) : UD :=
  let ⟨φ, v⟩ := f (UD.fn.proxy x)
  ⟨Uses.ext φ x .u0, .cons (φ !? x) v⟩

/-- Apply a summary: the head usage says how many copies of the argument's
    usage the call adds; the tail summarises the result. -/
def UD.apply : UD → UD → UD
  | ⟨φ1, v1⟩, ⟨φ2, _⟩ =>
    match peel v1 with
    | (u, v2) => ⟨φ1 + u * φ2, v2⟩

/-- A constructor is summarised like a lambda that uses every field an unknown
    number of times. -/
def UD.con (_K : ConTag) (ds : List UD) : UD :=
  ds.foldl UD.apply ⟨Uses.emp, .rep .uω⟩

/-- Proxies for the fields of a scrutinised constructor: one unknown value per
    field binder of the alternative. -/
def UD.select.fieldProxies (n : Nat) : List UD :=
  List.replicate n ⟨Uses.emp, .rep .uω⟩

/-- Case analysis: evaluate the scrutinee, run every alternative on unknown
    field values of its arity, and take the upper bound over the alternatives,
    one of which will be taken. -/
def UD.select (d : UD) (fs : List (ConTag × Nat × (List UD → UD))) : UD :=
  d >>= fun _ => lub (fs.map (fun kf => kf.2.2 (UD.select.fieldProxies kf.2.1)))

/-! ## The paper's example analyses

The expected analysis results (from `StaticAnalysis.lhs`, respectively
`Soundness.lhs` for the recursive binding) are checked at the bounded domain
in `AbsDen.BoundedUsage`. -/

/-- `let i = λx.x in i i`: `i` is used once in function and once in argument
    position, joining to `uω`. -/
def usgEx1 : Exp := .«let» "i" (.lam "x" (.ref "x")) (.app (.ref "i") "i")


/-- `let i = λx.x in let j = λy.y in i j j`: `i` is used once, `j` many
    times. -/
def usgEx2 : Exp :=
  .«let» "i" (.lam "x" (.ref "x"))
    (.«let» "j" (.lam "y" (.ref "y")) (.app (.app (.ref "i") "j") "j"))


/-- `let k = λy.λz.y in k a b`: `k` and `a` are used once and `b` is absent,
    even though `b` occurs syntactically. -/
def usgEx3 : Exp :=
  .«let» "k" (.lam "y" (.lam "z" (.ref "y"))) (.app (.app (.ref "k") "a") "b")


/-- `let i = λx.x in let j = λy.y in i i j`: the first-order summary cannot
    see through the indirect call `i i`, so `j` is conservatively reported as
    used many times. -/
def usgEx4 : Exp :=
  .«let» "i" (.lam "x" (.ref "x"))
    (.«let» "j" (.lam "y" (.ref "y")) (.app (.app (.ref "i") "i") "j"))


/-- `let z = Z() in case S(z) of { S(n) → n }` with tags `Z ↦ 0`, `S ↦ 1`:
    the constructor summary uses its field `z` an unknown number of times. -/
def usgEx5 : Exp :=
  .«let» "z" (.conapp 0 []) (.«case» (.conapp 1 ["z"]) [⟨1, ["n"], .ref "n"⟩])


/-- `let i = (λy.λx.x) i in i` (`Soundness.lhs`): a recursive binding solved
    by `kleeneFix`; `i` is used once and its summary uses its first argument
    once. -/
def usgEx6 : Exp :=
  .«let» "i" (.app (.lam "y" (.lam "x" (.ref "x"))) "i") (.ref "i")


/-- `let j = λy.y in j`: `j` is used once and its summary uses its one
    argument once. -/
def usgEx7 : Exp := .«let» "j" (.lam "y" (.ref "y")) (.ref "j")


end AbsDen
