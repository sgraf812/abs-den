import AbsDen.Safety
import AbsDen.UsesLattice

/-! # The bounded usage domain as a complete lattice

The order development for the `k`-bounded summaries `UValuek k`, carried out
through the pointwise view: a summary denotes the stream of usages it assigns to
each argument position (`UValue.At`), `rep u` being the constant tail. Two
summaries are equal exactly when their streams agree, and one approximates
another exactly when its stream is pointwise below, so the `rep`/`cons` quotient
never has to be reasoned about directly. Since `U` is finite and a `k`-bounded
summary is constant past position `k`, this presents `UValuek k` as a finite,
hence complete, lattice. -/

namespace AbsDen

/-! ## The usage lattice `U` -/

/-- `U`'s approximation is reflexive. -/
theorem U.le_refl (a : U) : (a ⊑ a) = true := by cases a <;> rfl

/-- `U`'s approximation is transitive. -/
theorem U.le_trans {a b c : U} : (a ⊑ b) = true → (b ⊑ c) = true → (a ⊑ c) = true := by
  cases a <;> cases b <;> cases c <;> decide

/-- `U`'s `BEq` reflects equality. -/
theorem U.beq_iff_eq {a b : U} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- `U`'s approximation is join membership. -/
theorem U.le_iff_join {a b : U} : (a ⊑ b) = true ↔ a ⊔ b = b := U.beq_iff_eq

instance : Std.IsPreorder U where
  le_refl := U.le_refl
  le_trans _ _ _ := U.le_trans

instance : Std.LawfulOrderSup U where
  max_le_iff a b c := by cases a <;> cases b <;> cases c <;> decide

/-- The height of a usage: `u0 ⊏ u1 ⊏ uω`. -/
def U.height : U → Nat
  | .u0 => 0
  | .u1 => 1
  | .uω => 2

instance : FiniteHeight U where
  height := U.height
  heightBound := 2
  height_le x := by cases x <;> decide
  height_lt x y := by cases x <;> cases y <;> decide

/-- The ascent engine stabilizes at a pre-fixpoint. -/
theorem kleeneFix_go_prefix {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] (f : a → a) (x : a) :
    (f (kleeneFix.go f x) ⊑ kleeneFix.go f x) = true := by
  fun_induction kleeneFix.go f x with
  | case1 x h =>
    exact le_iff_le.mp (Std.IsPreorder.le_trans _ _ _
      (le_iff_le.mpr (Std.right_le_max (a := x) (b := f x))) (le_iff_le.mpr h))
  | case2 x h ih => exact ih

/-- `kleeneFix` returns a pre-fixpoint. -/
theorem kleeneFix_prefix {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] (f : a → a) :
    (f (kleeneFix f) ⊑ kleeneFix f) = true :=
  kleeneFix_go_prefix f bottom

/-- Predicate induction for the ascent engine: a predicate of the seed that is
    closed under joins and under `f` holds at the stabilization point. -/
theorem kleeneFix_go_pred {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] {P : a → Prop} (f : a → a)
    (hjoin : ∀ x y, P x → P y → P (x ⊔ y)) (hf : ∀ x, P x → P (f x)) (x : a) :
    P x → P (kleeneFix.go f x) := by
  fun_induction kleeneFix.go f x with
  | case1 x h => exact id
  | case2 x h ih => exact fun hx => ih (hjoin x (f x) hx (hf x hx))

/-- Predicate induction for `kleeneFix`: a predicate of `bottom` that is
    closed under joins and under `f` holds of the Kleene ascent. -/
theorem kleeneFix_pred {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] {P : a → Prop} (f : a → a)
    (hbot : P bottom) (hjoin : ∀ x y, P x → P y → P (x ⊔ y))
    (hf : ∀ x, P x → P (f x)) : P (kleeneFix f) :=
  kleeneFix_go_pred f hjoin hf bottom hbot

/-- Relational induction for the ascent engine against a stabilized right
    side: a relation closed under the paired step and joins, and monotone in
    its right argument, survives the left ascent. -/
theorem kleeneFix_go_rel_left {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] {R : a → a → Prop} (f₁ f₂ : a → a)
    (hf : ∀ d₁ d₂, R d₁ d₂ → R (f₁ d₁) (f₂ d₂))
    (hjoin : ∀ a₁ b₁ a₂ b₂, R a₁ a₂ → R b₁ b₂ → R (a₁ ⊔ b₁) (a₂ ⊔ b₂))
    (hup : ∀ d₁ d₂ d₂', R d₁ d₂ → d₂ ⊑ d₂' → R d₁ d₂')
    (y : a) (hy : (y ⊔ f₂ y) ⊑ y) (x : a) :
    R x y → R (kleeneFix.go f₁ x) y := by
  fun_induction kleeneFix.go f₁ x with
  | case1 x h => exact id
  | case2 x h ih =>
    exact fun hxy => ih (hup _ _ _ (hjoin _ _ _ _ hxy (hf _ _ hxy)) hy)

/-- Relational induction for two paired ascents: a relation closed under the
    paired step and joins, and monotone in its right argument, relates the two
    stabilization points. The two sides may stabilize at different iteration
    counts; right-monotonicity bridges the mismatch. -/
theorem kleeneFix_go_rel {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] {R : a → a → Prop} (f₁ f₂ : a → a)
    (hf : ∀ d₁ d₂, R d₁ d₂ → R (f₁ d₁) (f₂ d₂))
    (hjoin : ∀ a₁ b₁ a₂ b₂, R a₁ a₂ → R b₁ b₂ → R (a₁ ⊔ b₁) (a₂ ⊔ b₂))
    (hup : ∀ d₁ d₂ d₂', R d₁ d₂ → d₂ ⊑ d₂' → R d₁ d₂')
    (y : a) : ∀ x, R x y → R (kleeneFix.go f₁ x) (kleeneFix.go f₂ y) := by
  fun_induction kleeneFix.go f₂ y with
  | case1 y h => exact kleeneFix_go_rel_left f₁ f₂ hf hjoin hup y h
  | case2 y h ih =>
    exact fun x hxy => ih x (hup _ _ _ hxy
      (le_iff_le.mp (Std.left_le_max (a := y) (b := f₂ y))))

/-- Relational induction for `kleeneFix`. -/
theorem kleeneFix_rel {a : Type} [Lat a] [Std.IsPreorder a]
    [Std.LawfulOrderSup a] [FiniteHeight a] {R : a → a → Prop} (f₁ f₂ : a → a)
    (hbot : R bottom bottom)
    (hf : ∀ d₁ d₂, R d₁ d₂ → R (f₁ d₁) (f₂ d₂))
    (hjoin : ∀ a₁ b₁ a₂ b₂, R a₁ a₂ → R b₁ b₂ → R (a₁ ⊔ b₁) (a₂ ⊔ b₂))
    (hup : ∀ d₁ d₂ d₂', R d₁ d₂ → d₂ ⊑ d₂' → R d₁ d₂') :
    R (kleeneFix f₁) (kleeneFix f₂) :=
  kleeneFix_go_rel f₁ f₂ hf hjoin hup bottom bottom hbot

/-! ## Pointwise view of summaries -/

/-- The usage a summary assigns to argument position `i`, unrolling `rep`. -/
def UValue.At : UValue → Nat → U
  | .rep u,    _    => u
  | .cons u _, 0    => u
  | .cons _ v, i+1  => v.At i

@[simp] theorem UValue.At_rep (u : U) (i : Nat) : (UValue.rep u).At i = u := rfl
@[simp] theorem UValue.At_cons_zero (u : U) (v : UValue) : (UValue.cons u v).At 0 = u := rfl
@[simp] theorem UValue.At_cons_succ (u : U) (v : UValue) (i : Nat) :
    (UValue.cons u v).At (i + 1) = v.At i := rfl

/-- Joining acts pointwise. -/
theorem UValue.At_join (a b : UValue) (i : Nat) :
    (UValue.join a b).At i = a.At i ⊔ b.At i := by
  induction i generalizing a b with
  | zero => cases a <;> cases b <;> simp [UValue.join, UValue.At]
  | succ i ih => cases a <;> cases b <;> simp [UValue.join, UValue.At, ih]

/-- Equality of summaries is pointwise stream equality. -/
theorem UValue.beq_iff_At (a b : UValue) :
    UValue.beq a b = true ↔ ∀ i, a.At i = b.At i := by
  fun_induction UValue.beq a b with
  | case1 x y =>
    simp only [U.beq_iff_eq, UValue.At_rep]
    exact ⟨fun h _ => h, fun h => h 0⟩
  | case2 x v y w ih =>
    simp only [Bool.and_eq_true, U.beq_iff_eq, ih]
    refine ⟨fun ⟨hxy, h⟩ i => ?_, fun h => ⟨h 0, fun i => h (i + 1)⟩⟩
    subst hxy; cases i with | zero => rfl | succ n => exact h n
  | case3 x v y ih =>
    simp only [Bool.and_eq_true, U.beq_iff_eq, ih]
    refine ⟨fun ⟨hxy, h⟩ i => ?_, fun h => ⟨h 0, fun i => h (i + 1)⟩⟩
    subst hxy; cases i with | zero => rfl | succ n => exact h n
  | case4 x y w ih =>
    simp only [Bool.and_eq_true, U.beq_iff_eq, ih]
    refine ⟨fun ⟨hxy, h⟩ i => ?_, fun h => ⟨h 0, fun i => h (i + 1)⟩⟩
    subst hxy; cases i with | zero => rfl | succ n => exact h n

/-- Approximation of summaries is pointwise approximation of usages. -/
theorem UValue.le_iff_At (a b : UValue) :
    (a ⊑ b) = true ↔ ∀ i, (a.At i ⊑ b.At i) = true := by
  show UValue.beq (UValue.join a b) b = true ↔ _
  rw [beq_iff_At]
  constructor
  · intro h i; rw [U.le_iff_join, ← At_join]; exact h i
  · intro h i; rw [At_join, ← U.le_iff_join]; exact h i

/-! ## The bounded subtype is a preorder -/

instance instPreorderUValuek (k : Nat) : @Std.IsPreorder (UValuek k) instLELat where
  le_refl a := by
    show (a.val ⊑ a.val) = true
    rw [UValue.le_iff_At]; exact fun i => U.le_refl _
  le_trans a b c hab hbc := by
    have hab' : (a.val ⊑ b.val) = true := hab
    have hbc' : (b.val ⊑ c.val) = true := hbc
    show (a.val ⊑ c.val) = true
    rw [UValue.le_iff_At] at hab' hbc' ⊢
    exact fun i => U.le_trans (hab' i) (hbc' i)

/-! ## Bounded chain completeness

Every family has a least upper bound: take the pointwise `U`-supremum, which is
constant past position `k` because each member is, and reassemble it into a
summary of length `≤ k`. -/

open Classical in
/-- The supremum of a family of usages. `U` is finite, so the join of the image
    exists; classical and never computed. -/
noncomputable def Usup (f : Nat → U) : U :=
  if ∃ n, f n = .uω then .uω else if ∃ n, f n = .u1 then .u1 else .u0

theorem U.le_Usup (f : Nat → U) (n : Nat) : (f n ⊑ Usup f) = true := by
  unfold Usup
  split
  · cases f n <;> rfl
  · rename_i h1
    split
    · cases hfn : f n with
      | u0 => rfl
      | u1 => rfl
      | uω => exact absurd ⟨n, hfn⟩ h1
    · rename_i h2
      cases hfn : f n with
      | u0 => rfl
      | u1 => exact absurd ⟨n, hfn⟩ h2
      | uω => exact absurd ⟨n, hfn⟩ h1

theorem U.Usup_le {f : Nat → U} {b : U} (h : ∀ n, (f n ⊑ b) = true) :
    (Usup f ⊑ b) = true := by
  unfold Usup
  split
  · rename_i h1; obtain ⟨n, hn⟩ := h1; rw [← hn]; exact h n
  · split
    · rename_i _ h2; obtain ⟨n, hn⟩ := h2; rw [← hn]; exact h n
    · cases b <;> rfl

/-- Assemble a summary of length `≤ k` reading `L` at each of the first `k`
    positions and repeating `L k` thereafter. -/
def buildU : Nat → (Nat → U) → UValue
  | 0,     L => .rep (L 0)
  | k + 1, L => .cons (L 0) (buildU k (fun i => L (i + 1)))

theorem buildU_length (k : Nat) (L : Nat → U) : (buildU k L).length ≤ k := by
  induction k generalizing L with
  | zero => exact Nat.le_refl 0
  | succ k ih => simp only [buildU, UValue.length]; exact Nat.succ_le_succ (ih _)

theorem buildU_At (k : Nat) (L : Nat → U) (i : Nat) :
    (buildU k L).At i = L (min i k) := by
  induction k generalizing L i with
  | zero => simp only [buildU, UValue.At_rep, Nat.min_zero]
  | succ k ih =>
    cases i with
    | zero => simp only [buildU, UValue.At_cons_zero, Nat.zero_min]
    | succ i => simp only [buildU, UValue.At_cons_succ, ih]; congr 1; omega

/-- Past its length a summary is constant. -/
theorem UValue.At_const_ge (v : UValue) {i j : Nat}
    (hi : v.length ≤ i) (hj : v.length ≤ j) : v.At i = v.At j := by
  induction v generalizing i j with
  | rep u => rfl
  | cons u w ih =>
    cases i with
    | zero => simp only [UValue.length] at hi; omega
    | succ i => cases j with
      | zero => simp only [UValue.length] at hj; omega
      | succ j =>
        simp only [UValue.At_cons_succ]
        simp only [UValue.length] at hi hj
        exact ih (by omega) (by omega)

instance instChainCompleteUValuek (k : Nat) : ChainComplete (UValuek k) where
  has_csup c _d _hd := by
    have key : ∀ i, (buildU k (fun j => Usup (fun n => (c n).val.At j))).At i
        = Usup (fun n => (c n).val.At i) := by
      intro i
      simp only [buildU_At]
      by_cases hik : i ≤ k
      · have : min i k = i := by omega
        rw [this]
      · have : min i k = k := by omega
        rw [this]
        congr 1; funext n
        exact UValue.At_const_ge (c n).val (c n).property
          (Nat.le_trans (c n).property (by omega))
    refine ⟨⟨buildU k (fun j => Usup (fun n => (c n).val.At j)), buildU_length k _⟩, ?_, ?_⟩
    · intro n
      rw [le_iff_le]
      show ((c n).val ⊑ buildU k (fun j => Usup (fun n => (c n).val.At j))) = true
      rw [UValue.le_iff_At]
      intro i
      rw [key i]
      exact U.le_Usup (fun m => (c m).val.At i) n
    · intro y hy
      rw [le_iff_le]
      show (buildU k (fun j => Usup (fun n => (c n).val.At j)) ⊑ y.val) = true
      rw [UValue.le_iff_At]
      intro i
      rw [key i]
      apply U.Usup_le
      intro n
      have hn : ((c n).val ⊑ y.val) = true := by rw [← le_iff_le]; exact hy n
      rw [UValue.le_iff_At] at hn
      exact hn i

/-! ## Widening and the bounded domain

Bounding a summary to length `k` joins everything past position `k` into the
repeating tail, an over-approximation that caps the length. The bounded domain
`UDk k` reuses every `UD` operation, widening the summary of each result; since
the summaries then live in the finite `UValuek k`, the recursive `bind` settles
and the analysis is total. -/

/-- The join of every usage a summary assigns. -/
def UValue.tailSup : UValue → U
  | .rep u => u
  | .cons u v => u ⊔ v.tailSup

/-- Bound a summary to length `k`, joining the dropped tail into position `k`. -/
def UValue.widen : Nat → UValue → UValue
  | 0,     v         => .rep v.tailSup
  | _ + 1, .rep u    => .rep u
  | k + 1, .cons u v => .cons u (v.widen k)

theorem UValue.widen_length (k : Nat) (v : UValue) : (v.widen k).length ≤ k := by
  induction k generalizing v with
  | zero => simp [UValue.widen, UValue.length]
  | succ k ih => cases v with
    | rep u => simp [UValue.widen, UValue.length]
    | cons u v => simp only [UValue.widen, UValue.length]; exact Nat.succ_le_succ (ih v)

/-- The bounded usage domain: usage traces over length-`k` summaries. -/
abbrev UDk (k : Nat) : Type := UT (UValuek k)

/-- Forget the length bound. -/
def UDk.embed {k : Nat} (d : UDk k) : UD := ⟨d.uses, d.val.val⟩

/-- Widen a usage trace back into the bounded domain. -/
def UDk.wrap {k : Nat} (d : UD) : UDk k :=
  ⟨d.uses, ⟨UValue.widen k d.val, UValue.widen_length k d.val⟩⟩

instance (k : Nat) : Lat (UDk k) where
  bottom := ⟨bottom, bottom⟩
  join a b := ⟨a.uses ⊔ b.uses, a.val ⊔ b.val⟩

/-! ## The usage environment order

`Uses` compares up to `u0`-thinning, so its `BEq` equality and order are
pointwise on the `!?` reading (`le_iff_get`), a preorder with least upper bounds
of bounded families. The lub is the key-wise `U`-supremum over the bound's keys;
off those keys every member reads `u0`, so the omitted keys read `u0` too. -/

/-- `u0` is a left identity of `U.join`. -/
@[simp] theorem U.zero_join (u : U) : U.u0 ⊔ u = u := rfl
/-- `u0` is a right identity of `U.join`. -/
@[simp] theorem U.join_zero (u : U) : u ⊔ U.u0 = u := by cases u <;> rfl
/-- Only `u0` approximates `u0`. -/
theorem U.eq_zero_of_le_zero {u : U} (h : (u ⊑ U.u0) = true) : u = U.u0 := by
  cases u <;> first | rfl | exact absurd h (by decide)

/-- Reading a key is the `getD` of its `getElem?`. -/
theorem Uses.get_eq (φ : Uses) (x : Var) : φ !? x = (φ[x]?).getD U.u0 := by
  show φ.toMap.getD x U.u0 = _; rw [Std.HashMap.getD_eq_getD_getElem?]; rfl

/-- Joining acts pointwise. -/
theorem Uses.get_join (φ₁ φ₂ : Uses) (x : Var) :
    (Uses.merge U.join φ₁ φ₂) !? x = φ₁ !? x ⊔ φ₂ !? x := by
  rw [Uses.get_eq, Uses.get_eq, Uses.get_eq, Uses.getElem?_merge]
  cases φ₂[x]? <;> cases φ₁[x]? <;> first | rfl | simp [mstep]

/-- Approximation of usage environments is pointwise. -/
theorem Uses.le_iff_get (a b : Uses) :
    (a ⊑ b) = true ↔ ∀ x, (a !? x ⊑ b !? x) = true := by
  show (Uses.merge U.join a b == b) = true ↔ _
  rw [Uses.beq_iff_get]
  constructor
  · intro h x; rw [U.le_iff_join, ← Uses.get_join]; exact h x
  · intro h x; rw [Uses.get_join, ← U.le_iff_join]; exact h x

instance instPreorderUses : @Std.IsPreorder Uses instLELat where
  le_refl a := by show (a ⊑ a) = true; rw [Uses.le_iff_get]; exact fun x => U.le_refl _
  le_trans a b c hab hbc := by
    have hab' : (a ⊑ b) = true := hab
    have hbc' : (b ⊑ c) = true := hbc
    show (a ⊑ c) = true
    rw [Uses.le_iff_get] at hab' hbc' ⊢
    exact fun x => U.le_trans (hab' x) (hbc' x)

instance instChainCompleteUses : ChainComplete Uses where
  has_csup c d _hd := by
    have hd' : ∀ n x, (c n !? x ⊑ d !? x) = true := fun n => by
      have := _hd n; rw [le_iff_le, Uses.le_iff_get] at this; exact this
    have key : ∀ x, (⟨d.toMap.map (fun k _ => Usup (fun n => c n !? k))⟩ : Uses) !? x
        = Usup (fun n => c n !? x) := by
      intro x
      show (d.toMap.map (fun k _ => Usup (fun n => c n !? k))).getD x U.u0 = _
      rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_map]
      cases hx : d.toMap[x]? with
      | some v => simp
      | none =>
        simp only [Option.map_none, Option.getD_none]
        have hz : ∀ n, (c n !? x ⊑ U.u0) = true := by
          intro n
          have hdx : d !? x = U.u0 := by rw [Uses.get_eq, Uses.getElem?_toMap, hx]; rfl
          have := hd' n x; rw [hdx] at this; exact this
        exact (U.eq_zero_of_le_zero (U.Usup_le hz)).symm
    refine ⟨⟨d.toMap.map (fun k _ => Usup (fun n => c n !? k))⟩, ?_, ?_⟩
    · intro n
      rw [le_iff_le, Uses.le_iff_get]
      intro x; rw [key x]; exact U.le_Usup (fun m => c m !? x) n
    · intro y hy
      rw [le_iff_le, Uses.le_iff_get]
      intro x; rw [key x]
      apply U.Usup_le
      intro n
      have := hy n; rw [le_iff_le, Uses.le_iff_get] at this; exact this x

/-! ## The bounded domain is a bounded-complete preorder

`UDk k` is the product of the usage environment and the length-`k` summary, both
preorders with least upper bounds of bounded families; the product order is
componentwise, so it inherits both. -/

/-- The order on `UDk k` is componentwise. -/
theorem UDk.le_iff {k : Nat} (a b : UDk k) :
    (a ⊑ b) = true ↔ (a.uses ⊑ b.uses) = true ∧ (a.val ⊑ b.val) = true := by
  show ((a.uses ⊔ b.uses == b.uses) && (a.val ⊔ b.val == b.val)) = true ↔ _
  rw [Bool.and_eq_true]; rfl

instance instPreorderUDk (k : Nat) : @Std.IsPreorder (UDk k) instLELat where
  le_refl a := by
    show (a ⊑ a) = true; rw [UDk.le_iff]
    exact ⟨le_iff_le.mp (Std.IsPreorder.le_refl a.uses),
           le_iff_le.mp (Std.IsPreorder.le_refl a.val)⟩
  le_trans a b c hab hbc := by
    have hab' : (a ⊑ b) = true := hab
    have hbc' : (b ⊑ c) = true := hbc
    rw [UDk.le_iff] at hab' hbc'
    show (a ⊑ c) = true; rw [UDk.le_iff]
    exact ⟨le_iff_le.mp (Std.IsPreorder.le_trans _ _ _ (le_iff_le.mpr hab'.1) (le_iff_le.mpr hbc'.1)),
           le_iff_le.mp (Std.IsPreorder.le_trans _ _ _ (le_iff_le.mpr hab'.2) (le_iff_le.mpr hbc'.2))⟩

instance instChainCompleteUDk (k : Nat) : ChainComplete (UDk k) where
  has_csup c d hd := by
    have hd' : ∀ n, (c n ⊑ d) = true := fun n => hd n
    have hu : ∀ n, (c n).uses ≤ d.uses := fun n => le_iff_le.mpr ((UDk.le_iff _ _).mp (hd' n)).1
    have hv : ∀ n, (c n).val ≤ d.val := fun n => le_iff_le.mpr ((UDk.le_iff _ _).mp (hd' n)).2
    obtain ⟨xu, hxu⟩ := ChainComplete.has_csup (fun n => (c n).uses) d.uses hu
    obtain ⟨xv, hxv⟩ := ChainComplete.has_csup (fun n => (c n).val) d.val hv
    refine ⟨⟨xu, xv⟩, ?_, ?_⟩
    · intro n
      show (c n ⊑ (⟨xu, xv⟩ : UDk k)) = true; rw [UDk.le_iff]
      exact ⟨le_iff_le.mp (hxu.1 n), le_iff_le.mp (hxv.1 n)⟩
    · intro y hy
      show ((⟨xu, xv⟩ : UDk k) ⊑ y) = true; rw [UDk.le_iff]
      refine ⟨le_iff_le.mp (hxu.2 y.uses fun n => ?_), le_iff_le.mp (hxv.2 y.val fun n => ?_)⟩
      · exact le_iff_le.mpr ((UDk.le_iff _ _).mp (hy n)).1
      · exact le_iff_le.mpr ((UDk.le_iff _ _).mp (hy n)).2

/-! ## Least upper bounds

The joins of `Uses`, `UValuek`, and `UDk` are least upper bounds, pointwise
(respectively componentwise) from `U`'s. -/

/-- `U`'s join is its least upper bound. -/
theorem U.join_le_iff {u w b : U} :
    ((u ⊔ w) ⊑ b) = true ↔ (u ⊑ b) = true ∧ (w ⊑ b) = true := by
  cases u <;> cases w <;> cases b <;> decide

instance : Std.LawfulOrderSup Uses where
  max_le_iff a b c := by
    show ((Uses.merge U.join a b) ⊑ c) = true ↔ (a ⊑ c) = true ∧ (b ⊑ c) = true
    simp only [Uses.le_iff_get, Uses.get_join, U.join_le_iff, forall_and]

instance (k : Nat) : Std.LawfulOrderSup (UValuek k) where
  max_le_iff a b c := by
    show ((a.val ⊔ b.val) ⊑ c.val) = true ↔ (a.val ⊑ c.val) = true ∧ (b.val ⊑ c.val) = true
    rw [show a.val ⊔ b.val = UValue.join a.val b.val from rfl]
    simp only [UValue.le_iff_At, UValue.At_join, U.join_le_iff, forall_and]

instance (k : Nat) : Std.LawfulOrderSup (UDk k) where
  max_le_iff a b c := by
    have hu := Std.LawfulOrderSup.max_le_iff a.uses b.uses c.uses
    have hv := Std.LawfulOrderSup.max_le_iff a.val b.val c.val
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := (UDk.le_iff (a ⊔ b) c).mp h
      obtain ⟨hu1, hu2⟩ := hu.mp h1
      obtain ⟨hv1, hv2⟩ := hv.mp h2
      exact ⟨(UDk.le_iff a c).mpr ⟨hu1, hv1⟩, (UDk.le_iff b c).mpr ⟨hu2, hv2⟩⟩
    · rintro ⟨ha, hb⟩
      obtain ⟨hu1, hv1⟩ := (UDk.le_iff a c).mp ha
      obtain ⟨hu2, hv2⟩ := (UDk.le_iff b c).mp hb
      exact (UDk.le_iff (a ⊔ b) c).mpr ⟨hu.mpr ⟨hu1, hu2⟩, hv.mpr ⟨hv1, hv2⟩⟩

/-! ## The name supply is finite

`Var` is a string of at most `Var.maxLength` characters, so a radix encoding
embeds it into an initial segment of `Nat`. A duplicate-free key list of a
usage environment therefore has at most `Var.card` entries, which caps the
environment's height. -/

/-- One more than the number of character codes: the radix of `encodeChars`. -/
def charBase : Nat := UInt32.size + 1

theorem charBase_pos : 0 < charBase := Nat.succ_pos _

theorem toNat_add_one_lt_charBase (c : Char) : c.toNat + 1 < charBase :=
  Nat.succ_lt_succ (UInt32.toNat_lt_size c.val)

/-- Radix encoding of a character list: digits `c.toNat + 1` in base
    `charBase`, so no digit is `0` and distinct lists get distinct codes. -/
def encodeChars : List Char → Nat
  | [] => 0
  | c :: cs => encodeChars cs * charBase + (c.toNat + 1)

theorem encodeChars_inj : ∀ {l₁ l₂ : List Char}, encodeChars l₁ = encodeChars l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [encodeChars] at h; omega
  | _ :: _, [], h => by simp only [encodeChars] at h; omega
  | c₁ :: cs₁, c₂ :: cs₂, h => by
    simp only [encodeChars] at h
    have hd₁ := toNat_add_one_lt_charBase c₁
    have hd₂ := toNat_add_one_lt_charBase c₂
    have hmod : c₁.toNat + 1 = c₂.toNat + 1 := by
      calc c₁.toNat + 1
          = (encodeChars cs₁ * charBase + (c₁.toNat + 1)) % charBase := by
            rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hd₁]
        _ = (encodeChars cs₂ * charBase + (c₂.toNat + 1)) % charBase := by rw [h]
        _ = c₂.toNat + 1 := by rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hd₂]
    have hdiv : encodeChars cs₁ = encodeChars cs₂ := by
      calc encodeChars cs₁
          = (encodeChars cs₁ * charBase + (c₁.toNat + 1)) / charBase := by
            rw [Nat.mul_comm, Nat.mul_add_div charBase_pos, Nat.div_eq_of_lt hd₁,
              Nat.add_zero]
        _ = (encodeChars cs₂ * charBase + (c₂.toNat + 1)) / charBase := by rw [h]
        _ = encodeChars cs₂ := by
            rw [Nat.mul_comm, Nat.mul_add_div charBase_pos, Nat.div_eq_of_lt hd₂,
              Nat.add_zero]
    rw [Char.toNat_inj.mp (by omega : c₁.toNat = c₂.toNat), encodeChars_inj hdiv]

theorem encodeChars_lt_pow {l : List Char} : ∀ {n : Nat}, l.length ≤ n →
    encodeChars l < charBase ^ n := by
  induction l with
  | nil =>
    intro n _
    simp only [encodeChars]
    exact Nat.pow_pos charBase_pos
  | cons c cs ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by simp)
    | succ n =>
      have hcs : encodeChars cs < charBase ^ n :=
        ih (Nat.le_of_succ_le_succ (by simpa using h))
      have hd := toNat_add_one_lt_charBase c
      have h2 : (encodeChars cs + 1) * charBase ≤ charBase ^ n * charBase :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hcs)
      have h3 : encodeChars cs * charBase + charBase = (encodeChars cs + 1) * charBase :=
        (Nat.succ_mul _ _).symm
      simp only [encodeChars]
      rw [Nat.pow_succ]
      omega

/-- The number of variable names. -/
def Var.card : Nat := charBase ^ Var.maxLength

/-- The radix code of a name. -/
def Var.encode (x : Var) : Nat := encodeChars x.val.toList

theorem Var.encode_inj {x y : Var} (h : x.encode = y.encode) : x = y :=
  Subtype.ext (String.toList_injective (encodeChars_inj h))

theorem Var.encode_lt (x : Var) : x.encode < Var.card :=
  encodeChars_lt_pow (by rw [String.length_toList]; exact x.property)

/-- A duplicate-free list of naturals below `n` has at most `n` elements. -/
theorem length_le_of_nodup_lt (n : Nat) : ∀ l : List Nat, l.Nodup →
    (∀ x ∈ l, x < n) → l.length ≤ n := by
  induction n with
  | zero =>
    intro l _ hb
    cases l with
    | nil => exact Nat.le_refl 0
    | cons a l => exact absurd (hb a (List.mem_cons_self ..)) (Nat.not_lt_zero a)
  | succ n ih =>
    intro l hnd hb
    by_cases hn : n ∈ l
    · have hlen : (l.erase n).length = l.length - 1 := List.length_erase_of_mem hn
      have hpos : 0 < l.length := List.length_pos_of_mem hn
      have hle : (l.erase n).length ≤ n := by
        refine ih (l.erase n) (hnd.sublist List.erase_sublist) fun x hx => ?_
        obtain ⟨hne, hmem⟩ := hnd.mem_erase_iff.mp hx
        have := hb x hmem
        omega
      omega
    · refine Nat.le_trans (ih l hnd fun x hx => ?_) (Nat.le_succ n)
      have := hb x hx
      have hne : x ≠ n := fun h => hn (h ▸ hx)
      omega

/-! ## Sums of pointwise readings

The height of a usage environment or a bounded summary is a sum of `U.height`
readings over an index list. These are the sum manipulations the height
lemmas need: reindexing along a permutation, dropping `0` summands, and
pointwise (strict) monotonicity. -/

theorem perm_sum_eq {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.sum_cons, ih]
  | swap a b l => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Duplicate-free lists with the same members are permutations. -/
theorem perm_of_nodup_mem_iff {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁.Perm l₂
  | [], l₂, _, _, hm => by
    have : l₂ = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun x hx => absurd ((hm x).mpr hx) (List.not_mem_nil))
    exact this ▸ List.Perm.refl []
  | a :: l₁, l₂, hnd₁, hnd₂, hm => by
    obtain ⟨ha₁, hnd₁'⟩ := List.nodup_cons.mp hnd₁
    have ha₂ : a ∈ l₂ := (hm a).mp (List.mem_cons_self ..)
    have hm' : ∀ x, x ∈ l₁ ↔ x ∈ l₂.erase a := by
      intro x
      rw [hnd₂.mem_erase_iff]
      constructor
      · intro hx
        exact ⟨fun hxa => ha₁ (hxa ▸ hx), (hm x).mp (List.mem_cons_of_mem a hx)⟩
      · rintro ⟨hxa, hx₂⟩
        rcases List.mem_cons.mp ((hm x).mpr hx₂) with rfl | h
        · exact absurd rfl hxa
        · exact h
    exact ((perm_of_nodup_mem_iff hnd₁' (hnd₂.sublist List.erase_sublist) hm').cons a).trans
      (List.perm_cons_erase ha₂).symm

/-- Summands reading `0` drop out of a pointwise sum. -/
theorem sum_map_filter_eq {α : Type} {f : α → Nat} {p : α → Bool}
    (hp : ∀ x, p x = false → f x = 0) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map f).sum
  | [] => rfl
  | a :: l => by
    cases hpa : p a with
    | true => simp [List.filter_cons, hpa, sum_map_filter_eq hp l]
    | false => simp [List.filter_cons, hpa, sum_map_filter_eq hp l, hp a hpa]

theorem sum_map_le_sum_map {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem a hx))

theorem sum_map_lt_sum_map {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) {x₀ : α} (hx₀ : x₀ ∈ l) (hlt : f x₀ < g x₀) :
    (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => cases hx₀
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have htail : ∀ x ∈ l, f x ≤ g x := fun x hx => h x (List.mem_cons_of_mem a hx)
    rcases List.mem_cons.mp hx₀ with rfl | hmem
    · exact Nat.add_lt_add_of_lt_of_le hlt (sum_map_le_sum_map htail)
    · exact Nat.add_lt_add_of_le_of_lt (h a (List.mem_cons_self ..)) (ih htail hmem)

theorem sum_map_le_two_mul {α : Type} {l : List α} {f : α → Nat}
    (h : ∀ x ∈ l, f x ≤ 2) : (l.map f).sum ≤ 2 * l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    omega

/-! ## `Uses` has finite height -/

/-- `U.height` is monotone. -/
theorem U.height_mono {u w : U} (h : (u ⊑ w) = true) : U.height u ≤ U.height w := by
  cases u <;> cases w <;> revert h <;> decide

/-- `U.height` is strictly monotone. -/
theorem U.height_lt_of_lt {u w : U} (h : (u ⊑ w) = true) (h' : (w ⊑ u) = false) :
    U.height u < U.height w := by
  cases u <;> cases w <;> revert h h' <;> decide

/-- A variable reading non-`u0` is a key of the underlying map. -/
theorem Uses.mem_keys_of_get_ne {φ : Uses} {x : Var} (h : φ !? x ≠ .u0) :
    x ∈ φ.toMap.keys := by
  refine Classical.byContradiction fun hx => h ?_
  have hmem : ¬ x ∈ φ.toMap := fun hm => hx (Std.HashMap.mem_keys.mpr hm)
  rw [Uses.get_eq, Uses.getElem?_toMap, Std.HashMap.getElem?_eq_none hmem]
  rfl

/-- The height of a usage environment: the total height of its readings. -/
def Uses.height (φ : Uses) : Nat :=
  (φ.toMap.keys.map (fun x => U.height (φ !? x))).sum

/-- The height read over any duplicate-free list covering the support. -/
theorem Uses.height_eq_read (φ : Uses) {l : List Var} (hl : l.Nodup)
    (hs : ∀ x, φ !? x ≠ .u0 → x ∈ l) :
    φ.height = (l.map (fun x => U.height (φ !? x))).sum := by
  have hzero : ∀ x, (φ !? x != U.u0) = false → U.height (φ !? x) = 0 := by
    intro x hx
    have : φ !? x = U.u0 := by simpa using hx
    rw [this]; rfl
  show (φ.toMap.keys.map (fun x => U.height (φ !? x))).sum = _
  rw [← sum_map_filter_eq hzero φ.toMap.keys, ← sum_map_filter_eq hzero l]
  refine perm_sum_eq (List.Perm.map _ (perm_of_nodup_mem_iff
    (Std.HashMap.nodup_keys.filter _) (hl.filter _) fun x => ?_))
  simp only [List.mem_filter, bne_iff_ne, ne_eq]
  exact ⟨fun ⟨_, hne⟩ => ⟨hs x hne, hne⟩, fun ⟨_, hne⟩ => ⟨Uses.mem_keys_of_get_ne hne, hne⟩⟩

theorem Uses.height_le (φ : Uses) : φ.height ≤ 2 * Var.card := by
  refine Nat.le_trans (sum_map_le_two_mul fun x _ => ?_) ?_
  · cases φ !? x <;> decide
  · have hnodup : (φ.toMap.keys.map Var.encode).Nodup :=
      List.Pairwise.map Var.encode (fun a b hab he => hab (Var.encode_inj he))
        Std.HashMap.nodup_keys
    have hbound : ∀ y ∈ φ.toMap.keys.map Var.encode, y < Var.card := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact Var.encode_lt x
    have := length_le_of_nodup_lt Var.card _ hnodup hbound
    rw [List.length_map] at this
    omega

theorem Uses.height_mono {φ ψ : Uses} (h : (φ ⊑ ψ) = true) : φ.height ≤ ψ.height := by
  have hpt := (Uses.le_iff_get φ ψ).mp h
  have hsup : ∀ x, φ !? x ≠ .u0 → x ∈ ψ.toMap.keys := by
    intro x hx
    refine Uses.mem_keys_of_get_ne fun hzero => hx ?_
    have := hpt x
    rw [hzero] at this
    exact U.eq_zero_of_le_zero this
  rw [φ.height_eq_read Std.HashMap.nodup_keys hsup,
      ψ.height_eq_read Std.HashMap.nodup_keys (fun x hx => Uses.mem_keys_of_get_ne hx)]
  exact sum_map_le_sum_map fun x _ => U.height_mono (hpt x)

theorem Uses.height_lt {φ ψ : Uses} (h : (φ ⊑ ψ) = true) (h' : (ψ ⊑ φ) = false) :
    φ.height < ψ.height := by
  have hpt := (Uses.le_iff_get φ ψ).mp h
  have hex : ∃ x, (ψ !? x ⊑ φ !? x) = false := by
    refine Classical.byContradiction fun hall => ?_
    have hall' : ∀ x, (ψ !? x ⊑ φ !? x) = true := by
      intro x
      cases hx : (ψ !? x ⊑ φ !? x) with
      | true => rfl
      | false => exact absurd ⟨x, hx⟩ hall
    rw [(Uses.le_iff_get ψ φ).mpr hall'] at h'
    exact Bool.noConfusion h'
  obtain ⟨x₀, hx₀⟩ := hex
  have hx₀ne : ψ !? x₀ ≠ .u0 := by
    intro hz
    rw [hz] at hx₀
    cases hφ : φ !? x₀ <;> rw [hφ] at hx₀ <;> exact absurd hx₀ (by decide)
  have hsup : ∀ x, φ !? x ≠ .u0 → x ∈ ψ.toMap.keys := by
    intro x hx
    refine Uses.mem_keys_of_get_ne fun hzero => hx ?_
    have := hpt x
    rw [hzero] at this
    exact U.eq_zero_of_le_zero this
  rw [φ.height_eq_read Std.HashMap.nodup_keys hsup,
      ψ.height_eq_read Std.HashMap.nodup_keys (fun x hx => Uses.mem_keys_of_get_ne hx)]
  exact sum_map_lt_sum_map (fun x _ => U.height_mono (hpt x))
    (Uses.mem_keys_of_get_ne hx₀ne) (U.height_lt_of_lt (hpt x₀) hx₀)

instance : FiniteHeight Uses where
  height := Uses.height
  heightBound := 2 * Var.card
  height_le := Uses.height_le
  height_lt _ _ := Uses.height_lt

/-! ## Bounded summaries have finite height -/

/-- The height of a bounded summary: the total height of its first `k + 1`
    positions, which determine it. -/
def UValuek.height {k : Nat} (v : UValuek k) : Nat :=
  ((List.range (k + 1)).map (fun i => U.height (v.val.At i))).sum

theorem UValuek.height_le {k : Nat} (v : UValuek k) : v.height ≤ 2 * (k + 1) := by
  refine Nat.le_trans (sum_map_le_two_mul fun i _ => ?_) ?_
  · cases v.val.At i <;> decide
  · rw [List.length_range]
    exact Nat.le_refl _

theorem UValuek.height_mono {k : Nat} {a b : UValuek k} (h : (a ⊑ b) = true) :
    a.height ≤ b.height := by
  have h' : (a.val ⊑ b.val) = true := h
  exact sum_map_le_sum_map fun i _ => U.height_mono ((UValue.le_iff_At _ _).mp h' i)

theorem UValuek.height_lt {k : Nat} {a b : UValuek k} (h : (a ⊑ b) = true)
    (h' : (b ⊑ a) = false) : a.height < b.height := by
  have hab : (a.val ⊑ b.val) = true := h
  have hba : (b.val ⊑ a.val) = false := h'
  have hpt := (UValue.le_iff_At _ _).mp hab
  have hex : ∃ i, (b.val.At i ⊑ a.val.At i) = false := by
    refine Classical.byContradiction fun hall => ?_
    have hall' : ∀ i, (b.val.At i ⊑ a.val.At i) = true := by
      intro i
      cases hi : (b.val.At i ⊑ a.val.At i) with
      | true => rfl
      | false => exact absurd ⟨i, hi⟩ hall
    rw [(UValue.le_iff_At b.val a.val).mpr hall'] at hba
    exact Bool.noConfusion hba
  obtain ⟨i₀, hi₀⟩ := hex
  have hi₀' : (b.val.At (min i₀ k) ⊑ a.val.At (min i₀ k)) = false := by
    by_cases hik : i₀ ≤ k
    · rwa [Nat.min_eq_left hik]
    · have hk : k ≤ i₀ := by omega
      rw [Nat.min_eq_right hk]
      rw [UValue.At_const_ge a.val a.property (Nat.le_trans a.property hk),
          UValue.At_const_ge b.val b.property (Nat.le_trans b.property hk)]
      exact hi₀
  refine sum_map_lt_sum_map (fun i _ => U.height_mono (hpt i))
    (List.mem_range.mpr (by omega : min i₀ k < k + 1))
    (U.height_lt_of_lt (hpt _) hi₀')

instance (k : Nat) : FiniteHeight (UValuek k) where
  height := UValuek.height
  heightBound := 2 * (k + 1)
  height_le := UValuek.height_le
  height_lt _ _ := UValuek.height_lt

/-! ## The bounded domain has finite height -/

instance instFiniteHeightUDk (k : Nat) : FiniteHeight (UDk k) where
  height d := d.uses.height + d.val.height
  heightBound := 2 * Var.card + 2 * (k + 1)
  height_le d := Nat.add_le_add d.uses.height_le d.val.height_le
  height_lt a b hab hba := by
    obtain ⟨hu, hv⟩ := (UDk.le_iff a b).mp hab
    have hor : ((b.uses ⊑ a.uses) = false) ∨ ((b.val ⊑ a.val) = false) := by
      cases hu' : (b.uses ⊑ a.uses) with
      | false => exact Or.inl rfl
      | true =>
        cases hv' : (b.val ⊑ a.val) with
        | false => exact Or.inr rfl
        | true =>
          rw [(UDk.le_iff b a).mpr ⟨hu', hv'⟩] at hba
          exact Bool.noConfusion hba
    rcases hor with h | h
    · exact Nat.add_lt_add_of_lt_of_le (Uses.height_lt hu h) (UValuek.height_mono hv)
    · exact Nat.add_lt_add_of_le_of_lt (Uses.height_mono hu) (UValuek.height_lt hv h)

/-! ## The bounded domain instance

Every operation reuses its `UD` counterpart, widening the summary of the
result. `bind` iterates the right-hand side to a pre-fixpoint by Kleene
ascent, total by the finite height, and runs the body on it. -/

instance (k : Nat) : AbstractDomain (UDk k) where
  step ev d := UDk.wrap (UD.step ev d.embed)
  stuck := UDk.wrap UD.stuck
  fn x f := UDk.wrap (UD.fn x (fun d => (f (UDk.wrap d)).embed))
  apply a b := UDk.wrap (UD.apply a.embed b.embed)
  con K ds := UDk.wrap (UD.con K (ds.map UDk.embed))
  select d alts := UDk.wrap (UD.select d.embed
    (alts.map (fun p => (p.1, p.2.1, fun ds => (p.2.2 (ds.map UDk.wrap)).embed))))
  bind rhs body := body (kleeneFix rhs)

/-- Usage analysis at the bounded domain: total, since summaries stay finite. -/
def evalUsgk (k : Nat) (e : Exp) (ρ : Env (UDk k)) : UDk k := eval (d := Discrete (UDk k)) e ρ

/-- `let r = λa. case a of C() → r in r`: recursion whose summary grows without
    bound at the unbounded domain. At the bounded domain the analysis settles. -/
def rDiv : Exp :=
  .«let» "r" (.lam "a" (.«case» (.ref "a") [⟨0, [], .ref "r"⟩])) (.ref "r")

/-- The initial environment for open examples: each free variable maps to a
    proxy recording a single use at an unknown value. -/
def ρe (k : Nat) : Env (UDk k) := fun x => some (UDk.wrap (UD.fn.proxy x))

#guard (evalUsgk 10 usgEx1 Env.empty).embed == (⟨⟨.ofList [("i", .uω)]⟩, .rep .uω⟩ : UD)
#guard (evalUsgk 10 usgEx2 Env.empty).embed
  == (⟨⟨.ofList [("i", .u1), ("j", .uω)]⟩, .rep .uω⟩ : UD)
#guard (evalUsgk 10 usgEx3 (ρe 10)).embed
  == (⟨⟨.ofList [("a", .u1), ("k", .u1)]⟩, .rep .uω⟩ : UD)
#guard (evalUsgk 10 usgEx4 Env.empty).embed
  == (⟨⟨.ofList [("i", .uω), ("j", .uω)]⟩, .rep .uω⟩ : UD)
#guard (evalUsgk 10 usgEx5 Env.empty).embed == (⟨⟨.ofList [("z", .uω)]⟩, .rep .uω⟩ : UD)
#guard (evalUsgk 10 usgEx6 Env.empty).embed == (⟨⟨.ofList [("i", .u1)]⟩, .cons .u1 (.rep .uω)⟩ : UD)
#guard (evalUsgk 10 usgEx7 Env.empty).embed
  == (⟨⟨.ofList [("j", .u1)]⟩, .cons .u1 (.rep .uω)⟩ : UD)
#guard (evalUsgk 3 rDiv Env.empty).embed
  == (⟨⟨.ofList [("r", .uω)]⟩, .cons .u1 (.cons .u1 (.cons .u1 (.rep .u1)))⟩ : UD)

end AbsDen
