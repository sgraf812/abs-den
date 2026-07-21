import AbsDen.UsageAnalysis

/-! # Usage environments, pointwise

`Uses` reads an absent key as `u0` and compares up to `u0`-thinning, so it
denotes the total function `φ !? ·`. This module ports the underlying
`Std.HashMap` facts to that view: combining acts key-wise (`getElem?_merge`), and
`BEq` equality is agreement of the `getD` readings (`beq_iff_get`), the thinned
map exposing exactly the non-`u0` keys. -/

namespace AbsDen
open Std

/-- `U`'s `BEq` reflects equality, so `Std.HashMap`'s key-value equality API
    applies to usage environments. -/
instance instLawfulBEqU : LawfulBEq U where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

/-- Two underlying maps are `BEq`-equal exactly when they agree at every key. -/
theorem beqMap_iff (m₁ m₂ : Std.HashMap Var U) :
    (m₁ == m₂) = true ↔ ∀ (k : Var), m₁[k]? = m₂[k]? := by
  rw [Std.HashMap.beq_iff_equiv]
  exact ⟨fun h k => h.getElem?_eq, Std.HashMap.Equiv.of_forall_getElem?_eq⟩

/-- The per-key combiner threaded through `Uses.merge`. -/
def mstep (f : U → U → U) (u₂ : U) : Option U → Option U
  | none => some u₂
  | some u₁ => some (f u₁ u₂)

/-- Folding `alter` over a distinct-key list touches each key at most once. -/
theorem foldl_alter_getElem? (f : U → U → U) (x : Var) :
    ∀ (l : List (Var × U)), l.Pairwise (fun a b => (a.1 == b.1) = false) →
    ∀ (acc : Std.HashMap Var U),
    (l.foldl (fun a p => a.alter p.1 (mstep f p.2)) acc)[x]? =
      match l.find? (fun p => p.1 == x) with
      | some p => mstep f p.2 acc[x]?
      | none => acc[x]?
  | [], _, acc => by simp
  | p :: l', hpw, acc => by
    rw [List.foldl_cons,
        foldl_alter_getElem? f x l' hpw.tail (acc.alter p.1 (mstep f p.2))]
    simp only [Std.HashMap.getElem?_alter, List.find?_cons]
    by_cases hpx : (p.1 == x) = true
    · have hnone : l'.find? (fun q => q.1 == x) = none := by
        rw [List.find?_eq_none]
        intro q hq hqx
        have hpq : (p.1 == q.1) = false := (List.pairwise_cons.mp hpw).1 q hq
        rw [beq_iff_eq] at hpx hqx; rw [hpx, hqx] at hpq; simp at hpq
      simp only [hpx, hnone, if_true]
      congr 1
      exact Std.HashMap.getElem?_congr hpx
    · simp only [Bool.not_eq_true] at hpx
      simp only [hpx, if_false, Bool.false_eq_true]

/-- A distinct-key list finds its entry at a present key. -/
theorem find?_key_eq (x : Var) : ∀ (l : List (Var × U)),
    l.Pairwise (fun a b => (a.1 == b.1) = false) → ∀ u,
    (x, u) ∈ l → l.find? (fun p => p.1 == x) = some (x, u)
  | p :: l', hpw, u, hmem => by
    rw [List.find?_cons]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp
    · have hpx : (p.1 == x) = false := (List.pairwise_cons.mp hpw).1 (x, u) h
      simp only [hpx]
      exact find?_key_eq x l' hpw.tail u h

/-- `getElem?` of `Uses.merge`: key-wise, the right value is combined with the
    left through `mstep`, an absent right key leaving the left untouched. -/
theorem Uses.getElem?_merge (f : U → U → U) (φ₁ φ₂ : Uses) (x : Var) :
    (Uses.merge f φ₁ φ₂)[x]? =
      match φ₂[x]? with
      | some u₂ => mstep f u₂ φ₁[x]?
      | none => φ₁[x]? := by
  simp only [Uses.getElem?_toMap]
  show (φ₂.toMap.fold (init := φ₁.toMap) (fun acc x u₂ => acc.alter x (mstep f u₂)))[x]? = _
  rw [Std.HashMap.fold_eq_foldl_toList,
      foldl_alter_getElem? f x φ₂.toMap.toList φ₂.toMap.distinct_keys_toList φ₁.toMap]
  cases hx : φ₂.toMap[x]? with
  | none =>
    have hf : φ₂.toMap.toList.find? (fun p => p.1 == x) = none := by
      rw [List.find?_eq_none]
      intro p hp hpx
      rw [beq_iff_eq] at hpx; subst hpx
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hp
      rw [hp] at hx; simp at hx
    rw [hf]
  | some u₂ =>
    rw [find?_key_eq x φ₂.toMap.toList φ₂.toMap.distinct_keys_toList u₂
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx)]

/-- The thinned map exposes exactly the non-`u0` keys, read through `!?`. -/
theorem Uses.getElem?_thin (φ : Uses) (x : Var) :
    (φ.thin)[x]? = if φ !? x = U.u0 then none else some (φ !? x) := by
  show (φ.toMap.filter (fun _ u => u != U.u0))[x]? = _
  rw [Std.HashMap.getElem?_filter, Uses.get, Std.HashMap.getD_eq_getD_getElem?]
  cases φ.toMap[x]? with
  | none => simp
  | some u => cases u <;> simp

/-- `BEq` equality of usage environments is agreement of their `getD` readings. -/
theorem Uses.beq_iff_get (a b : Uses) :
    (a == b) = true ↔ ∀ x, a !? x = b !? x := by
  show (a.thin == b.thin) = true ↔ _
  rw [beqMap_iff]
  constructor
  · intro h x
    have hx := h x
    rw [Uses.getElem?_thin, Uses.getElem?_thin] at hx
    by_cases ha : a !? x = U.u0 <;> by_cases hb : b !? x = U.u0 <;>
      simp_all
  · intro h x
    rw [Uses.getElem?_thin, Uses.getElem?_thin, h x]

end AbsDen
