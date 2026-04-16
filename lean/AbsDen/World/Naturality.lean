import AbsDen.World.Basic

/-!
# Naturality of `Fix.unfold` with respect to `restrictStep`

For `World.Function`-based Fix types, `unfold` after `restrictStep` equals
`unfold` with a weakened inequality proof.
-/

namespace World

set_option maxHeartbeats 3200000 in
/-- For `World.Function`-based Fix types, `unfold` after `restrictStep` equals
    `unfold` with a weakened inequality proof. -/
theorem Fix.unfold_restrictStep_Function
    {A B : (Nat → Type u) → (Nat → Type u)} [LocalFunctor A] [LocalFunctor B]
    {n : Nat} (x : Fix (fun X => Function (A X) (B X)) (n + 1))
    (m : Nat) (hm : m ≤ n) :
    Fix.unfold (restrictStep x) m hm =
    Fix.unfold x m (Nat.le_succ_of_le hm) := by
  simp [World.Fix.unfold, World.restrictStep]
  rw [cast_forall_le_congr_apply, cast_forall_le_congr_apply]
  · rfl
  · intro k hk
    congr 1 <;> exact LocalFunctor.property _ _ k
      (fun j hj => Later.ext _ _ j (fun i hi => Fix.chain_agree _ n i (by omega)))
  · intro k hk
    congr 1 <;> exact LocalFunctor.property _ _ k
      (fun j hj => Later.ext _ _ j (fun i hi => Fix.chain_agree _ n i (by omega)))

end World
