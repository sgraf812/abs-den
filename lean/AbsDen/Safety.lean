import Init.Data.Order.Classes
import AbsDen.UsageAnalysis

/-! # Safety properties and the order-theoretic safety extension

The order theory behind `soundness-appendix.lhs` §`sec:safety-extension`. A trace
abstraction is a fold whose value at an infinite trace is the least upper bound
of the folds over its finite prefixes. Comparing that limit against a fixed
abstract element reduces to comparing every prefix, and a predicate that
transfers from the prefixes to the limit is a *safety property* (Lamport). This
module develops that reduction generically, over any join order with least upper
bounds of countable families, with no reference to traces or a specific analysis.

The `Bool`-valued approximation order `⊑` induces the `Prop`-valued `≤`, and the
order laws are the standard `IsPreorder`. Antisymmetry is deliberately absent:
the reduction needs only reflexivity and transitivity, and abstract summaries can
be a quotient (a usage summary reads `rep u` and `cons u (rep u)` as equal), so
`≤` in both directions need not entail syntactic equality. Following
`Init.Internal.Order`'s `CCPO`, the supremum is characterized by a `Prop` and
never computed; it exists only in soundness statements. -/

namespace AbsDen

variable {V : Type} [Lat V]

/-- `x` is a least upper bound of the countable family `c`. -/
def IsLub (c : Nat → V) (x : V) : Prop :=
  (∀ n, c n ≤ x) ∧ ∀ y, (∀ n, c n ≤ y) → x ≤ y

/-- Bounded ω-completeness: every countable family bounded above has a least
    upper bound. Full completeness fails for finite-support summaries (an
    increasing family touching a fresh variable each step has infinite-support
    limit), but a bounded family has bounded support, so its supremum exists. The
    bound is a `Prop`, never a computation. -/
class ChainComplete (V : Type) [Lat V] : Prop where
  has_csup : ∀ (c : Nat → V) (d : V), (∀ n, c n ≤ d) → ∃ x, IsLub c x

variable [ChainComplete V]

theorem csup_exists (c : Nat → V) : ∃ x, ∀ d, (∀ n, c n ≤ d) → IsLub c x := by
  by_cases hb : ∃ d, ∀ n, c n ≤ d
  · obtain ⟨d, hd⟩ := hb
    obtain ⟨x, hx⟩ := ChainComplete.has_csup c d hd
    exact ⟨x, fun _ _ => hx⟩
  · exact ⟨default, fun d hd => absurd ⟨d, hd⟩ hb⟩

/-- The supremum of a countable family: its least upper bound when the family is
    bounded, junk otherwise. Never computed. -/
noncomputable def csup (c : Nat → V) : V := Classical.choose (csup_exists c)

theorem csup_isLub {c : Nat → V} {d : V} (hd : ∀ n, c n ≤ d) : IsLub c (csup c) :=
  Classical.choose_spec (csup_exists c) d hd

theorem le_csup {c : Nat → V} {d : V} (hd : ∀ n, c n ≤ d) (n : Nat) : c n ≤ csup c :=
  (csup_isLub hd).1 n

theorem csup_le {c : Nat → V} {d : V} (hd : ∀ n, c n ≤ d) : csup c ≤ d :=
  (csup_isLub hd).2 d hd

variable [Std.IsPreorder V]

/-- A bounded family's supremum approximates `d` exactly when every member does:
    the limit of the finite-prefix folds is below `d` iff each finite prefix is. -/
theorem csup_le_iff {c : Nat → V} {d₀ : V} (hb : ∀ n, c n ≤ d₀) (d : V) :
    csup c ≤ d ↔ ∀ n, c n ≤ d :=
  ⟨fun h n => Std.IsPreorder.le_trans _ _ _ (le_csup hb n) h, fun hd => csup_le hd⟩

end AbsDen
