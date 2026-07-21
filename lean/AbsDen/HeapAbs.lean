import AbsDen.AbstractDomain
import AbsDen.ByNeed
import Iris.Std.HeapInstances
import Iris.Algebra.Heap
import Iris.Algebra.View
import Iris.Algebra.HeapView
import Iris.Algebra.Agree
import Iris.Algebra.DFrac
import Iris.Instances.UPred.Instance

/-! # The heap abstraction

Ghost state for by-need soundness: a table assigning each allocated address
its abstract value. `HeapAbsAuth w` is the authoritative copy, held by the
heap invariant; `FetchAbs a â` is the duplicable per-address fact an
`IsThunk` carries. Validity forces every element in circulation to agree
with the authoritative copy, so owning `HeapAbsAuth w` bounds the whole
ghost state, which is what makes `nextFree` fresh for the ghost side too. -/

open Iris Iris.BI Iris.COFE OFE CMRA

namespace AbsDen

/-- The heap abstraction: the ghost table mapping each allocated address to
    its abstract value. A `def`, so the generic map instances (whose heads
    have the shape `M V`) match it first-order. -/
def HeapAbs : Type → Type := fun T => Addr → Option T

instance : Std.LawfulPartialMap HeapAbs Addr :=
  inferInstanceAs (Std.LawfulPartialMap (fun T => Addr → Option T) Addr)

/-- The camera of the heap abstraction: an authoritative map over addresses
    with agreeing, discardable per-address fragments. -/
abbrev HeapAbsView (V : Type) : Type :=
  HeapView Addr (Agree (LeibnizO V)) HeapAbs

/-- The propositions of the by-need soundness relation: step-indexed
    predicates over the heap abstraction. -/
abbrev NeedProp (V : Type) : Type := UPred (HeapAbsView V)

variable {V : Type}

/-- The map's image in the camera: abstract values wrapped in agreement. -/
def HeapAbs.image (w : HeapAbs V) : HeapAbs (Agree (LeibnizO V)) :=
  Std.PartialMap.map (fun â => toAgree ⟨â⟩) w

/-- Custody of the authoritative heap abstraction. -/
def HeapAbsAuth (w : HeapAbs V) : NeedProp V :=
  UPred.ownM (HeapView.Auth (.own One.one) (HeapAbs.image w))

/-- The abstraction of `fetch a`: the address's promised abstract value is
    `â`. One element of the heap abstraction. -/
def FetchAbs (a : Addr) (â : V) : NeedProp V :=
  UPred.ownM (HeapView.Frag a .discard (toAgree ⟨â⟩))

/-- Elements are duplicable knowledge: the fraction is discarded and
    agreement is idempotent. -/
instance fetchAbs_persistent (a : Addr) (â : V) :
    Persistent (FetchAbs (V := V) a â) :=
  inferInstanceAs (Persistent (UPred.ownM _))

/-- Extract a pure consequence of validity at every step index. -/
theorem internalValid_elim {M : Type _} [UCMRA M] {A : Type _} [CMRA A] {m : A}
    {φ : Prop} (H : ∀ n, ✓{n} m → φ) :
    (internalCmraValid m : UPred M) ⊢ ⌜φ⌝ :=
  fun n _ h => H n h

/-- Every element in circulation is an entry of the authoritative map. -/
theorem heapAbs_lookup (w : HeapAbs V) (a : Addr) (â : V) :
    iprop(HeapAbsAuth w ∗ FetchAbs a â) ⊢ (⌜Std.PartialMap.get? w a = some â⌝ : NeedProp V) := by
  refine .trans (UPred.ownM_op _ _).2 ?_
  refine .trans (UPred.ownM_valid _) ?_
  refine internalValid_elim fun n hv => ?_
  obtain ⟨v', dq', _, hget, hvv, hincl⟩ := HeapView.auth_op_frag_validN_iff.mp hv
  rw [HeapAbs.image, Std.LawfulPartialMap.get?_map] at hget
  obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp hget
  have hagree : toAgree (⟨â⟩ : LeibnizO V) ≡{n}≡ toAgree ⟨b'⟩ := by
    rcases Option.some_incN_some_iff.mp hincl with heqv | hinc
    · exact heqv.2
    · obtain ⟨z, hz⟩ := hinc
      exact Agree.valid_includedN hvv.2 ⟨z.2, hz.2⟩
  rw [hb, LeibnizO.dist_inj (Agree.toAgree_injN hagree)]

/-- Allocation: bind a fresh address and mint its element. -/
theorem heapAbs_insert (w : HeapAbs V) (a : Addr) (â : V)
    (h : Std.PartialMap.get? w a = none) :
    HeapAbsAuth w ⊢ iprop(|==> (HeapAbsAuth (Std.PartialMap.insert w a â) ∗ FetchAbs a â)) := by
  have hfresh : Std.PartialMap.get? (HeapAbs.image w) a = none := by
    rw [HeapAbs.image, Std.LawfulPartialMap.get?_map, h]; rfl
  have hup := UpdateP.of_update
    (HeapView.update_one_alloc (K := Addr) (H := HeapAbs)
      (v1 := toAgree (⟨â⟩ : LeibnizO V)) (dq := .discard) hfresh DFrac.valid_discard Agree.toAgree_valid)
  have hmono : (iprop(∃ y, ⌜HeapView.Auth (DFrac.own One.one)
        (Std.PartialMap.insert (HeapAbs.image w) a (toAgree (LeibnizO.mk â))) •
        HeapView.Frag a DFrac.discard (toAgree (LeibnizO.mk â)) = y⌝ ∧ UPred.ownM y) : NeedProp V) ⊢
      iprop(HeapAbsAuth (Std.PartialMap.insert w a â) ∗ FetchAbs a â) := by
    refine exists_elim fun y => ?_
    refine pure_elim _ and_elim_l fun hy => ?_
    refine and_elim_r.trans ?_
    subst hy
    refine .trans (UPred.ownM_op _ _).1 ?_
    refine sep_mono ?_ .rfl
    have himg : HeapAbs.image (Std.PartialMap.insert w a â)
        = Std.PartialMap.insert (HeapAbs.image w) a (toAgree ⟨â⟩) := by
      rw [HeapAbs.image, HeapAbs.image, Std.LawfulPartialMap.map_insert]
    rw [HeapAbsAuth, himg]
    exact .rfl
  exact (UPred.bupd_ownM_updateP _ _ hup).trans (bupd_mono hmono)

end AbsDen
