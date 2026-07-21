import Iris.Algebra.GenMap
import Batteries.Data.List.Basic

/-! Small gaps in iris-lean that ByNeed needs, kept apart so they can be
    upstreamed. iris-lean ships `OFunctor (GenMapOF F)` but not its contractive
    counterpart, and has no OFE/OFunctor on `List` at all. -/

open Iris Iris.COFE OFE

namespace Iris.COFE

/-- `GenMapOF` preserves contractiveness (it post-composes a non-expansive
    pointwise lift onto `F`'s functorial action). -/
instance instOFunctorContractive_GenMapOF (F : OFunctorPre) [OFunctorContractive F] :
    OFunctorContractive (GenMapOF F) where
  map_contractive.1 H k γ :=
    optionMap_ne.ne ((OFunctorContractive.map_contractive (F := F)).distLater_dist H) (k.car γ)

end Iris.COFE

namespace AbsDen
open Iris Iris.COFE OFE

/-! ## `List` OFE and `ListOF` functor

The OFE on `List α` is pointwise (`Forall₂`): two lists are `n`-close iff they
have equal length and corresponding elements are `n`-close. This is the standard
`listO`/`listOF` of Iris, which iris-lean does not yet ship. -/

section ListHelpers
variable {α β : Type _}

theorem forall₂_length {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) : l1.length = l2.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall₂_getElem {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length) :
    R l1[i] l2[i] := by
  induction h generalizing i with
  | nil => simp at h1
  | cons hx _ ih =>
    cases i with
    | zero => exact hx
    | succ j => exact ih j (by simpa using h1) (by simpa using h2)

theorem forall₂_of_getElem {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (hl : l1.length = l2.length)
    (h : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]) :
    List.Forall₂ R l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => exact .nil
    | cons => simp at hl
  | cons a as ih =>
    cases l2 with
    | nil => simp at hl
    | cons b bs =>
      refine .cons (h 0 (by simp) (by simp)) (ih (by simpa using hl) (fun i h1 h2 => ?_))
      exact h (i+1) (by simpa using h1) (by simpa using h2)

end ListHelpers

section ListO
variable {α : Type _} [OFE α]

instance instOFE_List : OFE (List α) where
  Equiv l1 l2 := List.Forall₂ (· ≡ ·) l1 l2
  Dist n l1 l2 := List.Forall₂ (· ≡{n}≡ ·) l1 l2
  dist_eqv :=
    { refl := fun l => by
        induction l with
        | nil => exact .nil
        | cons a as ih => exact .cons (OFE.dist_eqv.refl a) ih
      symm := fun h => by
        induction h with
        | nil => exact .nil
        | cons hx _ ih => exact .cons (OFE.dist_eqv.symm hx) ih
      trans := fun h1 h2 =>
        forall₂_of_getElem ((forall₂_length h1).trans (forall₂_length h2))
          (fun i hi1 hi3 => OFE.dist_eqv.trans
            (forall₂_getElem h1 i hi1 ((forall₂_length h1) ▸ hi1))
            (forall₂_getElem h2 i ((forall₂_length h1) ▸ hi1) hi3)) }
  equiv_dist :=
    { mp := fun h n => by
        induction h with
        | nil => exact .nil
        | cons hx _ ih => exact .cons (OFE.equiv_dist.mp hx n) ih
      mpr := fun h =>
        forall₂_of_getElem (forall₂_length (h 0))
          (fun i hi1 hi2 => OFE.equiv_dist.mpr (fun n => forall₂_getElem (h n) i hi1 hi2)) }
  dist_lt := fun h hlt => by
    induction h with
    | nil => exact .nil
    | cons hx _ ih => exact .cons (OFE.dist_lt hx hlt) ih

instance instIsCOFE_List [IsCOFE α] : IsCOFE (List α) where
  compl c :=
    List.ofFn (n := (c 0).length) fun i =>
      IsCOFE.compl
        { chain := fun k => (c k)[(i : Nat)]'(by rw [forall₂_length (c.cauchy (Nat.zero_le k))]; exact i.isLt)
          cauchy := fun {n j} hnj => forall₂_getElem (c.cauchy hnj) (i : Nat) _ _ }
  conv_compl {n c} := by
    refine forall₂_of_getElem ?_ ?_
    · rw [List.length_ofFn, forall₂_length (c.cauchy (Nat.zero_le n))]
    · intro i h1 h2
      rw [List.getElem_ofFn]
      exact IsCOFE.conv_compl

end ListO

section ListOF
variable {α β : Type _} [OFE α] [OFE β]

/-- Non-expansive `List.map` for the `List` OFE. -/
def List.mapO (f : α -n> β) : List α -n> List β :=
  ⟨List.map f, ⟨fun {_ l1 l2} h => by
    induction h with
    | nil => exact .nil
    | cons hx _ ih => exact .cons (f.ne.ne hx) ih⟩⟩

end ListOF

/-- The `List` OFunctor: `ListOF F α β = List (F α β)`, acting by `List.map`. -/
abbrev ListOF (F : OFunctorPre) : OFunctorPre := fun A B _ _ => List (F A B)

instance instOFunctor_ListOF (F : OFunctorPre) [OFunctor F] : OFunctor (ListOF F) where
  ofe := inferInstance
  map f g := List.mapO (OFunctor.map f g)
  map_ne.ne {_ _ _} Hf {_ _} Hg l := by
    induction l with
    | nil => exact .nil
    | cons a as ih => exact .cons (OFunctor.map_ne.ne Hf Hg a) ih
  map_id l := by
    induction l with
    | nil => exact .nil
    | cons a as ih => exact .cons (OFunctor.map_id a) ih
  map_comp f g f' g' l := by
    induction l with
    | nil => exact .nil
    | cons a as ih => exact .cons (OFunctor.map_comp f g f' g' a) ih

instance instOFunctorContractive_ListOF (F : OFunctorPre) [OFunctorContractive F] :
    OFunctorContractive (ListOF F) where
  map_contractive.1 {_ _ _} H l := by
    induction l with
    | nil => exact .nil
    | cons a as ih => exact .cons ((OFunctorContractive.map_contractive (F := F)).1 H a) ih

/-! ## `GenMap` is complete

iris-lean gives `GenMap` an OFE but no completion. The OFE is pointwise over keys
into `Option V`, so a chain of `GenMap`s completes pointwise; the bound carries
over from the chain's first element, because `c 0 ≡{0}≡ c i` already pins down the
support at every index. -/

section GenMapCOFE
variable {V : Type _} [OFE V]

/-- The per-key chain of a chain of `GenMap`s. -/
def genMapChainAt (c : Chain (GenMap V)) (k : Nat) : Chain (Option V) where
  chain i := (c i).car k
  cauchy h := c.cauchy h k

instance instIsCOFE_GenMap [IsCOFE V] : IsCOFE (GenMap V) where
  compl c :=
    { car := fun k => IsCOFE.compl (genMapChainAt c k)
      bound := by
        obtain ⟨N, hN⟩ := (c 0).bound
        refine ⟨N, fun k hk => ?_⟩
        have h0 : genMapChainAt c k 0 = none := hN k hk
        rw [chain_none_const h0]; rfl }
  conv_compl {n c} := fun k => IsCOFE.conv_compl

end GenMapCOFE

/-! ## `GenMap.lift` is functorial (the pointwise lift used by `GenMapOF`) -/

section GenMapLift
variable {α β γ : Type _} [OFE α] [OFE β] [OFE γ]

theorem GenMap.lift_ne {n} {f f' : α -n> β} (H : f ≡{n}≡ f') :
    GenMap.lift f ≡{n}≡ GenMap.lift f' := by
  intro g k
  show Option.map f (g.car k) ≡{n}≡ Option.map f' (g.car k)
  cases g.car k with
  | none => exact OFE.dist_eqv.refl _
  | some a => exact some_dist_some.mpr (H a)

theorem GenMap.lift_proper {f f' : α -n> β} (H : f ≡ f') :
    GenMap.lift f ≡ GenMap.lift f' := by
  intro g k
  show Option.map f (g.car k) ≡ Option.map f' (g.car k)
  cases g.car k with
  | none => exact .rfl
  | some a => exact H a

theorem GenMap.lift_id : GenMap.lift (OFE.Hom.id : α -n> α) ≡ OFE.Hom.id := by
  intro g k
  show Option.map id (g.car k) ≡ g.car k
  cases g.car k <;> exact .rfl

theorem GenMap.lift_comp (f : α -n> β) (h : β -n> γ) :
    GenMap.lift (h.comp f) ≡ (GenMap.lift h).comp (GenMap.lift f) := by
  intro g k
  show Option.map (h.comp f) (g.car k) ≡ Option.map h (Option.map f (g.car k))
  cases g.car k <;> exact .rfl

end GenMapLift

/-! ## A deterministic fresh key for `GenMap`

iris-lean only proves a fresh key *exists*. Allocation in a non-expansive
heap-to-trace map needs a fresh key that depends only on the support (so it
agrees on `n`-close heaps): the least unmapped key. -/

section GenMapFresh
variable {β : Type _}

instance instDecCarNone (g : GenMap β) : DecidablePred (fun k => g.car k = none) := fun k =>
  match h : g.car k with
  | none => isTrue h
  | some _ => isFalse (fun hc => by simp [h] at hc)

/-- Upward-search relation: advance to `b+1` only while `p b` fails. -/
private def SearchStep (p : Nat → Bool) (a b : Nat) : Prop := a = b + 1 ∧ p b = false

/-- Cofinal truth of `p` makes every index accessible for the upward search. -/
private theorem searchStep_acc (p : Nat → Bool) (N : Nat) (hN : ∀ k, N ≤ k → p k = true) :
    ∀ k, Acc (SearchStep p) k := by
  have aux : ∀ d k, N - k = d → Acc (SearchStep p) k := by
    intro d
    induction d with
    | zero => intro k hk; constructor; intro a h; have := hN k (by omega); simp_all [SearchStep]
    | succ m ih => intro k hk; constructor; intro a h; rw [h.1]; exact ih (k + 1) (by omega)
  exact fun k => aux (N - k) k rfl

/-- `p` holding cofinally makes the upward-search relation well-founded. -/
private theorem searchStep_wf (p : Nat → Bool) (H : ∃ N, ∀ k, N ≤ k → p k = true) :
    WellFounded (SearchStep p) :=
  ⟨H.elim fun N hN => searchStep_acc p N hN⟩

/-- Least index satisfying `p`, by well-founded upward search (well-foundedness
    comes from `p` holding cofinally; the accessibility is erased at runtime, so
    this is computable). -/
def leastCore (p : Nat → Bool) (wf : WellFounded (SearchStep p)) (k : Nat) : Nat :=
  wf.fix (C := fun _ => Nat)
    (fun k rec => if hp : p k = true then k else rec (k + 1) ⟨rfl, by simpa using hp⟩) k

theorem leastCore_eq (p : Nat → Bool) (wf : WellFounded (SearchStep p)) (k : Nat) :
    leastCore p wf k = if hp : p k = true then k else leastCore p wf (k + 1) :=
  WellFounded.fix_eq _ _ _

theorem leastCore_spec (p : Nat → Bool) (wf : WellFounded (SearchStep p)) (k : Nat) :
    p (leastCore p wf k) = true := by
  induction k using wf.induction with
  | _ k ih =>
    rw [leastCore_eq]; split
    · assumption
    · rename_i hp; exact ih (k + 1) ⟨rfl, by simpa using hp⟩

theorem leastCore_congr (p p' : Nat → Bool) (hpp : ∀ k, p k = p' k)
    (wf : WellFounded (SearchStep p)) (wf' : WellFounded (SearchStep p')) (k : Nat) :
    leastCore p wf k = leastCore p' wf' k := by
  induction k using wf.induction with
  | _ k ih =>
    rw [leastCore_eq p wf k, leastCore_eq p' wf' k]
    by_cases hp : p k = true
    · rw [dif_pos hp, dif_pos (show p' k = true by rw [← hpp k]; exact hp)]
    · rw [dif_neg hp, dif_neg (show ¬ p' k = true by rw [← hpp k]; exact hp)]
      exact ih (k + 1) ⟨rfl, by simpa using hp⟩

/-- Some key is unmapped (the support is bounded), in cofinal form. -/
theorem genMap_isNone_cofinal (g : GenMap β) :
    ∃ N, ∀ k, N ≤ k → (g.car k).isNone = true := by
  obtain ⟨N, hN⟩ := g.bound
  exact ⟨N, fun k hk => by rw [hN k hk]; rfl⟩

/-- The least unmapped key, computed by upward search. -/
def genMapLeast (g : GenMap β) : Nat :=
  leastCore (fun k => (g.car k).isNone) (searchStep_wf _ (genMap_isNone_cofinal g)) 0

theorem genMapLeast_spec (g : GenMap β) : g.car (genMapLeast g) = none := by
  have h : (g.car (genMapLeast g)).isNone = true := leastCore_spec (fun k => (g.car k).isNone) _ 0
  revert h; cases g.car (genMapLeast g) <;> simp [Option.isNone]

theorem genMapLeast_congr {β' : Type _} (g : GenMap β) (g' : GenMap β')
    (hiff : ∀ k, g.car k = none ↔ g'.car k = none) : genMapLeast g = genMapLeast g' := by
  have hpp : ∀ k, (g.car k).isNone = (g'.car k).isNone := fun k => by
    have := hiff k
    cases hg : g.car k <;> cases hg' : g'.car k <;> simp_all [Option.isNone]
  exact leastCore_congr _ _ hpp _ _ 0

end GenMapFresh

end AbsDen
