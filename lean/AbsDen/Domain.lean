import AbsDen.Trace

open Iris Iris.COFE OFE

/-! # The ByNeed domain `D`, solved via `Fix`

Faithful to `AbsDen/ByNeed.lean`: a heap-threaded, trace-producing computation

    D ≅ Heap(▶D) -n> Trace (Value(▶D) × Heap(▶D))

The `Trace`-inside-`D` nesting needs the COFE-input solver. The value/heap part is
the contractive `OFunctor` `ValueHeapOF`, so its functor laws come for free; only
the outer `Hom` and `Trace` layers are handled by hand. -/

namespace AbsDen

variable {A B C : Type} [COFE A] [COFE B] [COFE C]

/-! ## `laterMap` and `Trace.map` are functorial / proper (not shipped by iris-lean) -/

theorem laterMap_id : laterMap (OFE.Hom.id : A -n> A) ≡ OFE.Hom.id := fun _ => .rfl

theorem laterMap_comp (f : A -n> B) (g : B -n> C) :
    laterMap (g.comp f) ≡ (laterMap g).comp (laterMap f) := fun _ => .rfl

theorem Trace.map_proper {V₁ V₂ : Type} [COFE V₁] [COFE V₂] {h h' : V₁ -n> V₂}
    (H : h ≡ h') : Trace.map h ≡ Trace.map h' :=
  equiv_dist.2 fun _ => Trace.map_ne H.dist

/-- The value functor's identity law, as a `Hom` equivalence. -/
theorem vmap_id {α β : Type} [COFE α] [COFE β] :
    OFunctor.map (F := ValueHeapOF) (Hom.id : α -n> α) (Hom.id : β -n> β) ≡ Hom.id :=
  fun z => OFunctor.map_id z

/-- The value functor's composition law, as a `Hom` equivalence. -/
theorem vmap_comp {α₁ α₂ α₃ β₁ β₂ β₃ : Type}
    [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) :
    OFunctor.map (F := ValueHeapOF) (f.comp g) (g'.comp f') ≡
      (OFunctor.map g g').comp (OFunctor.map f f') :=
  fun z => OFunctor.map_comp f g f' g' z

/-! ## The domain signature `DSig` as a `OFunctorContractive` -/

/-- `D ≅ Heap(▶D) -n> Trace (Value(▶D) × Heap(▶D))`. -/
abbrev DSig : ∀ α β [COFE α] [COFE β], Type :=
  fun α β _ _ => GenMap (Later α) -n> Trace (ValueHeapOF α β)

instance : OFunctorContractive DSig where
  ofe := inferInstance
  map f g := Hom.map (GenMap.lift (laterMap f)) (Trace.map (OFunctor.map (F := ValueHeapOF) f g))
  map_ne := ⟨fun {_ _ _} H1 {_ _} H2 =>
    OFE.NonExpansive₂.ne (f := Hom.map) (GenMap.lift_ne (laterMap_ne H1))
      (Trace.map_ne (OFunctor.map_ne.ne H1 H2))⟩
  map_id x := by
    intro y
    refine .trans (Trace.map_proper vmap_id _) ?_
    refine .trans (Trace.map_id _) ?_
    exact x.ne.eqv (((GenMap.lift_proper laterMap_id).trans GenMap.lift_id) y)
  map_comp f g f' g' x := by
    intro y
    refine .trans (Trace.map_proper (vmap_comp f g f' g') _) ?_
    refine .trans (Trace.map_comp _ _ _) ?_
    refine (Trace.map _).ne.eqv ((Trace.map _).ne.eqv (x.ne.eqv ?_))
    exact ((GenMap.lift_proper (laterMap_comp g f)).trans (GenMap.lift_comp _ _)) y
  map_contractive.distLater_dist H :=
    OFE.NonExpansive₂.ne (f := Hom.map)
      (GenMap.lift_ne (Trace.laterMap_contractive fun m hm => (H m hm).1))
      (Trace.map_ne ((OFunctorContractive.map_contractive (F := ValueHeapOF)).1 H))

instance : Inhabited (DSig (ULift Unit) (ULift Unit)) :=
  ⟨⟨fun _ => default, ⟨fun _ _ _ _ => .rfl⟩⟩⟩

/-- The ByNeed-shaped domain, solved by the COFE-input solver. -/
def D : Type := OFunctor.Fix DSig

instance : COFE D := inferInstanceAs (COFE (OFunctor.Fix DSig))
instance : Inhabited D := inferInstanceAs (Inhabited (OFunctor.Fix DSig))

/-- `D ≅ Heap(▶D) -n> Trace (Value(▶D) × Heap(▶D))`, by construction. -/
def D.iso : OFE.Iso (DSig D D) D := OFunctor.Fix.fastIso (F := DSig)

/-- Run a computation against a heap, producing a trace. -/
def D.unfold : D -n> (GenMap (Later D) -n> Trace (ValueHeapOF D D)) :=
  OFunctor.Fix.fastUnfold (F := DSig)
/-- Package a heap-to-trace function as a computation. -/
def D.fold : (GenMap (Later D) -n> Trace (ValueHeapOF D D)) -n> D :=
  OFunctor.Fix.fastFold (F := DSig)

theorem D.fold_unfold (d : D) : D.fold (D.unfold d) ≡ d := OFunctor.Fix.fastFold_fastUnfold (F := DSig) d
theorem D.unfold_fold (f : GenMap (Later D) -n> Trace (ValueHeapOF D D)) :
    D.unfold (D.fold f) ≡ f := OFunctor.Fix.fastUnfold_fastFold (F := DSig) f

/- Keep the solved domain opaque so downstream proofs never unfold the tower. -/
attribute [irreducible] D D.fold D.unfold

end AbsDen
