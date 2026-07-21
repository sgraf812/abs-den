import AbsDen.IrisExtensions
import AbsDen.Syntax
import AbsDen.FixImpl

open Iris Iris.COFE OFE

/-! The guarded trace type `Trace V ≅ V ⊕ (Event × ▶Trace V) ⊕ ▶Trace V`, and
    (the crux of M2c) its functorial action in the value parameter `V`, built by
    Löb/Banach on top of the solver's non-expansive `Fix.iso`. -/

namespace Iris.OFE.ContractiveHom

/-- Fast runtime for `lazyFixpoint`: the recursive reference sits under the result
    morphism's own lambda, so it unrolls on demand (no `compl`). Sound for the
    guarded contractions used here (`Trace.bindPre`/`mapPre`/`D.memo.op`, guarded
    by `Later`); the `compl`-based spec is kept for proofs. -/
unsafe def unsafeLazyFixpoint {α β : Type} [OFE α] [COFE β] [Inhabited β]
    (f : (α -n> β) -c> (α -n> β)) : α -n> β :=
  ⟨fun t => (f.f (unsafeLazyFixpoint f)).f t, lcProof⟩

/-- The Banach fixpoint specialised to a morphism type `α -n> β`, so its single
    fast runtime implementation covers every use. Definitionally
    `ContractiveHom.fixpoint`, so all its lemmas apply; nested here so
    call sites keep dot notation (`f.lazyFixpoint`). -/
@[implemented_by unsafeLazyFixpoint]
def lazyFixpoint {α β : Type} [OFE α] [COFE β] [Inhabited β]
    (f : (α -n> β) -c> (α -n> β)) : α -n> β := f.fixpoint

end Iris.OFE.ContractiveHom

namespace AbsDen

/-- Trace signature functor on COFE inputs: the returned value `V` is a fixed
    parameter, the guarded tails are the (covariant) recursive slot. It is a
    `OFunctorContractive`, so `Trace` is solved by our own `OFunctor.Fix`. -/
inductive TraceF (V : Type) [COFE V] (α β : Type) [COFE α] [COFE β] : Type where
  | ret (v : V)
  | step (ev : Event) (tl : Later β)
  | invis (tl : Later β)

/-- `laterMap` is non-expansive in its morphism argument. -/
theorem laterMap_ne {A B : Type} [OFE A] [OFE B] {n} {f g : A -n> B} (H : f ≡{n}≡ g) :
    laterMap f ≡{n}≡ laterMap g := fun t _ hm => (H t.car).lt hm

/-- `laterMap` is contractive in its morphism argument (guarded by `▶`). -/
theorem Trace.laterMap_contractive {A B : Type} [OFE A] [OFE B] {n : Nat}
    {f g : A -n> B} (H : OFE.DistLater n f g) : laterMap f ≡{n}≡ laterMap g := by
  intro t m Hlt; exact H m Hlt t.car

namespace TraceF

variable {V : Type} [COFE V] {α β : Type} [COFE α] [COFE β]

/-- Layer distance: the same head constructor with componentwise-close fields. -/
protected def Dist (n : Nat) : TraceF V α β → TraceF V α β → Prop
  | .ret v, .ret v' => v ≡{n}≡ v'
  | .step ev tl, .step ev' tl' => ev = ev' ∧ tl ≡{n}≡ tl'
  | .invis tl, .invis tl' => tl ≡{n}≡ tl'
  | _, _ => False

instance : OFE (TraceF V α β) where
  Equiv x y := ∀ n, TraceF.Dist n x y
  Dist := TraceF.Dist
  dist_eqv := {
    refl := fun x => by
      cases x with
      | ret v => exact OFE.dist_eqv.refl v
      | step ev tl => exact ⟨rfl, OFE.dist_eqv.refl tl⟩
      | invis tl => exact OFE.dist_eqv.refl tl
    symm := fun {x y} h => by
      cases x <;> cases y <;> try exact False.elim h
      · exact OFE.dist_eqv.symm h
      · exact ⟨h.1.symm, OFE.dist_eqv.symm h.2⟩
      · exact OFE.dist_eqv.symm h
    trans := fun {x y z} h1 h2 => by
      cases x <;> cases y <;> try exact False.elim h1
      · cases z <;> try exact False.elim h2
        exact OFE.dist_eqv.trans h1 h2
      · cases z <;> try exact False.elim h2
        exact ⟨h1.1.trans h2.1, OFE.dist_eqv.trans h1.2 h2.2⟩
      · cases z <;> try exact False.elim h2
        exact OFE.dist_eqv.trans h1 h2 }
  equiv_dist := Iff.rfl
  dist_lt {n x y m} h hm := by
    cases x <;> cases y <;> try exact False.elim h
    · exact h.lt hm
    · exact ⟨h.1, h.2.lt hm⟩
    · exact h.lt hm

instance ret.ne : NonExpansive (ret : V → TraceF V α β) := ⟨fun {_ _ _} h => h⟩
instance invis.ne : NonExpansive (invis : Later β → TraceF V α β) := ⟨fun {_ _ _} h => h⟩
instance step.ne (ev : Event) : NonExpansive (step ev : Later β → TraceF V α β) :=
  ⟨fun {_ _ _} h => ⟨rfl, h⟩⟩

/-- Project the returned value out of a layer, defaulting off-`ret`. -/
private def retProj (seed : V) : TraceF V α β -n> V :=
  ⟨fun x => match x with | .ret v => v | _ => seed,
   ⟨fun {_ x y} h => by
     cases x <;> cases y <;> try exact False.elim h
     · exact h
     · exact OFE.dist_eqv.refl seed
     · exact OFE.dist_eqv.refl seed⟩⟩

/-- Project the guarded tail out of a layer, defaulting off-`step`/`invis`. -/
private def tailProj (seed : Later β) : TraceF V α β -n> Later β :=
  ⟨fun x => match x with | .ret _ => seed | .step _ tl => tl | .invis tl => tl,
   ⟨fun {_ x y} h => by
     cases x <;> cases y <;> try exact False.elim h
     · exact OFE.dist_eqv.refl seed
     · exact h.2
     · exact h⟩⟩

instance : IsCOFE (TraceF V α β) where
  compl c := match c 0 with
    | .ret seed => .ret (compl (c.map (retProj seed)))
    | .step ev seed => .step ev (compl (c.map (tailProj seed)))
    | .invis seed => .invis (compl (c.map (tailProj seed)))
  conv_compl {n c} := by
    cases h1 : c.chain 0 with
    | ret seed =>
      cases h2 : c.chain n with
      | ret v =>
        refine (conv_compl (c := c.map (retProj seed)) (n := n) : _)
          |>.trans ?_
        dsimp only [Chain.map_apply]
        rw [h2]
        exact OFE.dist_eqv.refl v
      | step ev tl =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | invis tl =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
    | step ev seed =>
      cases h2 : c.chain n with
      | ret v =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | step ev' tl =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc
        refine ⟨hc.1.symm, ?_⟩
        refine (conv_compl (c := c.map (tailProj seed)) (n := n) : _).trans ?_
        dsimp only [Chain.map_apply]
        rw [h2]
        exact OFE.dist_eqv.refl tl
      | invis tl =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
    | invis seed =>
      cases h2 : c.chain n with
      | ret v =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | step ev tl =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | invis tl =>
        refine (conv_compl (c := c.map (tailProj seed)) (n := n) : _).trans ?_
        dsimp only [Chain.map_apply]
        rw [h2]
        exact OFE.dist_eqv.refl tl

end TraceF

instance (V : Type) [COFE V] : Inhabited (TraceF V (ULift Unit) (ULift Unit)) :=
  ⟨.invis (Later.next default)⟩

/-- `TraceF` as a `OFunctorContractive`: `map` relabels the guarded tails (the
    recursive slot) and leaves the returned value fixed. -/
instance (V : Type) [COFE V] : OFunctorContractive (TraceF V) where
  ofe := inferInstance
  map _f g :=
    ⟨fun x => match x with
      | .ret v => .ret v
      | .step ev tl => .step ev (laterMap g tl)
      | .invis tl => .invis (laterMap g tl),
     ⟨fun {_ x y} h => by
       cases x <;> cases y <;> try exact False.elim h
       · exact h
       · exact ⟨h.1, (laterMap g).ne.ne h.2⟩
       · exact (laterMap g).ne.ne h⟩⟩
  map_ne := ⟨fun {_ _ _} _ {_ _} Hg x => by
    cases x with
    | ret v => exact OFE.dist_eqv.refl v
    | step ev tl => exact ⟨rfl, laterMap_ne Hg tl⟩
    | invis tl => exact laterMap_ne Hg tl⟩
  map_id x := by cases x <;> rfl
  map_comp _f _g _f' _g' x := by cases x <;> rfl
  map_contractive := ⟨fun {_ _ _} H x => by
    cases x with
    | ret v => exact OFE.dist_eqv.refl v
    | step ev tl => exact ⟨rfl, Trace.laterMap_contractive (fun m hm => (H m hm).2) tl⟩
    | invis tl => exact Trace.laterMap_contractive (fun m hm => (H m hm).2) tl⟩

/-- Guarded trace type over values `V`, solved by the COFE solver's
    `OFunctor.Fix`; its `fold`/`unfold` inherit the fast `Fix.unsafeIso`
    runtime. -/
abbrev Trace (V : Type) [COFE V] : Type := OFunctor.Fix (TraceF V)

example (V : Type) [COFE V] : COFE (Trace V) := inferInstance

/-- One layer unfolded. -/
example (V : Type) [COFE V] :
    OFE.Iso (TraceF V (Trace V) (Trace V)) (Trace V) := OFunctor.Fix.fastIso (F := TraceF V)

section Map
variable {V₁ V₂ : Type} [COFE V₁] [COFE V₂]

/-- One-layer functorial action: relabel the returned value with `h`, and the
    guarded tails with the recursive call `rec`. -/
def Trace.bodyMap (h : V₁ -n> V₂) (rec : Trace V₁ -n> Trace V₂) :
    TraceF V₁ (Trace V₁) (Trace V₁) -n> TraceF V₂ (Trace V₂) (Trace V₂) :=
  ⟨fun x => match x with
    | .ret v => .ret (h v)
    | .step ev tl => .step ev (laterMap rec tl)
    | .invis tl => .invis (laterMap rec tl),
   ⟨fun {_ x y} hd => by
     cases x <;> cases y <;> try exact False.elim hd
     · exact h.ne.ne hd
     · exact ⟨hd.1, (laterMap rec).ne.ne hd.2⟩
     · exact (laterMap rec).ne.ne hd⟩⟩

/-- `bodyMap` congruence in both morphism arguments. -/
theorem Trace.bodyMap_ne {n : Nat} {h h' : V₁ -n> V₂} {rec rec' : Trace V₁ -n> Trace V₂}
    (Hh : h ≡{n}≡ h') (Hrec : laterMap rec ≡{n}≡ laterMap rec')
    (x : TraceF V₁ (Trace V₁) (Trace V₁)) :
    Trace.bodyMap h rec x ≡{n}≡ Trace.bodyMap h' rec' x := by
  cases x with
  | ret v => exact Hh v
  | step ev tl => exact ⟨rfl, Hrec tl⟩
  | invis tl => exact Hrec tl

/-- The Löb operator whose fixpoint is `Trace.map h`. -/
def Trace.mapPre (h : V₁ -n> V₂) (rec : Trace V₁ -n> Trace V₂) : Trace V₁ -n> Trace V₂ :=
  (OFunctor.Fix.fastIso (F := TraceF V₂)).hom.comp
    ((Trace.bodyMap h rec).comp (OFunctor.Fix.fastIso (F := TraceF V₁)).inv)

instance (h : V₁ -n> V₂) : OFE.Contractive (Trace.mapPre h) where
  distLater_dist {n rec rec'} Hl := by
    have hlm : laterMap rec ≡{n}≡ laterMap rec' := Trace.laterMap_contractive Hl
    have hb : Trace.bodyMap h rec ≡{n}≡ Trace.bodyMap h rec' :=
      Trace.bodyMap_ne (OFE.dist_eqv.refl h) hlm
    intro x
    exact (OFunctor.Fix.fastIso (F := TraceF V₂)).hom.ne.ne
      (hb ((OFunctor.Fix.fastIso (F := TraceF V₁)).inv x))

/-- Functorial action of the trace fixpoint in its value parameter, built by
    Banach iteration on the non-expansive `Fix.iso`. -/
def Trace.map (h : V₁ -n> V₂) : Trace V₁ -n> Trace V₂ :=
  (Trace.mapPre h).toContractiveHom.lazyFixpoint

theorem Trace.map_unfold (h : V₁ -n> V₂) : Trace.map h ≡ Trace.mapPre h (Trace.map h) :=
  fixpoint_unfold (Trace.mapPre h).toContractiveHom

/-- `bodyMap` of identities is the identity. -/
theorem Trace.bodyMap_id {V : Type} [COFE V] (y : TraceF V (Trace V) (Trace V)) :
    Trace.bodyMap (OFE.Hom.id) (OFE.Hom.id) y ≡ y := by
  cases y <;> rfl

/-- Functor law: `map` preserves identities. -/
theorem Trace.map_id {V : Type} [COFE V] : Trace.map (OFE.Hom.id : V -n> V) ≡ OFE.Hom.id := by
  refine (fixpoint_unique (f := (Trace.mapPre OFE.Hom.id).toContractiveHom) (x := OFE.Hom.id) ?_).symm
  intro x
  refine .trans (OFunctor.Fix.fastIso (F := TraceF V)).hom_inv.symm ?_
  exact ((OFunctor.Fix.fastIso (F := TraceF V)).hom.ne.eqv
    (Trace.bodyMap_id ((OFunctor.Fix.fastIso (F := TraceF V)).inv x))).symm

/-- Functor law: `map` is non-expansive in the value morphism. -/
theorem Trace.map_ne {n : Nat} {h h' : V₁ -n> V₂} (H : h ≡{n}≡ h') :
    Trace.map h ≡{n}≡ Trace.map h' := by
  refine OFE.ContractiveHom.fixpoint_ne.ne ?_
  intro rec
  have hb : Trace.bodyMap h rec ≡{n}≡ Trace.bodyMap h' rec :=
    Trace.bodyMap_ne H (OFE.dist_eqv.refl _)
  intro x
  exact (OFunctor.Fix.fastIso (F := TraceF V₂)).hom.ne.ne
    (hb ((OFunctor.Fix.fastIso (F := TraceF V₁)).inv x))

/-- `bodyMap` commutes with composition. -/
theorem Trace.bodyMap_comp {V₃ : Type} [COFE V₃] (f : V₁ -n> V₂) (g : V₂ -n> V₃)
    (rf : Trace V₁ -n> Trace V₂) (rg : Trace V₂ -n> Trace V₃)
    (z : TraceF V₁ (Trace V₁) (Trace V₁)) :
    Trace.bodyMap g rg (Trace.bodyMap f rf z) ≡ Trace.bodyMap (g.comp f) (rg.comp rf) z := by
  cases z <;> rfl

/-- Functor law: `map` commutes with composition. -/
theorem Trace.map_comp {V₃ : Type} [COFE V₃] (f : V₁ -n> V₂) (g : V₂ -n> V₃) :
    Trace.map (g.comp f) ≡ (Trace.map g).comp (Trace.map f) := by
  symm
  refine fixpoint_unique (f := (Trace.mapPre (g.comp f)).toContractiveHom)
    (x := (Trace.map g).comp (Trace.map f)) ?_
  intro x
  refine .trans ((Trace.map g).ne.eqv (Trace.map_unfold f x)) ?_
  refine .trans (Trace.map_unfold g _) ?_
  refine (OFunctor.Fix.fastIso (F := TraceF V₃)).hom.ne.eqv ?_
  refine .trans ((Trace.bodyMap g (Trace.map g)).ne.eqv
    (OFunctor.Fix.fastIso (F := TraceF V₂)).inv_hom) ?_
  exact Trace.bodyMap_comp f g (Trace.map f) (Trace.map g) _

end Map

/-! ## Constructors -/

section Cons
variable {V : Type} [COFE V]

/-- One trace layer packaged / unpacked. The fast runtime is inherited from
    `Fix.unsafeIso` via `OFunctor.Fix.fastIso`. -/
def Trace.fold : TraceF V (Trace V) (Trace V) -n> Trace V :=
  OFunctor.Fix.fastFold (F := TraceF V)
def Trace.unfold : Trace V -n> TraceF V (Trace V) (Trace V) :=
  OFunctor.Fix.fastUnfold (F := TraceF V)

/-- A trace that immediately returns a value. -/
def Trace.ret (v : V) : Trace V := Trace.fold (.ret v)
/-- A trace emitting an event, then continuing. -/
def Trace.step (e : Event) (t : Later (Trace V)) : Trace V :=
  Trace.fold (.step e t)
/-- A trace taking one silent `▶` step. -/
def Trace.invis (t : Later (Trace V)) : Trace V := Trace.fold (.invis t)

/-! The constructors are non-expansive (`Trace.fold` after the layer
    constructors), so `ofe_norm` can rewrite under a trace's first layer. -/
instance Trace.ret.ne : NonExpansive (Trace.ret : V → Trace V) :=
  ⟨fun {_ _ _} h => Trace.fold.ne.ne h⟩
instance Trace.invis.ne : NonExpansive (Trace.invis : Later (Trace V) → Trace V) :=
  ⟨fun {_ _ _} h => Trace.fold.ne.ne h⟩
instance Trace.step.ne (e : Event) : NonExpansive (Trace.step e : Later (Trace V) → Trace V) :=
  ⟨fun {_ _ _} h => Trace.fold.ne.ne ⟨rfl, h⟩⟩

theorem Trace.unfold_fold (x : TraceF V (Trace V) (Trace V)) : Trace.unfold (Trace.fold x) ≡ x :=
  OFunctor.Fix.fastUnfold_fastFold (F := TraceF V) x
theorem Trace.fold_unfold (t : Trace V) : Trace.fold (Trace.unfold t) ≡ t :=
  OFunctor.Fix.fastFold_fastUnfold (F := TraceF V) t

/-- Recover a trace from an equation on its unfolding: the layer's fold is
    equivalent to the trace itself. -/
theorem Trace.equiv_of_unfold {t : Trace V} {x : TraceF V (Trace V) (Trace V)}
    (hu : Trace.unfold t = x) : Trace.fold x ≡ t :=
  hu ▸ Trace.fold_unfold t

end Cons

/-! ## Monadic bind

`bind k` substitutes the continuation `k` at returned values and recurses under
the guard on `step`/`invis` tails. Like `map`, it is the Banach fixpoint of a
contractive operator on `Trace A -n> Trace B`. -/

section Bind
variable {A B : Type} [COFE A] [COFE B]

/-- One layer of `bind`: apply `k` to a returned value, recurse guarded on tails. -/
def Trace.bindBody (k : A -n> Trace B) (rec : Trace A -n> Trace B) :
    TraceF A (Trace A) (Trace A) -n> Trace B :=
  ⟨fun x => match x with
    | .ret a => k a
    | .step e tl => Trace.step e (laterMap rec tl)
    | .invis tl => Trace.invis (laterMap rec tl),
   ⟨fun {_ x y} h => by
     cases x <;> cases y <;> try exact False.elim h
     · exact k.ne.ne h
     · obtain ⟨rfl, htl⟩ := h
       exact (Trace.step.ne _).ne ((laterMap rec).ne.ne htl)
     · exact Trace.invis.ne.ne ((laterMap rec).ne.ne h)⟩⟩

/-- The Löb operator whose fixpoint is `Trace.bind k`. -/
def Trace.bindPre (k : A -n> Trace B) (rec : Trace A -n> Trace B) :
    Trace A -n> Trace B :=
  (Trace.bindBody k rec).comp Trace.unfold

instance (k : A -n> Trace B) : OFE.Contractive (Trace.bindPre k) where
  distLater_dist {n rec rec'} H := by
    have hlm : laterMap rec ≡{n}≡ laterMap rec' := Trace.laterMap_contractive H
    intro t
    show Trace.bindBody k rec (Trace.unfold t) ≡{n}≡ Trace.bindBody k rec' (Trace.unfold t)
    rcases Trace.unfold t with a | ⟨e, t'⟩ | t'
    · exact OFE.dist_eqv.refl _
    · exact (Trace.step.ne e).ne (hlm t')
    · exact Trace.invis.ne.ne (hlm t')

/-- Monadic bind on traces. -/
def Trace.bind (k : A -n> Trace B) : Trace A -n> Trace B :=
  (Trace.bindPre k).toContractiveHom.lazyFixpoint

theorem Trace.bind_unfold (k : A -n> Trace B) :
    Trace.bind k ≡ Trace.bindPre k (Trace.bind k) :=
  fixpoint_unfold (Trace.bindPre k).toContractiveHom

theorem Trace.bindPre_ne {n} {k k' : A -n> Trace B} (H : k ≡{n}≡ k') (rec : Trace A -n> Trace B) :
    Trace.bindPre k rec ≡{n}≡ Trace.bindPre k' rec := by
  intro t
  show Trace.bindBody k rec (Trace.unfold t) ≡{n}≡ Trace.bindBody k' rec (Trace.unfold t)
  rcases Trace.unfold t with a | ⟨e, t'⟩ | t'
  · exact H a
  · exact OFE.dist_eqv.refl _
  · exact OFE.dist_eqv.refl _

theorem Trace.bind_ne {n} {k k' : A -n> Trace B} (H : k ≡{n}≡ k') :
    Trace.bind k ≡{n}≡ Trace.bind k' :=
  OFE.ContractiveHom.fixpoint_ne.ne (fun rec => Trace.bindPre_ne H rec)

@[eval_simp] theorem Trace.bind_ret (k : A -n> Trace B) (a : A) : Trace.bind k (Trace.ret a) ≡ k a := by
  refine (Trace.bind_unfold k (Trace.ret a)).trans ?_
  refine ((Trace.bindBody k (Trace.bind k)).ne.eqv (Trace.unfold_fold (.ret a))).trans ?_
  exact .rfl

@[eval_simp] theorem Trace.bind_step (k : A -n> Trace B) (e : Event) (t : Later (Trace A)) :
    Trace.bind k (Trace.step e t) ≡ Trace.step e (laterMap (Trace.bind k) t) := by
  refine (Trace.bind_unfold k (Trace.step e t)).trans ?_
  refine ((Trace.bindBody k (Trace.bind k)).ne.eqv (Trace.unfold_fold (.step e t))).trans ?_
  exact .rfl

@[eval_simp] theorem Trace.bind_invis (k : A -n> Trace B) (t : Later (Trace A)) :
    Trace.bind k (Trace.invis t) ≡ Trace.invis (laterMap (Trace.bind k) t) := by
  refine (Trace.bind_unfold k (Trace.invis t)).trans ?_
  refine ((Trace.bindBody k (Trace.bind k)).ne.eqv (Trace.unfold_fold (.invis t))).trans ?_
  exact .rfl

end Bind

/-! ## The ByNeed value functor

A value is `stuck`, a function, or a constructor application. As a bifunctor on
COFEs the recursive domain occurs guarded under `▶`, contravariantly in the
function argument and covariantly elsewhere, so every occurrence sits under
`LaterOF` and the functor is contractive. The heap is a finite `Nat`-keyed map of
guarded thunks. -/

/-- Value bifunctor: `stuck | fn ▶(α -n> β) | con K (List ▶β)`. The function
    slot is the `LaterOF (HomOF IdOF IdOF)` functor and the argument list the
    `ListOF (LaterOF IdOF)` functor, so the functorial action and its laws
    delegate to those instances field by field. -/
inductive ValueF (α β : Type) [COFE α] [COFE β] : Type where
  | stuck
  | fn (f : Later (α -n> β))
  | con (K : ConTag) (ds : List (Later β))

namespace ValueF

variable {α β : Type} [COFE α] [COFE β]

/-- Layer distance: the same head constructor with componentwise-close fields. -/
protected def Dist (n : Nat) : ValueF α β → ValueF α β → Prop
  | .stuck, .stuck => True
  | .fn f, .fn f' => f ≡{n}≡ f'
  | .con K ds, .con K' ds' => K = K' ∧ ds ≡{n}≡ ds'
  | _, _ => False

instance : OFE (ValueF α β) where
  Equiv x y := ∀ n, ValueF.Dist n x y
  Dist := ValueF.Dist
  dist_eqv := {
    refl := fun x => by
      cases x with
      | stuck => trivial
      | fn f => exact OFE.dist_eqv.refl f
      | con K ds => exact ⟨rfl, OFE.dist_eqv.refl ds⟩
    symm := fun {x y} h => by
      cases x <;> cases y <;> try exact False.elim h
      · trivial
      · exact OFE.dist_eqv.symm h
      · exact ⟨h.1.symm, OFE.dist_eqv.symm h.2⟩
    trans := fun {x y z} h1 h2 => by
      cases x <;> cases y <;> try exact False.elim h1
      · cases z <;> try exact False.elim h2
        trivial
      · cases z <;> try exact False.elim h2
        exact OFE.dist_eqv.trans h1 h2
      · cases z <;> try exact False.elim h2
        exact ⟨h1.1.trans h2.1, OFE.dist_eqv.trans h1.2 h2.2⟩ }
  equiv_dist := Iff.rfl
  dist_lt {n x y m} h hm := by
    cases x <;> cases y <;> try exact False.elim h
    · trivial
    · exact h.lt hm
    · exact ⟨h.1, h.2.lt hm⟩

instance fn.ne : NonExpansive (fn : Later (α -n> β) → ValueF α β) :=
  ⟨fun {_ _ _} h => h⟩
instance con.ne (K : ConTag) : NonExpansive (con K : List (Later β) → ValueF α β) :=
  ⟨fun {_ _ _} h => ⟨rfl, h⟩⟩

/-- Whether a value layer is `stuck`. -/
def isStuck : ValueF α β → Bool
  | .stuck => true
  | _ => false

/-- Layer distance relates only equal head constructors, so stuckness is
    distance-invariant. -/
theorem isStuck_dist {n : Nat} {v v' : ValueF α β} (h : v ≡{n}≡ v') :
    v.isStuck = v'.isStuck := by
  cases v <;> cases v' <;> first | rfl | exact False.elim h

/-- Project the function out of a layer, defaulting off-`fn`. -/
private def fnProj (seed : Later (α -n> β)) : ValueF α β -n> Later (α -n> β) :=
  ⟨fun x => match x with | .fn f => f | _ => seed,
   ⟨fun {_ x y} h => by
     cases x <;> cases y <;> try exact False.elim h
     · exact OFE.dist_eqv.refl seed
     · exact h
     · exact OFE.dist_eqv.refl seed⟩⟩

/-- Project the constructor arguments out of a layer, defaulting off-`con`. -/
private def conProj (seed : List (Later β)) : ValueF α β -n> List (Later β) :=
  ⟨fun x => match x with | .con _ ds => ds | _ => seed,
   ⟨fun {_ x y} h => by
     cases x <;> cases y <;> try exact False.elim h
     · exact OFE.dist_eqv.refl seed
     · exact OFE.dist_eqv.refl seed
     · exact h.2⟩⟩

instance : IsCOFE (ValueF α β) where
  compl c := match c 0 with
    | .stuck => .stuck
    | .fn seed => .fn (compl (c.map (fnProj seed)))
    | .con K seed => .con K (compl (c.map (conProj seed)))
  conv_compl {n c} := by
    cases h1 : c.chain 0 with
    | stuck =>
      cases h2 : c.chain n with
      | stuck => trivial
      | fn f =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | con K ds =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
    | fn seed =>
      cases h2 : c.chain n with
      | stuck =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | fn f =>
        refine (conv_compl (c := c.map (fnProj seed)) (n := n) : _).trans ?_
        dsimp only [Chain.map_apply]
        rw [h2]
        exact OFE.dist_eqv.refl f
      | con K ds =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
    | con K seed =>
      cases h2 : c.chain n with
      | stuck =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | fn f =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc; exact False.elim hc
      | con K' ds =>
        have hc := c.cauchy (Nat.zero_le n); rw [h1, h2] at hc
        refine ⟨hc.1.symm, ?_⟩
        refine (conv_compl (c := c.map (conProj seed)) (n := n) : _).trans ?_
        dsimp only [Chain.map_apply]
        rw [h2]
        exact OFE.dist_eqv.refl ds

end ValueF

/-- `ValueF` as a `OFunctorContractive`: conjugate the function slot, relabel
    the constructor arguments, all through the field functors. -/
instance : OFunctorContractive ValueF where
  ofe := inferInstance
  map f g :=
    ⟨fun x => match x with
      | .stuck => .stuck
      | .fn h => .fn (OFunctor.map (F := LaterOF (HomOF IdOF IdOF)) f g h)
      | .con K ds => .con K (OFunctor.map (F := ListOF (LaterOF IdOF)) f g ds),
     ⟨fun {_ x y} h => by
       cases x <;> cases y <;> try exact False.elim h
       · trivial
       · exact (OFunctor.map (F := LaterOF (HomOF IdOF IdOF)) f g).ne.ne h
       · exact ⟨h.1, (OFunctor.map (F := ListOF (LaterOF IdOF)) f g).ne.ne h.2⟩⟩⟩
  map_ne := ⟨fun {_ _ _} Hf {_ _} Hg x => by
    cases x with
    | stuck => trivial
    | fn h =>
      exact (OFunctor.map_ne (F := LaterOF (HomOF IdOF IdOF))).ne Hf Hg h
    | con K ds => exact ⟨rfl, (OFunctor.map_ne (F := ListOF (LaterOF IdOF))).ne Hf Hg ds⟩⟩
  map_id x := by
    cases x with
    | stuck => intro n; trivial
    | fn h =>
      intro n
      exact OFE.equiv_dist.mp
        (OFunctor.map_id (F := LaterOF (HomOF IdOF IdOF)) h) n
    | con K ds =>
      intro n
      exact ⟨rfl, OFE.equiv_dist.mp (OFunctor.map_id (F := ListOF (LaterOF IdOF)) ds) n⟩
  map_comp f g f' g' x := by
    cases x with
    | stuck => intro n; trivial
    | fn h =>
      intro n
      exact OFE.equiv_dist.mp
        (OFunctor.map_comp (F := LaterOF (HomOF IdOF IdOF)) f g f' g' h) n
    | con K ds =>
      intro n
      exact ⟨rfl, OFE.equiv_dist.mp
        (OFunctor.map_comp (F := ListOF (LaterOF IdOF)) f g f' g' ds) n⟩
  map_contractive := ⟨fun {_ _ _} H x => by
    cases x with
    | stuck => trivial
    | fn h =>
      exact (OFunctorContractive.map_contractive
        (F := LaterOF (HomOF IdOF IdOF))).1 H h
    | con K ds =>
      exact ⟨rfl, (OFunctorContractive.map_contractive (F := ListOF (LaterOF IdOF))).1 H ds⟩⟩

/-- Heap functor: a finite map of guarded thunks (covariant in the value). -/
abbrev HeapOF : OFunctorPre := GenMapOF (LaterOF IdOF)

/-- What a trace returns: a value together with the resulting heap. -/
abbrev ValueHeapOF : OFunctorPre := ProdOF ValueF HeapOF

example : OFunctorContractive HeapOF := inferInstance
example : OFunctorContractive ValueHeapOF := inferInstance
example {D : Type} [COFE D] : COFE (ValueHeapOF D D) := inferInstance

/-! ### The diagonal instantiations -/

section Cons
variable {V : Type} [COFE V]

/-- The concrete value type at the (diagonal) domain `V`. -/
abbrev Value (V : Type) [COFE V] : Type := ValueF V V

/-- The concrete heap type at the domain `V`. -/
abbrev Heap (V : Type) [COFE V] : Type := GenMap (Later V)

@[match_pattern] abbrev Value.stuck : Value V := ValueF.stuck
@[match_pattern] abbrev Value.fn (f : Later (V -n> V)) : Value V := ValueF.fn f
@[match_pattern] abbrev Value.con (K : ConTag) (ds : List (Later V)) : Value V :=
  ValueF.con K ds

end Cons

/- The `Fix`/fixpoint towers are enormous; keep them opaque so proofs use only
   the bundled non-expansiveness and the equational lemmas above. -/
attribute [irreducible] Trace.fold Trace.unfold Trace.map Trace.bind

end AbsDen
