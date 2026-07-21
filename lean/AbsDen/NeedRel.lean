import AbsDen.HeapAbs
import AbsDen.Productive
import AbsDen.BoundedUsage
import AbsDen.ParametricLR

/-! # The by-need soundness relation, stage 1: the heap invariant

The invariant `HeapInv rec μ` ties the physical heap `μ` to the ghost table:
some table `w` covers exactly `μ`'s domain, `HeapAbsAuth w` is in custody, and
every binding `a ↦ â` backs its cell: one step later, and persistently, the
cell's stored Thunk runs `rec`-below `â` at every future heap satisfying the
invariant. That self-reference sits under the entries' `▷`, so the invariant
is the Banach fixpoint of a contractive operator, separately for every
candidate relation `rec`; the trace relation of stage 2 closes the loop by
taking its own fixpoint with `HeapInv rec` at the returned heaps, which is
well-defined because `HeapInv` is also contractive in `rec`. -/

open Iris Iris.BI Iris.COFE OFE

namespace AbsDen
namespace Need

variable {V : Type}

/-- A backed Thunk: run against any heap satisfying the invariant `S`, the
    trace of `a` is `rec`-below the abstract value `ah`. -/
def Thunk (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V)
    (ah : V) (a : D) : NeedProp V :=
  iprop(∀ μ, S μ -∗ rec ah (D.runAt μ a))

theorem thunk_ne_a {n} (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V)
    (ah : V) {a a' : D} (h : a ≡{n}≡ a') :
    Thunk S rec ah a ≡{n}≡ Thunk S rec ah a' := by
  apply forall_ne; intro μ
  exact wand_ne.ne (OFE.dist_eqv.refl _) ((rec ah).ne.ne ((D.runAt μ).ne.ne h))

theorem thunk_distLater_S {n} {S S' : Heap D -n> NeedProp V}
    (H : OFE.DistLater n S S') (rec : V → Trace VH -n> NeedProp V) (ah : V) (a : D) :
    OFE.DistLater n (Thunk S rec ah a) (Thunk S' rec ah a) := by
  intro m hm
  apply forall_ne; intro μ
  exact wand_ne.ne (H m hm μ) (OFE.dist_eqv.refl _)

theorem thunk_distLater_rec {n} (S : Heap D -n> NeedProp V)
    {rec rec' : V → Trace VH -n> NeedProp V} (H : OFE.DistLater n rec rec')
    (ah : V) (a : D) :
    OFE.DistLater n (Thunk S rec ah a) (Thunk S rec' ah a) := by
  intro m hm
  apply forall_ne; intro μ
  exact wand_ne.ne (OFE.dist_eqv.refl _) (H m hm ah (D.runAt μ a))

/-- One address of the invariant: the table binding and the heap cell exist in
    lockstep, and the cell's stored Thunk is backed by its abstract value, one
    step later and persistently. -/
def EntryRel (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V) :
    Option V → Option (Later D) → NeedProp V
  | none, none => iprop(True)
  | some â, some dl => iprop(▷ □ Thunk S rec â dl.car)
  | _, _ => iprop(False)

theorem entryRel_ne_cell {n} (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) (ô : Option V) {o o' : Option (Later D)}
    (h : o ≡{n}≡ o') : EntryRel S rec ô o ≡{n}≡ EntryRel S rec ô o' := by
  cases o <;> cases o' <;> try exact False.elim h
  · cases ô <;> exact OFE.dist_eqv.refl _
  · cases ô with
    | none => exact OFE.dist_eqv.refl _
    | some â =>
      have hdl := OFE.some_dist_some.mp h
      apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
      intro m hm
      exact intuitionistically_ne.ne (thunk_ne_a S rec â (hdl m hm))

theorem entryRel_distLater_S {n} {S S' : Heap D -n> NeedProp V}
    (H : OFE.DistLater n S S') (rec : V → Trace VH -n> NeedProp V)
    (ô : Option V) (o : Option (Later D)) :
    EntryRel S rec ô o ≡{n}≡ EntryRel S' rec ô o := by
  cases ô <;> cases o <;> try exact OFE.dist_eqv.refl _
  apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
  intro m hm
  exact intuitionistically_ne.ne (OFE.dist_eqv.symm (OFE.dist_eqv.symm
    ((thunk_distLater_S H rec _ _) m hm)))

theorem entryRel_distLater_rec {n} (S : Heap D -n> NeedProp V)
    {rec rec' : V → Trace VH -n> NeedProp V} (H : OFE.DistLater n rec rec')
    (ô : Option V) (o : Option (Later D)) :
    EntryRel S rec ô o ≡{n}≡ EntryRel S rec' ô o := by
  cases ô <;> cases o <;> try exact OFE.dist_eqv.refl _
  apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
  intro m hm
  exact intuitionistically_ne.ne ((thunk_distLater_rec S H _ _) m hm)

/-- The invariant operator: some table `w` covering exactly `μ`'s domain,
    every binding backing its cell. The recursion sits under the entries' `▷`,
    so the operator is contractive. -/
def SBody (rec : V → Trace VH -n> NeedProp V) (Srec : Heap D -n> NeedProp V) :
    Heap D -n> NeedProp V :=
  ⟨fun μ => iprop(∃ w : HeapAbs V, HeapAbsAuth w ∗
      ∀ a : Addr, EntryRel Srec rec (Std.PartialMap.get? w a) (μ.car a)),
   ⟨fun {n μ μ'} h => by
     apply exists_ne; intro w
     refine sep_ne.ne (OFE.dist_eqv.refl _) ?_
     apply forall_ne; intro a
     exact entryRel_ne_cell Srec rec _ (h a)⟩⟩

instance SBody_contractive (rec : V → Trace VH -n> NeedProp V) :
    OFE.Contractive (SBody (V := V) rec) where
  distLater_dist {n Srec Srec'} H := by
    intro μ
    apply exists_ne; intro w
    refine sep_ne.ne (OFE.dist_eqv.refl _) ?_
    apply forall_ne; intro a
    exact entryRel_distLater_S H rec _ _

/-- The heap invariant: the Banach fixpoint of `SBody rec`. -/
def HeapInv (rec : V → Trace VH -n> NeedProp V) : Heap D -n> NeedProp V :=
  (Function.toContractiveHom (SBody rec)).fixpoint

theorem heapInv_unfold (rec : V → Trace VH -n> NeedProp V) :
    HeapInv rec ≡ SBody rec (HeapInv rec) :=
  fixpoint_unfold (Function.toContractiveHom (SBody rec))

/-- The invariant at a heap, unfolded once. -/
theorem heapInv_eq (rec : V → Trace VH -n> NeedProp V) (μ : Heap D) :
    HeapInv rec μ ⊣⊢ iprop(∃ w : HeapAbs V, HeapAbsAuth w ∗
      ∀ a : Addr, EntryRel (HeapInv rec) rec (Std.PartialMap.get? w a) (μ.car a)) :=
  equiv_iff.mp (heapInv_unfold rec μ)

/-- `HeapInv` is contractive in the trace relation: its occurrences also sit
    under the entries' `▷`, which is what lets stage 2 use the invariant at
    returned heaps without guarding it. -/
theorem heapInv_distLater_rec {n} {rec rec' : V → Trace VH -n> NeedProp V}
    (H : OFE.DistLater n rec rec') : HeapInv rec ≡{n}≡ HeapInv rec' := by
  refine OFE.ContractiveHom.fixpoint_ne.ne (fun Srec μ => ?_)
  apply exists_ne; intro w
  refine sep_ne.ne (OFE.dist_eqv.refl _) ?_
  apply forall_ne; intro a
  exact entryRel_distLater_rec Srec H _ _

/-! ## Stage 2: the trace relation

The paper's `βD^μ(d) ⊑ dh` of `fig:abstract-name-need`, defined by guarded
recursion on the trace, one arm per `TraceF` constructor: a returned value is
scored by `SoundVal` and hands back the invariant at the returned heap, a
visible step charges the abstract step against the bound behind an update and
a `▷`, a silent step passes the bound on likewise. The update modality at each
layer is where ghost allocation and the memo write-back re-establish the
invariant. -/

section Stage2

variable [AbstractDomain V] [Lat V]
variable {L : List Var}

/-- A backed Thunk carrying the look-shapes of both sides, persistently: what
    a constructor field stores and a `case` alternative consumes. -/
def LookThunk (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V)
    (ah : V) (a : D) : NeedProp V :=
  iprop(□ Thunk S rec ah a ∧ IsLookShape a ∧ IsLookShape (D := Discrete V) ah)

theorem lookThunk_ne_a {n} (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) (ah : V) {a a' : D} (h : a ≡{n}≡ a') :
    LookThunk S rec ah a ≡{n}≡ LookThunk S rec ah a' :=
  and_ne.ne (intuitionistically_ne.ne (thunk_ne_a S rec ah h))
    (and_ne.ne (IsLookShape_ne h) (OFE.dist_eqv.refl _))

theorem lookThunk_distLater {n} {S S' : Heap D -n> NeedProp V}
    (HS : OFE.DistLater n S S') {rec rec' : V → Trace VH -n> NeedProp V}
    (H : OFE.DistLater n rec rec') (ah : V) (a : D) :
    OFE.DistLater n (LookThunk S rec ah a) (LookThunk S' rec' ah a) := by
  intro m hm
  refine and_ne.ne (intuitionistically_ne.ne ?_) (OFE.dist_eqv.refl _)
  exact ((thunk_distLater_S HS rec ah a) m hm).trans
    ((thunk_distLater_rec S' H ah a) m hm)

/-- A field-list of backed look-thunks, pointwise. -/
def ThunkList (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V) :
    List D → List V → NeedProp V
  | [], [] => iprop(True)
  | a :: xs, ah :: ahs => iprop(LookThunk S rec ah a ∧ ThunkList S rec xs ahs)
  | _, _ => iprop(False)

theorem thunkList_ne_l {n} (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) {xs xs' : List D} (h : xs ≡{n}≡ xs')
    (ahs : List V) : ThunkList S rec xs ahs ≡{n}≡ ThunkList S rec xs' ahs := by
  induction h generalizing ahs with
  | nil => cases ahs <;> exact OFE.dist_eqv.refl _
  | @cons a a' xs xs' ha _ ih =>
    cases ahs with
    | nil => exact OFE.dist_eqv.refl _
    | cons ah ahs => exact and_ne.ne (lookThunk_ne_a S rec ah ha) (ih ahs)

theorem thunkList_distLater {n} {S S' : Heap D -n> NeedProp V}
    (HS : OFE.DistLater n S S') {rec rec' : V → Trace VH -n> NeedProp V}
    (H : OFE.DistLater n rec rec') (xs : List D) (ahs : List V) :
    OFE.DistLater n (ThunkList S rec xs ahs) (ThunkList S' rec' xs ahs) := by
  intro m hm
  induction xs generalizing ahs with
  | nil => cases ahs <;> exact OFE.dist_eqv.refl _
  | cons a xs ih =>
    cases ahs with
    | nil => exact OFE.dist_eqv.refl _
    | cons ah ahs => exact and_ne.ne ((lookThunk_distLater HS H ah a) m hm) (ih ahs)

/-- Structural score of a returned value against the abstract bound `dh`:
    a function asks, one step later and persistently, that backed look-Thunk
    arguments fresh outside `L` go to backed results, and carries the
    parametricity and freshness of its summary; a constructor asks for
    abstract fields its stored thunks are backed by, each fresh outside
    `L`. -/
def SoundVal (L : List Var) (rec : V → Trace VH -n> NeedProp V) (dh : V) :
    Value D -n> NeedProp V :=
  ⟨fun v => match v with
    | .stuck => iprop(⌜AbstractDomain.stuck ≤ dh⌝)
    | .fn f => iprop(∃ (x : Var) (g : V → V) (A : List Var),
        ⌜AbstractDomain.fn x g ≤ dh⌝ ∧
        ⌜x ∉ A ∧ x ∉ L ∧ (∀ y ∈ A, y ∉ L) ∧
          ParametricOn (D := Discrete V) A L g ∧ FreshFn (D := Discrete V) x g⌝ ∧
        ▷ □ (∀ (a : D) (ah : V), ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y ah⌝ →
          LookThunk (HeapInv rec) rec ah a → Thunk (HeapInv rec) rec (g ah) (f.car a)))
    | .con K ds => iprop(∃ dhs : List V, ⌜AbstractDomain.con K dhs ≤ dh⌝ ∧
        ⌜∀ d ∈ dhs, ∀ y, y ∉ L → Fresh (D := Discrete V) y d⌝ ∧
        ▷ ThunkList (HeapInv rec) rec (ds.map (·.car)) dhs),
   ⟨fun {n v v'} h => by
     cases v <;> cases v' <;> try exact False.elim h
     · exact OFE.dist_eqv.refl _
     · have hf : _ ≡{n}≡ _ := h
       apply exists_ne; intro x
       apply exists_ne; intro g
       apply exists_ne; intro A
       refine and_ne.ne (OFE.dist_eqv.refl _) ?_
       refine and_ne.ne (OFE.dist_eqv.refl _) ?_
       apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
       intro m hm
       refine intuitionistically_ne.ne ?_
       apply forall_ne; intro a; apply forall_ne; intro ah
       refine imp_ne.ne (OFE.dist_eqv.refl _) ?_
       refine imp_ne.ne (OFE.dist_eqv.refl _) ?_
       exact thunk_ne_a (HeapInv rec) rec (g ah) ((hf m hm) a)
     · obtain ⟨rfl, hds⟩ := h
       apply exists_ne; intro dhs
       refine and_ne.ne (OFE.dist_eqv.refl _) ?_
       refine and_ne.ne (OFE.dist_eqv.refl _) ?_
       apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
       intro m hm
       exact thunkList_ne_l (HeapInv rec) rec (mapCar_distLater hds m hm) dhs⟩⟩

theorem soundVal_distLater_rec {n} {rec rec' : V → Trace VH -n> NeedProp V}
    (H : OFE.DistLater n rec rec') (dh : V) (v : Value D) :
    SoundVal L rec dh v ≡{n}≡ SoundVal L rec' dh v := by
  have HInv : OFE.DistLater n (HeapInv (V := V) rec) (HeapInv rec') :=
    fun m hm => heapInv_distLater_rec (fun k hk => H k (Nat.lt_trans hk hm))
  cases v with
  | stuck => exact OFE.dist_eqv.refl _
  | fn f =>
    apply exists_ne; intro x
    apply exists_ne; intro g
    apply exists_ne; intro A
    refine and_ne.ne (OFE.dist_eqv.refl _) ?_
    refine and_ne.ne (OFE.dist_eqv.refl _) ?_
    apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
    intro m hm
    refine intuitionistically_ne.ne ?_
    apply forall_ne; intro a; apply forall_ne; intro ah
    refine imp_ne.ne (OFE.dist_eqv.refl _) ?_
    refine imp_ne.ne ((lookThunk_distLater HInv H ah a) m hm) ?_
    exact ((thunk_distLater_S HInv rec (g ah) (f.car a)) m hm).trans
      ((thunk_distLater_rec (HeapInv rec') H (g ah) (f.car a)) m hm)
  | con K ds =>
    apply exists_ne; intro dhs
    refine and_ne.ne (OFE.dist_eqv.refl _) ?_
    refine and_ne.ne (OFE.dist_eqv.refl _) ?_
    apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
    intro m hm
    exact (thunkList_distLater HInv H (ds.map (·.car)) dhs) m hm

/-- One unfolded trace layer scored against the bound `dh`: a `.ret` scores
    its value and hands back the invariant at the returned heap; a visible
    `.step ev` picks a tail bound whose stepped image stays below `dh`, behind
    an update and one step later; a silent `.invis` passes the bound on
    likewise. -/
def RawStep (L : List Var) (rec : V → Trace VH -n> NeedProp V) (dh : V) :
    TraceF VH (Trace VH) (Trace VH) -n> NeedProp V :=
  ⟨fun x => match x with
    | .ret vμ => iprop(SoundVal L rec dh vμ.1 ∗ HeapInv rec vμ.2)
    | .step ev tl => iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧
        |==> ▷ (rec dh' tl.car))
    | .invis tl => iprop(|==> ▷ (rec dh tl.car)),
   ⟨fun {n x x'} h => by
     rcases x with vμ | ⟨ev, tl⟩ | tl <;> rcases x' with vμ' | ⟨ev', tl'⟩ | tl' <;>
       try exact False.elim h
     · exact sep_ne.ne ((SoundVal L rec dh).ne.ne (OFE.dist_fst h))
         ((HeapInv rec).ne.ne (OFE.dist_snd h))
     · obtain ⟨rfl, htl⟩ := h
       apply exists_ne; intro dh'
       refine and_ne.ne (OFE.dist_eqv.refl _) (bupd_ne.ne ?_)
       apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
       intro m hm
       exact (rec dh').ne.ne (htl m hm)
     · refine bupd_ne.ne ?_
       apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
       intro m hm
       exact (rec dh).ne.ne (h m hm)⟩⟩

/-- The Body of the trace relation's fixpoint: score the unfolded layer. Every
    recursive occurrence sits under `▷` or under the entries' `▷` inside
    `HeapInv`, so the operator is contractive. -/
def Body (L : List Var) (rec : V → Trace VH -n> NeedProp V) : V → Trace VH -n> NeedProp V :=
  fun dh => (RawStep L rec dh).comp Trace.unfold

instance : OFE.Contractive (Body (V := V) L) where
  distLater_dist {n rec rec'} H := by
    intro dh t
    show RawStep L rec dh (Trace.unfold t) ≡{n}≡ RawStep L rec' dh (Trace.unfold t)
    rcases Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · exact sep_ne.ne (soundVal_distLater_rec H dh vμ.1)
        (heapInv_distLater_rec H vμ.2)
    · apply exists_ne; intro dh'
      refine and_ne.ne (OFE.dist_eqv.refl _) (bupd_ne.ne ?_)
      apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
      intro m hm
      exact H m hm dh' tl.car
    · refine bupd_ne.ne ?_
      apply Contractive.distLater_dist (f := (BIBase.later : NeedProp V → NeedProp V))
      intro m hm
      exact H m hm dh tl.car

/-- The by-need trace relation: the fixpoint of `Body`. -/
def Rel (L : List Var) : V → Trace VH -n> NeedProp V :=
  (Function.toContractiveHom (Body (V := V) L)).fixpoint

theorem rel_unfold : Rel (V := V) L ≡ Body L (Rel (V := V) L) :=
  fixpoint_unfold (Function.toContractiveHom (Body (V := V) L))

theorem body_ret_eq (rec : V → Trace VH -n> NeedProp V) (dh : V) (vμ : VH) :
    Body L rec dh (Trace.ret vμ) ≡ iprop(SoundVal L rec dh vμ.1 ∗ HeapInv rec vμ.2) :=
  (RawStep L rec dh).ne.eqv (Trace.unfold_fold (.ret vμ))

theorem body_step_eq (rec : V → Trace VH -n> NeedProp V) (dh : V) (ev : Event)
    (tl : Later (Trace VH)) :
    Body L rec dh (Trace.step ev tl) ≡
      iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧ |==> ▷ (rec dh' tl.car)) :=
  (RawStep L rec dh).ne.eqv (Trace.unfold_fold (.step ev tl))

theorem body_invis_eq (rec : V → Trace VH -n> NeedProp V) (dh : V)
    (tl : Later (Trace VH)) :
    Body L rec dh (Trace.invis tl) ≡ iprop(|==> ▷ (rec dh tl.car)) :=
  (RawStep L rec dh).ne.eqv (Trace.unfold_fold (.invis tl))

theorem rel_run (dh : V) (t : Trace VH) : Rel (V := V) L dh t ⊣⊢ Body L (Rel (V := V) L) dh t :=
  equiv_iff.mp (rel_unfold (V := V) dh t)

theorem rel_ret (dh : V) (vμ : VH) :
    Rel (V := V) L dh (Trace.ret vμ) ⊣⊢
      iprop(SoundVal L (Rel (V := V) L) dh vμ.1 ∗ HeapInv (Rel (V := V) L) vμ.2) :=
  (rel_run dh (Trace.ret vμ)).trans (equiv_iff.mp (body_ret_eq (Rel (V := V) L) dh vμ))

theorem rel_step (dh : V) (ev : Event) (tl : Later (Trace VH)) :
    Rel (V := V) L dh (Trace.step ev tl) ⊣⊢
      iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧
        |==> ▷ (Rel (V := V) L dh' tl.car)) :=
  (rel_run dh (Trace.step ev tl)).trans
    (equiv_iff.mp (body_step_eq (Rel (V := V) L) dh ev tl))

theorem rel_invis (dh : V) (tl : Later (Trace VH)) :
    Rel (V := V) L dh (Trace.invis tl) ⊣⊢ iprop(|==> ▷ (Rel (V := V) L dh tl.car)) :=
  (rel_run dh (Trace.invis tl)).trans
    (equiv_iff.mp (body_invis_eq (Rel (V := V) L) dh tl))

/-! ## Reductions of the relation through the by-need combinators -/

/-- The relation at a fixed bound respects trace equivalence. -/
theorem rel_proper (dh : V) {t t' : Trace VH} (h : t ≡ t') :
    Rel (V := V) L dh t ⊣⊢ Rel (V := V) L dh t' :=
  equiv_iff.mp ((Rel (V := V) L dh).ne.eqv h)

theorem rel_ret_run (dh : V) (v : Value D) (μ : Heap D) :
    Rel (V := V) L dh (D.runAt μ (D.ret v)) ⊣⊢
      iprop(SoundVal L (Rel (V := V) L) dh v ∗ HeapInv (Rel (V := V) L) μ) :=
  (rel_proper dh (D.ret_run v μ)).trans (rel_ret dh (v, μ))

theorem rel_step_run (ev : Event) (dh : V) (a : D) (μ : Heap D) :
    Rel (V := V) L dh (D.runAt μ (D.step ev a)) ⊣⊢
      iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧
        |==> ▷ (Rel (V := V) L dh' (D.runAt μ a))) :=
  (rel_proper dh (D.step_run ev a μ)).trans
    (rel_step dh ev (laterMap (D.runAt μ) (Later.next a)))

theorem rel_invis_run (dh : V) (a : D) (μ : Heap D) :
    Rel (V := V) L dh (D.runAt μ (D.invis (Later.next a))) ⊣⊢
      iprop(|==> ▷ (Rel (V := V) L dh (D.runAt μ a))) :=
  (rel_proper dh (D.invis_run (Later.next a) μ)).trans
    (rel_invis dh (laterMap (D.runAt μ) (Later.next a)))

/-! ## Reductions keyed on the unfolded trace layer -/

theorem rel_ret_of_unfold (dh : V) {t : Trace VH} {vμ : VH}
    (hu : Trace.unfold t = .ret vμ) :
    Rel (V := V) L dh t ⊣⊢
      iprop(SoundVal L (Rel (V := V) L) dh vμ.1 ∗ HeapInv (Rel (V := V) L) vμ.2) :=
  (rel_proper dh (Trace.equiv_of_unfold hu).symm).trans (rel_ret dh vμ)

theorem rel_step_of_unfold (dh : V) {t : Trace VH} {ev : Event} {tl : Later (Trace VH)}
    (hu : Trace.unfold t = .step ev tl) :
    Rel (V := V) L dh t ⊣⊢
      iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧
        |==> ▷ (Rel (V := V) L dh' tl.car)) :=
  (rel_proper dh (Trace.equiv_of_unfold hu).symm).trans (rel_step dh ev tl)

theorem rel_invis_of_unfold (dh : V) {t : Trace VH} {tl : Later (Trace VH)}
    (hu : Trace.unfold t = .invis tl) :
    Rel (V := V) L dh t ⊣⊢ iprop(|==> ▷ (Rel (V := V) L dh tl.car)) :=
  (rel_proper dh (Trace.equiv_of_unfold hu).symm).trans (rel_invis dh tl)

theorem rel_bind_ret_of_unfold (k : Value D -n> D) (dh : V) {t : Trace VH} {vμ : VH}
    (hu : Trace.unfold t = .ret vμ) :
    Rel (V := V) L dh (Trace.bind (D.kCont k) t) ⊣⊢
      Rel (V := V) L dh (D.runAt vμ.2 (k vμ.1)) :=
  rel_proper dh (((Trace.bind (D.kCont k)).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
    (Trace.bind_ret (D.kCont k) vμ))

theorem rel_bind_step_of_unfold (k : Value D -n> D) (dh : V) {t : Trace VH} {ev : Event}
    {tl : Later (Trace VH)} (hu : Trace.unfold t = .step ev tl) :
    Rel (V := V) L dh (Trace.bind (D.kCont k) t) ⊣⊢
      iprop(∃ dh' : V, ⌜AbstractDomain.step ev dh' ≤ dh⌝ ∧
        |==> ▷ (Rel (V := V) L dh' (Trace.bind (D.kCont k) tl.car))) :=
  (rel_proper dh (((Trace.bind (D.kCont k)).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
    (Trace.bind_step (D.kCont k) ev tl))).trans
    (rel_step dh ev (laterMap (Trace.bind (D.kCont k)) tl))

theorem rel_bind_invis_of_unfold (k : Value D -n> D) (dh : V) {t : Trace VH}
    {tl : Later (Trace VH)} (hu : Trace.unfold t = .invis tl) :
    Rel (V := V) L dh (Trace.bind (D.kCont k) t) ⊣⊢
      iprop(|==> ▷ (Rel (V := V) L dh (Trace.bind (D.kCont k) tl.car))) :=
  (rel_proper dh (((Trace.bind (D.kCont k)).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
    (Trace.bind_invis (D.kCont k) tl))).trans
    (rel_invis dh (laterMap (Trace.bind (D.kCont k)) tl))

/-! ## The relation on denotations, and the Thunk relation -/

/-- The by-need soundness relation on denotations: at every heap satisfying
    the invariant, the trace of `d` is `Rel`-below the bound. -/
def SoundR (L : List Var) : D -n> Discrete V -n> NeedProp V :=
  ⟨fun d => ⟨fun dh => iprop(∀ μ, HeapInv (Rel (V := V) L) μ -∗ Rel (V := V) L dh (D.runAt μ d)),
      ⟨fun {_ a b} h => by have : a = b := h; subst this; exact OFE.dist_eqv.refl _⟩⟩,
   ⟨fun {_ _ _} h => fun dh => by
      apply forall_ne; intro μ
      exact wand_ne.ne (OFE.dist_eqv.refl _)
        ((Rel (V := V) L dh).ne.ne ((D.runAt μ).ne.ne h))⟩⟩

/-- The Thunk relation a `let` establishes: `a₁` is the fetch of an address
    whose promised abstract value is `a₂`, itself fresh outside the let
    universe `L`. Persistent, so it survives into the entries' backing and
    the function clauses. -/
def IsThunk (L : List Var) : D -n> Discrete V -n> NeedProp V :=
  ⟨fun a₁ => ⟨fun â => iprop((∃ addr : Addr, (a₁ ≡ fetch addr) ∧ FetchAbs addr â) ∧
        ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y â⌝),
      ⟨fun {_ a b} h => by have : a = b := h; subst this; exact OFE.dist_eqv.refl _⟩⟩,
   ⟨fun {n a₁ a₁'} h => fun â => by
      refine and_ne.ne ?_ (OFE.dist_eqv.refl _)
      apply exists_ne; intro addr
      exact and_ne.ne (NonExpansive₂.ne (f := (internalEq : D → D → NeedProp V)) h
        (OFE.dist_eqv.refl _)) (OFE.dist_eqv.refl _)⟩⟩

/-! ## Persistence plumbing for the update modality -/

/-- Persistent propositions become intuitionistic outright. -/
theorem persistent_intuitionistically {P : NeedProp V} [Persistent P] : P ⊢ iprop(□ P) :=
  affinely_intro Persistent.persistent

/-- Persistent context survives into an update. -/
theorem persistent_and_bupd {P Q : NeedProp V} [Persistent P] :
    iprop(P ∧ |==> Q) ⊢ iprop(|==> (P ∧ Q)) :=
  persistent_and_sep_mp.trans (bupd_frame_left.trans (bupd_mono sep_and))

/-- Löb induction at an intuitionistic goal: the hypothesis arrives boxed, so
    it can follow the goal through update modalities. -/
theorem loeb_intuit {X : NeedProp V} (h : iprop(▷ □ X) ⊢ X) : ⊢ (iprop(□ X) : NeedProp V) :=
  (BI.imp_intro (and_elim_r.trans
    (persistent_intuitionistically.trans (intuitionistically_mono h)))).trans loeb

/-- Löb induction under a persistent ambient hypothesis. -/
theorem loeb_intuit_hyp {H X : NeedProp V} [Persistent H]
    (h : iprop(H ∧ ▷ □ X) ⊢ X) : H ⊢ iprop(□ X) := by
  have main : ⊢ (iprop(□ (H → X)) : NeedProp V) := by
    refine loeb_intuit ?_
    refine BI.imp_intro ?_
    refine .trans (and_intro and_elim_r ?_) h
    refine .trans (and_mono .rfl (persistent_intuitionistically.trans later_intro)) ?_
    refine .trans later_and.2 (later_mono ?_)
    refine .trans intuitionistically_and.2 ?_
    exact intuitionistically_mono imp_elim_left
  refine .trans (and_intro (LR.of_empValid main) persistent_intuitionistically) ?_
  refine .trans intuitionistically_and.2 ?_
  exact intuitionistically_mono imp_elim_left

/-! ## Monotonicity of the relation in the abstract bound

A larger bound is a weaker claim: raising `dh` preserves the relation. The
returned-value and visible-step arms weaken pointwise; only the silent `invis`
arm recurses, and its update modality is why the Löb induction runs at a boxed
goal. -/

theorem soundVal_mono_bound [Std.IsPreorder V] (rec : V → Trace VH -n> NeedProp V)
    {dha dhb : V} (hab : dha ≤ dhb) (v : Value D) :
    SoundVal L rec dha v ⊢ SoundVal L rec dhb v := by
  cases v with
  | stuck => exact pure_mono (fun h => Std.IsPreorder.le_trans _ _ _ h hab)
  | fn f =>
    refine exists_elim fun x => ?_
    refine .trans ?_ (exists_intro x)
    refine exists_elim fun g => ?_
    refine .trans ?_ (exists_intro g)
    refine exists_elim fun A => ?_
    refine .trans ?_ (exists_intro A)
    exact and_mono (pure_mono (fun h => Std.IsPreorder.le_trans _ _ _ h hab)) .rfl
  | con K ds =>
    refine exists_elim fun dhs => ?_
    refine .trans ?_ (exists_intro dhs)
    exact and_mono (pure_mono (fun h => Std.IsPreorder.le_trans _ _ _ h hab)) .rfl

theorem rel_mono_bound [Std.IsPreorder V] {dha dhb : V} (hab : dha ≤ dhb) (t : Trace VH) :
    Rel (V := V) L dha t ⊢ Rel (V := V) L dhb t := by
  have main : ⊢ (iprop(□ ∀ (s : Trace VH),
      Rel (V := V) L dha s → Rel (V := V) L dhb s) : NeedProp V) := by
    refine loeb_intuit ?_
    refine forall_intro fun s => imp_intro ?_
    rcases hu : Trace.unfold s with vμ | ⟨ev, tl⟩ | tl
    · refine .trans (and_mono .rfl (rel_ret_of_unfold dha hu).1) ?_
      refine .trans ?_ (rel_ret_of_unfold dhb hu).2
      exact and_elim_r.trans (sep_mono (soundVal_mono_bound _ hab vμ.1) .rfl)
    · refine .trans (and_mono .rfl (rel_step_of_unfold dha hu).1) ?_
      refine .trans ?_ (rel_step_of_unfold dhb hu).2
      refine .trans and_exists_left.1 (exists_elim fun dh' => ?_)
      refine .trans ?_ (exists_intro dh')
      refine and_intro ?_ (and_elim_r.trans and_elim_r)
      exact (and_elim_r.trans and_elim_l).trans
        (pure_mono fun h => Std.IsPreorder.le_trans _ _ _ h hab)
    · refine .trans (and_mono .rfl (rel_invis_of_unfold dha hu).1) ?_
      refine .trans ?_ (rel_invis_of_unfold dhb hu).2
      refine .trans persistent_and_bupd (bupd_mono ?_)
      refine .trans later_and.2 (later_mono ?_)
      exact (and_mono (intuitionistically_elim.trans (forall_elim tl.car)) .rfl).trans
        imp_elim_left
  exact (and_intro ((LR.of_empValid main).trans (intuitionistically_elim.trans
    (forall_elim t))) .rfl).trans imp_elim_left

/-! ## The trace-bind lemma

Binding a by-need continuation `k` after a scrutinee whose trace is
`Rel`-below `dh` produces a trace `Rel`-below `F dh`, provided the bound
transformer `F` is monotone and commutes past a `step`, and the continuation
is sound on every returned value together with the invariant handed back at
the returned heap. Since abstract steps are inflationary, the bound at the
returned value is below the scrutinee's, and the continuation receives that
fact. The Löb induction runs at a boxed goal so the induction hypothesis
follows the trace through the update modalities. -/
theorem rel_bind [Std.IsPreorder V] (Q : NeedProp V) [Persistent Q]
    (k : Value D -n> D) (F : V → V)
    (hFmono : ∀ {dx dy : V}, dx ≤ dy → F dx ≤ F dy)
    (hFstep : ∀ (ev : Event) (dx : V),
      AbstractDomain.step ev (F dx) ≤ F (AbstractDomain.step ev dx))
    (hstep_le : ∀ (ev : Event) (dx : V), dx ≤ AbstractDomain.step ev dx)
    (dh : V)
    (Hk : ∀ (v : Value D) (μ' : Heap D) (dx : V), dx ≤ dh →
      iprop(Q ∧ (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) μ')) ⊢
        Rel (V := V) L (F dx) (D.runAt μ' (k v)))
    (t : Trace VH) :
    iprop(Q ∧ Rel (V := V) L dh t) ⊢ Rel (V := V) L (F dh) (Trace.bind (D.kCont k) t) := by
  have main : ⊢ (iprop(□ ∀ (dx : V) (s : Trace VH),
      (⌜dx ≤ dh⌝ ∧ Q ∧ Rel (V := V) L dx s) →
        Rel (V := V) L (F dx) (Trace.bind (D.kCont k) s)) :
        NeedProp V) := by
    refine loeb_intuit ?_
    refine forall_intro fun dx => forall_intro fun s => imp_intro ?_
    refine pure_elim (dx ≤ dh) (and_elim_r.trans and_elim_l) fun hdx => ?_
    refine .trans (and_mono .rfl and_elim_r) ?_
    rcases hu : Trace.unfold s with vμ | ⟨ev, tl⟩ | tl
    · refine .trans (and_mono .rfl (and_mono .rfl (rel_ret_of_unfold dx hu).1)) ?_
      refine .trans ?_ (rel_bind_ret_of_unfold k (F dx) hu).2
      exact and_elim_r.trans (Hk vμ.1 vμ.2 dx hdx)
    · refine .trans (and_mono .rfl (and_mono .rfl (rel_step_of_unfold dx hu).1)) ?_
      refine .trans ?_ (rel_bind_step_of_unfold k (F dx) hu).2
      refine .trans (and_mono .rfl and_exists_left.1) ?_
      refine .trans and_exists_left.1 (exists_elim fun dx' => ?_)
      refine pure_elim (AbstractDomain.step ev dx' ≤ dx)
        (and_elim_r.trans (and_elim_r.trans and_elim_l)) fun hstep' => ?_
      have hdx' : dx' ≤ dh := Std.IsPreorder.le_trans _ _ _
        (Std.IsPreorder.le_trans _ _ _ (hstep_le ev dx') hstep') hdx
      refine .trans ?_ (exists_intro (F dx'))
      refine and_intro
        (pure_intro (Std.IsPreorder.le_trans _ _ _ (hFstep ev dx') (hFmono hstep'))) ?_
      refine .trans (and_intro
        (and_intro and_elim_l (and_elim_r.trans and_elim_l))
        (and_elim_r.trans (and_elim_r.trans and_elim_r))) ?_
      refine .trans persistent_and_bupd (bupd_mono ?_)
      refine .trans (and_mono (and_mono .rfl later_intro) .rfl) ?_
      refine .trans (and_mono later_and.2 .rfl) ?_
      refine .trans later_and.2 (later_mono ?_)
      refine .trans (and_intro
        (and_elim_l.trans (and_elim_l.trans intuitionistically_elim))
        (and_intro (pure_intro hdx')
          (and_intro (and_elim_l.trans and_elim_r) and_elim_r))) ?_
      exact (and_mono ((forall_elim dx').trans (forall_elim tl.car)) .rfl).trans
        imp_elim_left
    · refine .trans (and_mono .rfl (and_mono .rfl (rel_invis_of_unfold dx hu).1)) ?_
      refine .trans ?_ (rel_bind_invis_of_unfold k (F dx) hu).2
      refine .trans (and_intro
        (and_intro and_elim_l (and_elim_r.trans and_elim_l))
        (and_elim_r.trans and_elim_r)) ?_
      refine .trans persistent_and_bupd (bupd_mono ?_)
      refine .trans (and_mono (and_mono .rfl later_intro) .rfl) ?_
      refine .trans (and_mono later_and.2 .rfl) ?_
      refine .trans later_and.2 (later_mono ?_)
      refine .trans (and_intro
        (and_elim_l.trans (and_elim_l.trans intuitionistically_elim))
        (and_intro (pure_intro hdx)
          (and_intro (and_elim_l.trans and_elim_r) and_elim_r))) ?_
      exact (and_mono ((forall_elim dx).trans (forall_elim tl.car)) .rfl).trans
        imp_elim_left
  exact (and_intro ((LR.of_empValid main).trans (intuitionistically_elim.trans
    ((forall_elim dh).trans (forall_elim t))))
    (and_intro (pure_intro (Std.IsPreorder.le_refl (α := V) dh)) .rfl)).trans imp_elim_left

end Stage2

end Need
end AbsDen
