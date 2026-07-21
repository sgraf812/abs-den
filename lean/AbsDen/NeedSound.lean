import AbsDen.NeedRel
import AbsDen.UsageLaws

/-! # The by-need soundness fields at `NeedProp`

The closure fields of the by-need `LR2` instance over `NeedProp V`: the
relation is `SoundR`, thunks are `IsThunk`, and each field discharges one
`eval` clause against the abstraction laws. The ghost table ties the fields
together: `bind` allocates a promise, `IsThunk_to_R` redeems it against
the heap invariant. -/

open Iris Iris.BI Iris.COFE OFE

namespace AbsDen
namespace Need

variable {V : Type} [AbstractDomain V] [Lat V]
variable {L : List Var}

/-! ## Introduction and elimination for `SoundR` -/

theorem soundR_intro {X : NeedProp V} {d : D} {dh : Discrete V}
    (h : ∀ μ : Heap D,
      iprop(HeapInv (Rel (V := V) L) μ ∗ X) ⊢ Rel (V := V) L dh (D.runAt μ d)) :
    X ⊢ SoundR (V := V) L d dh := by
  show X ⊢ iprop(∀ μ, HeapInv (Rel (V := V) L) μ -∗ Rel (V := V) L dh (D.runAt μ d))
  exact forall_intro fun μ => wand_intro_left (h μ)

theorem soundR_elim (d : D) (dh : Discrete V) (μ : Heap D) :
    iprop(SoundR (V := V) L d dh ∗ HeapInv (Rel (V := V) L) μ) ⊢
      Rel (V := V) L dh (D.runAt μ d) := by
  show iprop((∀ μ, HeapInv (Rel (V := V) L) μ -∗ Rel (V := V) L dh (D.runAt μ d)) ∗
    HeapInv (Rel (V := V) L) μ : NeedProp V) ⊢ _
  exact (sep_mono (forall_elim μ) .rfl).trans wand_elim_left

/-! ## Bridges between the `LR2` vocabulary and the relation's own

`Thunk` at the invariant is definitionally `SoundR`, so a backed look-thunk is
a boxed `IsLookupR` pair and vice versa; the shapes are persistent. -/

instance isLookShape_persistent {D' : Type} [OFE D'] [Domain D'] (a : D') :
    Persistent (IsLookShape a : NeedProp V) :=
  inferInstanceAs (Persistent iprop(∃ (x : Var) (a' : D'), a ≡ Domain.step (.look x) a'))

theorem lookThunk_to_isLookupR (a : D) (ah : Discrete V)
    (hfresh : ∀ y, y ∉ L → Fresh (D := Discrete V) y ah) :
    LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ah a ⊢
      iprop(□ IsLookupR L (SoundR (V := V) L) a ah) := by
  refine .trans ?_ intuitionistically_and.2
  refine and_intro and_elim_l (.trans and_elim_r ?_)
  refine .trans ?_ intuitionistically_and.2
  refine and_intro (and_elim_l.trans intuitionistic_alias) (.trans ?_ intuitionistically_and.2)
  exact and_intro (and_elim_r.trans intuitionistic_alias) (LR.of_empValid_box (pure_intro hfresh))

theorem isLookupR_to_lookThunk (a : D) (ah : Discrete V) :
    iprop(□ IsLookupR L (SoundR (V := V) L) a ah) ⊢
      LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ah a :=
  intuitionistically_and.1.trans (and_mono .rfl (intuitionistically_elim.trans
    (and_intro and_elim_l (and_elim_r.trans and_elim_l))))

theorem conR_to_thunkList : ∀ (ds₁ : List D) (ds₂ : List (Discrete V)),
    Parametric.ConR L (SoundR (V := V) L) ds₁ ds₂ ⊢
      ThunkList (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ds₁ ds₂
  | [], [] => .rfl
  | a₁ :: as₁, a₂ :: as₂ =>
    and_mono (isLookupR_to_lookThunk a₁ a₂) (conR_to_thunkList as₁ as₂)
  | [], _ :: _ => .rfl
  | _ :: _, [] => .rfl

theorem thunkList_to_conR : ∀ (ds₁ : List D) (ds₂ : List (Discrete V)),
    (∀ d ∈ ds₂, ∀ y, y ∉ L → Fresh (D := Discrete V) y d) →
    ThunkList (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ds₁ ds₂ ⊢
      Parametric.ConR L (SoundR (V := V) L) ds₁ ds₂
  | [], [], _ => .rfl
  | a₁ :: as₁, a₂ :: as₂, hfresh =>
    and_mono (lookThunk_to_isLookupR a₁ a₂ (hfresh a₂ (List.mem_cons_self ..)))
      (thunkList_to_conR as₁ as₂ (fun d hd => hfresh d (List.mem_cons_of_mem _ hd)))
  | [], _ :: _, _ => .rfl
  | _ :: _, [], _ => .rfl

/-! ## Redeeming a promise against the invariant -/

/-- A promise at an unallocated cell contradicts the invariant: the table and
    the heap have the same domain. -/
theorem heapInv_lookup_none (μ : Heap D) (addr : Addr) (â : Discrete V)
    (hcell : μ.car addr = none) {Q : NeedProp V} :
    iprop(HeapInv (Rel (V := V) L) μ ∗ FetchAbs addr â) ⊢ Q := by
  refine .trans (sep_mono (heapInv_eq (Rel (V := V) L) μ).1 .rfl) ?_
  refine .trans sep_exists_right.1 (exists_elim fun w => ?_)
  refine pure_elim (Std.PartialMap.get? w addr = some â)
    ((sep_mono sep_elim_left .rfl).trans (heapAbs_lookup w addr â)) fun hget => ?_
  refine .trans (sep_elim_left.trans (sep_elim_right.trans (forall_elim addr))) ?_
  rw [hget, hcell]
  exact false_elim

/-- A promise at an allocated cell is redeemed: the cell's stored thunk is
    backed at the promised value, one step later and persistently. -/
theorem heapInv_lookup_some (μ : Heap D) (addr : Addr) (â : Discrete V) {dl : Later D}
    (hcell : μ.car addr = some dl) :
    iprop(HeapInv (Rel (V := V) L) μ ∗ FetchAbs addr â) ⊢
      iprop(▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) â dl.car) := by
  refine .trans (sep_mono (heapInv_eq (Rel (V := V) L) μ).1 .rfl) ?_
  refine .trans sep_exists_right.1 (exists_elim fun w => ?_)
  refine pure_elim (Std.PartialMap.get? w addr = some â)
    ((sep_mono sep_elim_left .rfl).trans (heapAbs_lookup w addr â)) fun hget => ?_
  refine .trans (sep_elim_left.trans (sep_elim_right.trans (forall_elim addr))) ?_
  rw [hget, hcell]
  exact .rfl

variable [Std.IsPreorder V]

/-- Fetching a promised address runs below the promised abstract value. -/
theorem fetchAbs_to_R (x : Var) (addr : Addr) (â : Discrete V) :
    FetchAbs (V := V) addr â ⊢
      SoundR (V := V) L (Domain.step (.look x) (fetch addr)) (Domain.step (.look x) â) := by
  refine soundR_intro fun μ => ?_
  refine .trans ?_ (rel_step_run (.look x) _ (fetch addr) μ).2
  refine .trans ?_ (exists_intro â)
  refine and_intro (pure_intro (Std.IsPreorder.le_refl (α := V) _)) ?_
  rcases hcell : μ.car addr with _ | dl
  · exact heapInv_lookup_none μ addr â hcell
  · refine .trans ?_
      (bupd_mono (later_mono
        ((rel_proper (V := V) â (fetch_run_some hcell)).trans (rel_invis (V := V) â _)).2))
    refine .trans ?_ bupd_intro
    refine .trans (and_intro (heapInv_lookup_some μ addr â hcell) sep_elim_left) ?_
    refine .trans (and_mono .rfl later_intro) ?_
    refine .trans later_and.2 (later_mono ?_)
    refine .trans ?_ bupd_intro
    refine .trans ?_ later_intro
    refine .trans persistent_and_sep_mp ?_
    exact (sep_mono (intuitionistically_elim.trans (forall_elim μ)) .rfl).trans wand_elim_left

/-- **IsThunk-to-R**: a promised thunk, look-wrapped on both sides, is
    represented: the by-need `look` step is charged against the abstract one
    and the promise is redeemed against the invariant. -/
theorem soundR_isThunk_to_R (x : Var) (a₁ : D) (â : Discrete V) :
    IsThunk (V := V) L a₁ â ⊢
      SoundR (V := V) L (Domain.step (.look x) a₁) (Domain.step (.look x) â) := by
  show iprop((∃ addr : Addr, (a₁ ≡ fetch addr) ∧ FetchAbs addr â) ∧
    ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y â⌝) ⊢ _
  refine and_elim_l.trans ?_
  refine exists_elim fun addr => ?_
  letI : NonExpansive (fun d : D =>
      (SoundR (V := V) L (Domain.step (.look x) d) (Domain.step (.look x) â) : NeedProp V)) :=
    ⟨fun {n d d'} h =>
      ((SoundR (V := V) L).ne.ne ((Domain.step (.look x)).ne.ne h)) (Domain.step (.look x) â)⟩
  refine internalEq.rewrite'
    (fun d => SoundR (V := V) L (Domain.step (.look x) d) (Domain.step (.look x) â))
    (and_elim_l.trans internalEq.symm) ?_
  exact and_elim_r.trans (fetchAbs_to_R x addr â)

/-! ## The value-introducing fields -/

/-- **Stuck**: the by-need stuck value is represented by the abstract stuck
    value at any heap satisfying the invariant. -/
theorem soundR_stuck : ⊢ SoundR (V := V) L Domain.stuck Domain.stuck := by
  refine soundR_intro fun μ => ?_
  refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck μ).2
  exact (sep_mono .rfl (pure_intro (Std.IsPreorder.le_refl _))).trans sep_comm.1

/-- **Con**: a constructor of promised fields is represented by the abstract
    constructor of the promised values, one step later; the promised values'
    freshness rides in the field relation. -/
theorem soundR_con (K : ConTag) (ds₁ : List D) (ds₂ : List (Discrete V)) :
    Parametric.ConR L (SoundR (V := V) L) ds₁ ds₂ ⊢
      SoundR (V := V) L (Domain.con K ds₁) (Domain.con K ds₂) := by
  refine pure_elim (∀ d ∈ ds₂, ∀ y, y ∉ L → Fresh (D := Discrete V) y d)
    (Parametric.ConR_fresh L (SoundR (V := V) L) ds₁ ds₂) fun hfresh => ?_
  refine soundR_intro fun μ => ?_
  refine .trans ?_ (rel_ret_run (V := V) _ (Value.con K (ds₁.map Later.next)) μ).2
  refine sep_comm.1.trans (sep_mono ?_ .rfl)
  refine .trans ?_ (exists_intro ds₂)
  refine and_intro (pure_intro (Std.IsPreorder.le_refl _)) ?_
  refine and_intro (pure_intro hfresh) ?_
  have hmap : (ds₁.map Later.next).map (·.car) = ds₁ := by
    simp only [List.map_map, Function.comp_def, List.map_id']
  rw [hmap]
  exact (conR_to_thunkList ds₁ ds₂).trans later_intro

/-- **Fn**: a function sending promised look-thunks to represented results is
    represented by the abstract function of the promise summaries, whose
    parametricity and freshness arrive as premises from the fundamental
    lemma. The clause is stored boxed, so the hypothesis arrives boxed. -/
theorem soundR_fn (x : Var) (f₁ : D -n> D) (f₂ : Discrete V -n> Discrete V)
    (A : List Var) (hxA : x ∉ A) (hxL : x ∉ L) (hAL : ∀ y ∈ A, y ∉ L)
    (hpar : ParametricOn (D := Discrete V) A L (fun a => Domain.step .app2 (f₂ a)))
    (hff : FreshFn (D := Discrete V) x (fun a => Domain.step .app2 (f₂ a))) :
    iprop(□ Parametric.FnR L (SoundR (V := V) L) f₁ f₂) ⊢
      SoundR (V := V) L (Domain.fn x ((Domain.step .app2).comp f₁))
        (Domain.fn x ((Domain.step .app2).comp f₂)) := by
  refine soundR_intro fun μ => ?_
  refine .trans ?_
    (rel_ret_run (V := V) _ (Value.fn (Later.next ((Domain.step .app2).comp f₁))) μ).2
  refine sep_comm.1.trans (sep_mono ?_ .rfl)
  refine .trans ?_ (exists_intro x)
  refine .trans ?_ (exists_intro (fun ah => AbstractDomain.step (D := V) .app2 (f₂ ah)))
  refine .trans ?_ (exists_intro A)
  refine and_intro (pure_intro (Std.IsPreorder.le_refl _)) ?_
  refine and_intro (pure_intro ⟨hxA, hxL, hAL, hpar, hff⟩) ?_
  refine .trans ?_ later_intro
  refine intuitionistically_intro_intuitionistically ?_
  refine forall_intro fun a => forall_intro fun ah => imp_intro (imp_intro ?_)
  refine pure_elim (∀ y, y ∉ L → Fresh (D := Discrete V) y ah)
    (and_elim_l.trans and_elim_r) fun hfr => ?_
  have happly : iprop((□ Parametric.FnR L (SoundR (V := V) L) f₁ f₂ ∧
      ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y ah⌝) ∧
      LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ah a) ⊢
      SoundR (V := V) L (f₁ a) (f₂ ah) := by
    refine .trans (and_mono (and_elim_l.trans intuitionistically_elim)
      (lookThunk_to_isLookupR a ah hfr)) ?_
    exact (and_mono ((forall_elim a).trans (forall_elim ah)) .rfl).trans imp_elim_left
  show _ ⊢ SoundR (V := V) L (Domain.step .app2 (f₁ a))
    (AbstractDomain.step (D := V) .app2 (f₂ ah))
  refine soundR_intro fun μ' => ?_
  refine .trans ?_ (rel_step_run .app2 _ (f₁ a) μ').2
  refine .trans ?_ (exists_intro (f₂ ah))
  refine and_intro (pure_intro (Std.IsPreorder.le_refl _)) ?_
  refine .trans ?_ bupd_intro
  refine .trans ?_ later_intro
  exact (sep_mono .rfl happly).trans (sep_comm.1.trans (soundR_elim _ _ μ'))

/-! ## The scrutinee-binding fields -/

variable [ChainComplete V]

instance lookThunk_persistent (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) (ah : V) (a : D) :
    Persistent (LookThunk S rec ah a) :=
  inferInstanceAs (Persistent iprop(□ Thunk S rec ah a ∧
    IsLookShape a ∧ IsLookShape (D := Discrete V) ah))

/-- **App**: applying a represented function to a promised look-thunk is
    represented by the abstract application, wrapped in the by-need `app1`
    step. The scrutinee's trace is bound with the by-need `applyCont`; the
    trace-bind lemma pushes `apply · da₂` past it, charging interior steps by
    `Step-App` and closing the returned value by `Beta-App`/`Stuck-App`. -/
theorem soundR_app (laws : AbstractionLaws V) (dv₁ da₁ : D) (dv₂ da₂ : Discrete V) :
    iprop(SoundR (V := V) L dv₁ dv₂ ∧ □ IsLookupR L (SoundR (V := V) L) da₁ da₂) ⊢
      SoundR (V := V) L (Domain.step .app1 (Domain.apply dv₁ da₁))
        (Domain.step .app1 (Domain.apply dv₂ da₂)) := by
  have Hk : ∀ (v : Value D) (μ' : Heap D) (dx : V), dx ≤ dv₂ →
      iprop((iprop(□ IsLookupR L (SoundR (V := V) L) da₁ da₂) : NeedProp V) ∧
          (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) μ')) ⊢
        Rel (V := V) L (AbstractDomain.apply (D := V) dx da₂)
          (D.runAt μ' (D.applyCont da₁ v)) := by
    intro v μ' dx _hdx
    cases v with
    | stuck =>
      refine .trans and_elim_r ?_
      refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck μ').2
      refine sep_mono (pure_mono fun hstuck => ?_) .rfl
      exact Std.IsPreorder.le_trans _ _ _ (laws.stuck_apply_stuck da₂)
        (laws.mono_apply hstuck (Std.IsPreorder.le_refl (α := V) da₂))
    | fn f =>
      refine .trans ?_ (rel_invis_run (V := V) _ (f.car da₁) μ').2
      refine .trans (and_mono .rfl sep_exists_right.1) ?_
      refine .trans and_exists_left.1 (exists_elim fun y => ?_)
      refine .trans (and_mono .rfl sep_exists_right.1) ?_
      refine .trans and_exists_left.1 (exists_elim fun g => ?_)
      refine .trans (and_mono .rfl sep_exists_right.1) ?_
      refine .trans and_exists_left.1 (exists_elim fun A => ?_)
      refine pure_elim (AbstractDomain.fn (D := V) y g ≤ dx)
        (and_elim_r.trans (sep_elim_left.trans and_elim_l)) fun hfn => ?_
      refine pure_elim (y ∉ A ∧ y ∉ L ∧ (∀ z ∈ A, z ∉ L) ∧
          ParametricOn (D := Discrete V) A L g ∧ FreshFn (D := Discrete V) y g)
        (and_elim_r.trans (sep_elim_left.trans (and_elim_r.trans and_elim_l)))
        fun hpack => ?_
      obtain ⟨hyA, hyL, hAL, hpar, hff⟩ := hpack
      refine pure_elim (∀ z, z ∉ L → Fresh (D := Discrete V) z da₂)
        (and_elim_l.trans (intuitionistically_elim.trans
          (IsLookupR_fresh L (SoundR (V := V) L) da₁ da₂))) fun hda₂ => ?_
      -- `Beta-App`: the pure conjuncts stored by the fundamental lemma supply
      -- the parametricity and freshness premises
      have hbeta : g da₂ ⊑ AbstractDomain.apply (AbstractDomain.fn (D := V) y g) da₂ :=
        laws.apply_fn y g da₂ A L hyA hyL hpar hff (hda₂ y hyL)
          (fun z hz => hda₂ z (hAL z hz))
      refine .trans ?_ bupd_intro
      refine .trans (and_mono (isLookupR_to_lookThunk da₁ da₂)
        (sep_mono (and_elim_r.trans and_elim_r) later_intro)) ?_
      refine .trans (and_mono later_intro later_sep.2) ?_
      refine .trans later_and.2 (later_mono ?_)
      refine .trans ?_ (rel_mono_bound (Std.IsPreorder.le_trans _ _ _
        hbeta (laws.mono_apply hfn (Std.IsPreorder.le_refl (α := V) da₂))) _)
      refine .trans persistent_and_sep_mp ?_
      refine .trans sep_assoc.2 ?_
      have happ : iprop(LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) da₂ da₁ ∗
          □ (∀ (a : D) (ah : V), ⌜∀ z, z ∉ L → Fresh (D := Discrete V) z ah⌝ →
            LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ah a →
              Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) (g ah) (f.car a))) ⊢
          SoundR (V := V) L (f.car da₁) (g da₂) := by
        refine .trans sep_and ?_
        refine .trans (and_intro
          (and_elim_r.trans (intuitionistically_elim.trans
            ((forall_elim da₁).trans (forall_elim da₂))))
          and_elim_l) ?_
        refine .trans (and_mono
          ((and_intro .rfl (pure_intro hda₂)).trans imp_elim_left) .rfl) ?_
        exact imp_elim_left
      exact (sep_mono happ .rfl).trans (soundR_elim _ _ μ')
    | con K ds =>
      refine .trans and_elim_r ?_
      refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck μ').2
      refine .trans sep_exists_right.1 (exists_elim fun dhs => ?_)
      refine pure_elim (AbstractDomain.con (D := V) K dhs ≤ dx)
        (sep_elim_left.trans and_elim_l) fun hcon => ?_
      refine sep_mono (pure_intro ?_) .rfl
      exact Std.IsPreorder.le_trans _ _ _ (laws.stuck_apply_con K dhs da₂)
        (laws.mono_apply hcon (Std.IsPreorder.le_refl (α := V) da₂))
  refine soundR_intro fun μ => ?_
  refine .trans ?_ (rel_step_run .app1 _ (D.bind dv₁ (D.applyCont da₁)) μ).2
  refine .trans ?_ (exists_intro (AbstractDomain.apply (D := V) dv₂ da₂))
  refine and_intro (pure_intro (Std.IsPreorder.le_refl (α := V) _)) ?_
  refine .trans ?_ bupd_intro
  refine .trans ?_ later_intro
  refine .trans ?_ (rel_proper (V := V) _ (D.bind_run dv₁ (D.applyCont da₁) μ)).2
  refine .trans ?_ (rel_bind (V := V) iprop(□ IsLookupR L (SoundR (V := V) L) da₁ da₂)
    (D.applyCont da₁) (fun d => AbstractDomain.apply (D := V) d da₂)
    (fun {dx dy} h => laws.mono_apply h (Std.IsPreorder.le_refl (α := V) da₂))
    (fun ev dx => laws.step_apply ev dx da₂)
    (fun ev dx => laws.step_inc ev dx) dv₂ Hk (D.runAt μ dv₁))
  refine and_intro (sep_elim_right.trans and_elim_r) ?_
  exact (sep_mono .rfl and_elim_l).trans (sep_comm.1.trans (soundR_elim _ _ μ))

/-! ## The Case field -/

omit [AbstractDomain V] [Lat V] [Std.IsPreorder V] [ChainComplete V] in
/-- Persistent left conjuncts associate into a separating context. -/
theorem persistent_and_sep_assoc {P Q R : NeedProp V} [Persistent P] :
    iprop(P ∧ (Q ∗ R)) ⊢ iprop((P ∧ Q) ∗ R) :=
  persistent_and_sep_mp.trans (sep_assoc.2.trans (sep_mono sep_and .rfl))

omit [Lat V] [Std.IsPreorder V] [ChainComplete V] in
theorem thunkList_length (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) :
    ∀ (xs : List D) (ahs : List V),
      ThunkList S rec xs ahs ⊢ (⌜xs.length = ahs.length⌝ : NeedProp V)
  | [], [] => pure_intro rfl
  | _ :: xs, _ :: ahs =>
      (and_elim_r.trans (thunkList_length S rec xs ahs)).trans
        (pure_mono fun h => by simp only [List.length_cons, h])
  | [], _ :: _ => false_elim
  | _ :: _, [] => false_elim

set_option maxHeartbeats 400000 in
/-- Selecting on a represented constructor value: the by-need `selectCont`
    dispatches to the first matching alternative (or gets stuck), and the
    abstract `select` of the constructor's summary bounds it. The matching
    branch is closed by `Beta-Sel`, a missing constructor by `Stuck-Sel`; the
    alternatives' boxed `AltsR` relation supplies the branch soundness and the
    tag correspondence, and the invariant is threaded through to the branch. -/
theorem selectCont_con_sound (laws : AbstractionLaws V) (K : ConTag) (dx : V) (mu : Heap D)
    (ds : List (Later D)) (dhs : List V)
    (alts₁ : List (ConTag × Nat × (List D -n> D)))
    (alts₂ : List (ConTag × Nat × (List (Discrete V) -n> Discrete V)))
    (hAlts : ∀ p ∈ Parametric.stepAlts alts₂, ∃ A, (∀ y ∈ A, y ∉ L) ∧
      ParametricAltOn (D := Discrete V) A L (fun es => p.2.2 es)) :
    iprop(□ Parametric.AltsR L (SoundR (V := V) L) alts₁ alts₂ ∧
        ((⌜AbstractDomain.con (D := V) K dhs ≤ dx⌝ ∧
          ⌜∀ d ∈ dhs, ∀ y, y ∉ L → Fresh (D := Discrete V) y d⌝ ∧
          ▷ ThunkList (HeapInv (Rel (V := V) L)) (Rel (V := V) L) (ds.map (·.car)) dhs) ∗
         HeapInv (Rel (V := V) L) mu)) ⊢
      Rel (V := V) L (AbstractDomain.select (D := V) dx
          ((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f))))
        (D.runAt mu (D.selectCont (Parametric.stepAlts alts₁) (Value.con K ds))) := by
  refine pure_elim (alts₁.length = alts₂.length ∧
      ∀ p ∈ alts₁.zip alts₂, p.1.1 = p.2.1 ∧ p.1.2.1 = p.2.2.1)
    (and_elim_l.trans (intuitionistically_elim.trans
      (Parametric.AltsR_pure L (SoundR (V := V) L) alts₁ alts₂))) fun hpure => ?_
  obtain ⟨hlen, htags⟩ := hpure
  refine pure_elim (AbstractDomain.con (D := V) K dhs ≤ dx)
    (and_elim_r.trans (sep_elim_left.trans and_elim_l)) fun hcon => ?_
  refine pure_elim (∀ d ∈ dhs, ∀ y, y ∉ L → Fresh (D := Discrete V) y d)
    (and_elim_r.trans (sep_elim_left.trans (and_elim_r.trans and_elim_l))) fun hdfr => ?_
  rw [D.selectCont_stored]
  rcases hfind : (Parametric.stepAlts alts₁).find? (·.1 == K) with _ | p
  all_goals rw [hfind]
  · -- no alternative matches: the by-need side is a stuck return, and `K` is
    -- absent from the abstract alternatives too, so `Stuck-Sel` closes
    have h1 : ∀ q ∈ alts₁, q.1 ≠ K := by
      intro q hq hK
      have hnone := List.find?_eq_none.mp hfind _ (by
        simp only [Parametric.stepAlts, List.mem_map]
        exact ⟨q, hq, rfl⟩)
      simp [hK] at hnone
    have h2 : ∀ q₂ ∈ (Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f)),
        q₂.1 ≠ K := by
      intro q₂ hq₂ hK
      simp only [Parametric.stepAlts, List.map_map, List.mem_map] at hq₂
      obtain ⟨q, hq, rfl⟩ := hq₂
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      have hj₁ : j < alts₁.length := hlen ▸ hj
      have hpair : (alts₁[j]'hj₁, alts₂[j]'hj) ∈ alts₁.zip alts₂ :=
        List.mem_iff_getElem.mpr
          ⟨j, by rw [List.length_zip]; omega, by simp [List.getElem_zip]⟩
      exact h1 _ (List.getElem_mem hj₁) ((htags _ hpair).1.trans hK)
    refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck mu).2
    exact and_elim_r.trans (sep_mono (pure_intro (Std.IsPreorder.le_trans _ _ _
      (laws.stuck_select_con K dhs _ h2) (laws.mono_select _ hcon))) .rfl)
  · -- the first matching alternative runs; pair it positionally with its
    -- abstract counterpart and close by `Beta-Sel`
    have hpK : (p.1 == K) = true := by
      have h := List.find?_some hfind
      exact h
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfind)
    have hi₁ : i < alts₁.length := by
      simpa only [Parametric.stepAlts, List.length_map] using hi
    have hi₂ : i < alts₂.length := hlen ▸ hi₁
    have hpair : (alts₁[i]'hi₁, alts₂[i]'hi₂) ∈ alts₁.zip alts₂ :=
      List.mem_iff_getElem.mpr
        ⟨i, by rw [List.length_zip]; omega, by simp [List.getElem_zip]⟩
    have hK₁ : (alts₁[i]'hi₁).1 = K := by
      have : ((Parametric.stepAlts alts₁)[i]'hi).1 = K := by
        rw [hpi]; exact beq_iff_eq.mp hpK
      simpa only [Parametric.stepAlts, List.getElem_map] using this
    have harity : (alts₁[i]'hi₁).2.1 = (alts₂[i]'hi₂).2.1 := (htags _ hpair).2
    have hp22 : ∀ es, p.2.2 es
        = if es.length = (alts₁[i]'hi₁).2.1
          then Domain.step .case2 ((alts₁[i]'hi₁).2.2 es) else Domain.stuck := by
      intro es
      rw [← hpi]
      simp only [Parametric.stepAlts, List.getElem_map]
    have hi₂' : i < ((Parametric.stepAlts alts₂).map
        (fun p => (p.1, p.2.1, p.2.2.f))).length := by
      simpa only [Parametric.stepAlts, List.length_map] using hi₂
    have hK₂' : (((Parametric.stepAlts alts₂).map
        (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').1 = K := by
      simp only [Parametric.stepAlts, List.getElem_map]
      exact (htags _ hpair).1.symm.trans hK₁
    have hmem₂ : (K,
        (((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.1,
        (((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.2)
        ∈ (Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f)) := by
      rw [← hK₂']
      exact List.getElem_mem hi₂'
    have hget : (alts₁.zip alts₂)[i]? = some (alts₁[i]'hi₁, alts₂[i]'hi₂) :=
      List.getElem?_eq_some_iff.mpr ⟨by rw [List.length_zip]; omega,
        by simp [List.getElem_zip]⟩
    have hclause : iprop(□ Parametric.AltsR L (SoundR (V := V) L) alts₁ alts₂) ⊢
        iprop(∀ ds₁ ds₂, Parametric.ConR L (SoundR (V := V) L) ds₁ ds₂ →
          SoundR (V := V) L ((alts₁[i]'hi₁).2.2 ds₁) ((alts₂[i]'hi₂).2.2 ds₂)) :=
      intuitionistically_elim.trans (and_elim_r.trans
        ((BigAndL.bigAndL_lookup hget).trans and_elim_r))
    dsimp only [Option.elim]
    refine .trans ?_ (rel_invis_run (V := V) _ _ mu).2
    refine .trans ?_ bupd_intro
    refine .trans (and_mono .rfl (sep_mono (and_elim_r.trans and_elim_r) .rfl)) ?_
    refine .trans persistent_and_sep_assoc ?_
    refine .trans (sep_mono (and_mono later_intro .rfl) later_intro) ?_
    refine .trans (sep_mono later_and.2 .rfl) ?_
    refine .trans later_sep.2 (later_mono ?_)
    refine pure_elim ((ds.map (·.car)).length = dhs.length)
      (sep_elim_left.trans (and_elim_r.trans (thunkList_length _ _ _ _))) fun hdlen => ?_
    rw [hp22]
    by_cases hlen' : (ds.map (·.car)).length = (alts₁[i]'hi₁).2.1
    · -- matching arity on both sides: `Beta-Sel` bounds the stepped branch,
      -- with the branch parametricity from the alternatives' premise and the
      -- field freshness from the scrutinee's stored value
      rw [if_pos hlen']
      have hiₛ : i < (Parametric.stepAlts alts₂).length := by
        simpa only [Parametric.stepAlts, List.length_map] using hi₂
      have harity₂ : (((Parametric.stepAlts alts₂).map
          (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.1 = (alts₂[i]'hi₂).2.1 := by
        simp only [Parametric.stepAlts, List.getElem_map]
      have hdhslen : dhs.length = (alts₂[i]'hi₂).2.1 :=
        (hdlen.symm.trans hlen').trans harity
      obtain ⟨A, hAL, hparA⟩ := hAlts ((Parametric.stepAlts alts₂)[i]'hiₛ)
        (List.getElem_mem hiₛ)
      have hpar' : ParametricAltOn (D := Discrete V) A L
          ((((Parametric.stepAlts alts₂).map
            (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.2) := by
        simp only [Parametric.stepAlts, List.getElem_map]
        simp only [Parametric.stepAlts, List.getElem_map] at hparA
        exact hparA
      have hp22' : ∀ es : List (Discrete V),
          ((((Parametric.stepAlts alts₂).map
            (fun p : ConTag × Nat × (List (Discrete V) -n> Discrete V) =>
              (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.2) es
          = if es.length = (alts₂[i]'hi₂).2.1
            then AbstractDomain.step (D := V) .case2 ((alts₂[i]'hi₂).2.2 es)
            else AbstractDomain.stuck (D := V) := by
        intro es
        simp only [Parametric.stepAlts, List.getElem_map]
        rfl
      have hbr : AbstractDomain.step (D := V) .case2 ((alts₂[i]'hi₂).2.2 dhs)
          ⊑ AbstractDomain.select (D := V) (AbstractDomain.con (D := V) K dhs)
            ((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f))) := by
        have h := laws.select_con K _ _ dhs _ A L hpar'
          (fun y hy d hd => hdfr d hd y (hAL y hy)) hmem₂
          (hdhslen.trans harity₂.symm)
        rw [hp22'] at h
        split at h
        · exact h
        · next hne => exact absurd hdhslen hne
      refine .trans ?_ (rel_step_run (V := V) .case2 _ _ mu).2
      refine .trans ?_ (exists_intro ((alts₂[i]'hi₂).2.2 dhs))
      refine and_intro (pure_intro (Std.IsPreorder.le_trans _ _ _ hbr
        (laws.mono_select _ hcon))) ?_
      refine .trans ?_ bupd_intro
      refine .trans ?_ later_intro
      refine .trans (sep_mono ?_ .rfl) (soundR_elim _ _ mu)
      refine .trans (and_intro
        (and_elim_l.trans (hclause.trans
          ((forall_elim (ds.map (·.car))).trans (forall_elim dhs))))
        (and_elim_r.trans (thunkList_to_conR _ _ hdfr))) ?_
      exact imp_elim_left
    · -- arity mismatch on both sides: the branch is stuck, and
      -- `Stuck-Sel-Arity` bounds it
      rw [if_neg hlen']
      have harity₂ : (((Parametric.stepAlts alts₂).map
          (fun p => (p.1, p.2.1, p.2.2.f)))[i]'hi₂').2.1 = (alts₂[i]'hi₂).2.1 := by
        simp only [Parametric.stepAlts, List.getElem_map]
      have hbr := laws.stuck_select_arity K _ _ dhs _ hmem₂
        (fun h => hlen' ((hdlen.trans (harity₂.symm.trans h).symm).trans harity.symm))
      refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck mu).2
      exact sep_mono (pure_intro (Std.IsPreorder.le_trans _ _ _ hbr
        (laws.mono_select _ hcon))) .rfl

/-- **Case**: selecting on a represented scrutinee with `AltsR`-related
    alternatives is represented by the abstract selection, wrapped in the
    by-need `case1` step. The scrutinee's trace is bound with the by-need
    `selectCont`; the trace-bind lemma pushes `select · alts₂` past it,
    charging interior steps by `Step-Sel` and closing the returned value by
    `selectCont_con_sound` or the `Stuck-Sel` laws. -/
theorem soundR_case (laws : AbstractionLaws V) (dv₁ : D) (dv₂ : Discrete V)
    (alts₁ : List (ConTag × Nat × (List D -n> D)))
    (alts₂ : List (ConTag × Nat × (List (Discrete V) -n> Discrete V)))
    (hAlts : ∀ p ∈ Parametric.stepAlts alts₂, ∃ A, (∀ y ∈ A, y ∉ L) ∧
      ParametricAltOn (D := Discrete V) A L (fun es => p.2.2 es)) :
    iprop(SoundR (V := V) L dv₁ dv₂ ∧ □ Parametric.AltsR L (SoundR (V := V) L) alts₁ alts₂) ⊢
      SoundR (V := V) L
        (Domain.step .case1 (Domain.select dv₁ (Parametric.stepAlts alts₁)))
        (Domain.step .case1 (Domain.select dv₂ (Parametric.stepAlts alts₂))) := by
  have Hk : ∀ (v : Value D) (μ' : Heap D) (dx : V), dx ≤ dv₂ →
      iprop((iprop(□ Parametric.AltsR L (SoundR (V := V) L) alts₁ alts₂) : NeedProp V) ∧
          (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) μ')) ⊢
        Rel (V := V) L (AbstractDomain.select (D := V) dx
            ((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f))))
          (D.runAt μ' (D.selectCont (Parametric.stepAlts alts₁) v)) := by
    intro v μ' dx _hdx
    cases v with
    | stuck =>
      refine .trans and_elim_r ?_
      refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck μ').2
      refine sep_mono (pure_mono fun hstuck => ?_) .rfl
      exact Std.IsPreorder.le_trans _ _ _
        (laws.stuck_select_stuck _) (laws.mono_select _ hstuck)
    | fn f =>
      refine .trans and_elim_r ?_
      refine .trans ?_ (rel_ret_run (V := V) _ Value.stuck μ').2
      refine .trans sep_exists_right.1 (exists_elim fun y => ?_)
      refine .trans sep_exists_right.1 (exists_elim fun g => ?_)
      refine .trans sep_exists_right.1 (exists_elim fun A => ?_)
      refine pure_elim (AbstractDomain.fn (D := V) y g ≤ dx)
        (sep_elim_left.trans and_elim_l) fun hfn => ?_
      refine sep_mono (pure_intro ?_) .rfl
      exact Std.IsPreorder.le_trans _ _ _
        (laws.stuck_select_fn y g _) (laws.mono_select _ hfn)
    | con K ds =>
      refine .trans (and_mono .rfl sep_exists_right.1) ?_
      refine .trans and_exists_left.1 (exists_elim fun dhs => ?_)
      exact selectCont_con_sound laws K dx μ' ds dhs alts₁ alts₂ hAlts
  refine soundR_intro fun μ => ?_
  refine .trans ?_ (rel_step_run .case1 _
    (D.bind dv₁ (D.selectCont (Parametric.stepAlts alts₁))) μ).2
  refine .trans ?_ (exists_intro (AbstractDomain.select (D := V) dv₂
    ((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f)))))
  refine and_intro (pure_intro (Std.IsPreorder.le_refl (α := V) _)) ?_
  refine .trans ?_ bupd_intro
  refine .trans ?_ later_intro
  refine .trans ?_ (rel_proper (V := V) _
    (D.bind_run dv₁ (D.selectCont (Parametric.stepAlts alts₁)) μ)).2
  refine .trans ?_ (rel_bind (V := V)
    iprop(□ Parametric.AltsR L (SoundR (V := V) L) alts₁ alts₂)
    (D.selectCont (Parametric.stepAlts alts₁))
    (fun d => AbstractDomain.select (D := V) d
      ((Parametric.stepAlts alts₂).map (fun p => (p.1, p.2.1, p.2.2.f))))
    (fun {dx dy} h => laws.mono_select _ h)
    (fun ev dx => laws.step_select ev dx _)
    (fun ev dx => laws.step_inc ev dx) dv₂ Hk (D.runAt μ dv₁))
  refine and_intro (sep_elim_right.trans and_elim_r) ?_
  exact (sep_mono .rfl and_elim_l).trans (sep_comm.1.trans (soundR_elim _ _ μ))

/-! ## The Bind field

The by-need `let` allocates a fresh cell holding the memoized rhs. The ghost
step promises the abstract pre-fixpoint `d₁` of the rhs to the fresh address;
the memoized rhs backs the promise: forcing it runs the rhs below `rhs₂ d₁`,
which the pre-fixpoint property caps at `d₁`, and the `update` write-back
re-establishes the invariant with a memoized value cell, itself backed by a
Löb fixpoint. -/

instance entryRel_persistent (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) :
    ∀ (ô : Option V) (o : Option (Later D)), Persistent (EntryRel S rec ô o)
  | none, none => inferInstanceAs (Persistent iprop(⌜True⌝))
  | some â, some dl => inferInstanceAs (Persistent iprop(▷ □ Thunk S rec â dl.car))
  | none, some _ => inferInstanceAs (Persistent iprop(⌜False⌝))
  | some _, none => inferInstanceAs (Persistent iprop(⌜False⌝))

instance thunkList_persistent (S : Heap D -n> NeedProp V)
    (rec : V → Trace VH -n> NeedProp V) :
    ∀ (xs : List D) (ahs : List V), Persistent (ThunkList S rec xs ahs)
  | [], [] => inferInstanceAs (Persistent iprop(⌜True⌝))
  | a :: xs, ah :: ahs =>
    have := thunkList_persistent S rec xs ahs
    inferInstanceAs (Persistent iprop(LookThunk S rec ah a ∧ ThunkList S rec xs ahs))
  | [], _ :: _ => inferInstanceAs (Persistent iprop(⌜False⌝))
  | _ :: _, [] => inferInstanceAs (Persistent iprop(⌜False⌝))

instance soundVal_persistent (dh : V) (v : Value D) :
    Persistent (SoundVal L (Rel (V := V) L) dh v) := by
  cases v with
  | stuck => exact inferInstanceAs (Persistent iprop(⌜AbstractDomain.stuck ≤ dh⌝))
  | fn f =>
    exact inferInstanceAs (Persistent iprop(∃ (x : Var) (g : V → V) (A : List Var),
      ⌜AbstractDomain.fn x g ≤ dh⌝ ∧
      ⌜x ∉ A ∧ x ∉ L ∧ (∀ y ∈ A, y ∉ L) ∧
        ParametricOn (D := Discrete V) A L g ∧ FreshFn (D := Discrete V) x g⌝ ∧
      ▷ □ (∀ (a : D) (ah : V), ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y ah⌝ →
        LookThunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) ah a →
          Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) (g ah) (f.car a))))
  | con K ds =>
    exact inferInstanceAs (Persistent iprop(∃ dhs : List V,
      ⌜AbstractDomain.con K dhs ≤ dh⌝ ∧
      ⌜∀ d ∈ dhs, ∀ y, y ∉ L → Fresh (D := Discrete V) y d⌝ ∧
      ▷ ThunkList (HeapInv (Rel (V := V) L)) (Rel (V := V) L) (ds.map (·.car)) dhs))

instance isThunk_persistent (a₁ : D) (â : Discrete V) :
    Persistent (IsThunk (V := V) L a₁ â) :=
  inferInstanceAs (Persistent iprop((∃ addr : Addr, (a₁ ≡ fetch addr) ∧ FetchAbs addr â) ∧
    ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y â⌝))

/-- A promise fresh outside the let universe names its own fetch. -/
theorem fetchAbs_to_isThunk (a : Addr) (d₁ : Discrete V)
    (hfresh : ∀ y, y ∉ L → Fresh (D := Discrete V) y d₁) :
    FetchAbs (V := V) a d₁ ⊢ IsThunk (V := V) L (fetch a) d₁ := by
  show _ ⊢ iprop((∃ addr : Addr, (fetch a ≡ fetch addr) ∧ FetchAbs addr d₁) ∧
    ⌜∀ y, y ∉ L → Fresh (D := Discrete V) y d₁⌝)
  refine and_intro (.trans ?_ (exists_intro a)) (pure_intro hfresh)
  exact and_intro internalEq.refl .rfl

/-- Rewriting a promised cell preserves the invariant, provided the new
    content is backed at the promise. -/
theorem heapInv_update (ν : Heap D) (a : Addr) (d₁ : Discrete V) (dl : Later D) :
    iprop((HeapInv (Rel (V := V) L) ν ∗ FetchAbs a d₁) ∧
        ▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁ dl.car) ⊢
      HeapInv (Rel (V := V) L) (Heap.set ν a dl) := by
  refine .trans (and_mono (sep_mono (heapInv_eq (Rel (V := V) L) ν).1 .rfl) .rfl) ?_
  refine .trans (and_mono sep_exists_right.1 .rfl) ?_
  refine .trans and_exists_right.1 (exists_elim fun w => ?_)
  refine pure_elim (Std.PartialMap.get? w a = some d₁)
    (and_elim_l.trans ((sep_mono sep_elim_left .rfl).trans (heapAbs_lookup w a d₁)))
    fun hget => ?_
  refine .trans ?_ (heapInv_eq (Rel (V := V) L) (Heap.set ν a dl)).2
  refine .trans ?_ (exists_intro w)
  have hEnt : iprop(((HeapAbsAuth w ∗ (∀ b, EntryRel (HeapInv (Rel (V := V) L))
        (Rel (V := V) L) (Std.PartialMap.get? w b) (ν.car b))) ∗ FetchAbs a d₁) ∧
        ▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁ dl.car) ⊢
      iprop(∀ b, EntryRel (HeapInv (Rel (V := V) L)) (Rel (V := V) L)
        (Std.PartialMap.get? w b) ((Heap.set ν a dl).car b)) := by
    refine forall_intro fun b => ?_
    by_cases hb : a = b
    · rw [Heap.set_get, if_pos hb, ← hb, hget]
      exact and_elim_r
    · rw [Heap.set_get, if_neg hb]
      exact and_elim_l.trans (sep_elim_left.trans (sep_elim_right.trans (forall_elim b)))
  refine .trans (and_intro .rfl hEnt) ?_
  refine .trans persistent_and_sep_mp ?_
  exact sep_mono (and_elim_l.trans (sep_elim_left.trans sep_elim_left)) .rfl

/-- Allocating a fresh cell with a fresh promise: the ghost step extends the
    table, and the invariant follows once the content is backed at the
    promise it just received. -/
theorem heapInv_alloc (μ : Heap D) (a : Addr) (d₁ : Discrete V) (dl : Later D)
    (hcell : μ.car a = none) :
    iprop(HeapInv (Rel (V := V) L) μ ∗
        (FetchAbs a d₁ -∗ ▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁ dl.car)) ⊢
      iprop(|==> (HeapInv (Rel (V := V) L) (Heap.set μ a dl) ∗ FetchAbs a d₁)) := by
  refine .trans (sep_mono (heapInv_eq (Rel (V := V) L) μ).1 .rfl) ?_
  refine .trans sep_exists_right.1 (exists_elim fun w => ?_)
  rcases hw : Std.PartialMap.get? w a with _ | â'
  · refine .trans (sep_mono (sep_mono (heapAbs_insert w a d₁ hw) .rfl) .rfl) ?_
    refine .trans (sep_mono bupd_frame_right .rfl) ?_
    refine .trans bupd_frame_right (bupd_mono ?_)
    refine .trans (sep_mono sep_assoc.1 .rfl) ?_
    refine .trans sep_assoc.1 ?_
    have hEnt : iprop((FetchAbs a d₁ ∗
          (∀ b, EntryRel (HeapInv (Rel (V := V) L)) (Rel (V := V) L)
            (Std.PartialMap.get? w b) (μ.car b))) ∗
          (FetchAbs a d₁ -∗
            ▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁ dl.car)) ⊢
        iprop(∀ b, EntryRel (HeapInv (Rel (V := V) L)) (Rel (V := V) L)
          (Std.PartialMap.get? (Std.PartialMap.insert w a d₁) b)
          ((Heap.set μ a dl).car b)) := by
      refine forall_intro fun b => ?_
      by_cases hb : a = b
      · rw [Heap.set_get, if_pos hb, Std.LawfulPartialMap.get?_insert_eq hb]
        exact (sep_mono sep_elim_left .rfl).trans wand_elim_right
      · rw [Heap.set_get, if_neg hb, Std.LawfulPartialMap.get?_insert_ne hb]
        exact sep_elim_left.trans (sep_elim_right.trans (forall_elim b))
    refine .trans (sep_mono .rfl ((and_intro hEnt
      (sep_elim_left.trans sep_elim_left)).trans persistent_and_sep_mp)) ?_
    refine .trans sep_assoc.2 ?_
    refine sep_mono ?_ .rfl
    exact (exists_intro (Std.PartialMap.insert w a d₁)).trans
      (heapInv_eq (Rel (V := V) L) (Heap.set μ a dl)).2
  · refine .trans (sep_elim_left.trans (sep_elim_right.trans (forall_elim a))) ?_
    rw [hw, hcell]
    exact false_elim

/-- One unfolding of a memoized cell: force the stored thunk and bind the
    cell update. -/
theorem memo_car (a : Addr) (d : D) :
    (D.memo a (Later.next d)).car ≡ D.bind d (D.memo.cont a (D.memo a)) :=
  D.memo_unfold a (Later.next d)

theorem thunk_proper_a (S : Heap D -n> NeedProp V) (rec : V → Trace VH -n> NeedProp V)
    (ah : V) {a a' : D} (h : a ≡ a') : Thunk S rec ah a ⊣⊢ Thunk S rec ah a' :=
  equiv_iff.mp (OFE.equiv_dist.mpr fun n => thunk_ne_a S rec ah (OFE.equiv_dist.mp h n))

/-- The backing of a memoized value: fetching it emits `update` and rewrites
    the cell to itself, so the backing is a Löb fixpoint over the promise. -/
theorem memo_ret_backing (laws : AbstractionLaws V) (a : Addr) (d₁ : Discrete V)
    (v : Value D) (hv : v.isStuck = false) :
    iprop(□ SoundVal L (Rel (V := V) L) d₁ v ∧ FetchAbs a d₁) ⊢
      iprop(□ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁
        (D.bind (D.ret v) (D.memo.cont a (D.memo a)))) := by
  refine loeb_intuit_hyp ?_
  show _ ⊢ iprop(∀ ν, HeapInv (Rel (V := V) L) ν -∗
    Rel (V := V) L d₁ (D.runAt ν (D.bind (D.ret v) (D.memo.cont a (D.memo a)))))
  refine forall_intro fun ν => ?_
  refine wand_intro_left ?_
  refine .trans ?_ (rel_proper (V := V) d₁
    ((D.bind_run (D.ret v) (D.memo.cont a (D.memo a)) ν).trans
      (((Trace.bind (D.kCont (D.memo.cont a (D.memo a)))).ne.eqv (D.ret_run v ν)).trans
        (Trace.bind_ret (D.kCont (D.memo.cont a (D.memo a))) (v, ν))))).2
  refine .trans ?_ (rel_proper (V := V) d₁ (D.memoCont_run a (D.memo a) hv ν)).2
  refine .trans ?_ (rel_step (V := V) d₁ .update _).2
  refine .trans ?_ (exists_intro d₁)
  have hupd : AbstractDomain.step (D := V) .update d₁ ≤ (d₁ : V) := by
    rw [laws.update]
    exact Std.IsPreorder.le_refl (α := V) d₁
  refine and_intro (pure_intro hupd) ?_
  refine .trans ?_ bupd_intro
  refine .trans ?_ later_intro
  refine .trans ?_ (rel_ret (V := V) d₁ _).2
  refine .trans (and_intro
    (sep_elim_right.trans (and_elim_l.trans and_elim_l))
    (.trans (and_intro (sep_mono .rfl (and_elim_l.trans and_elim_r))
        ((sep_elim_right.trans and_elim_r).trans (later_mono (intuitionistically_mono
          (thunk_proper_a _ _ _ (memo_car a (D.ret v))).2))))
      (heapInv_update ν a d₁ (D.memo a (Later.next (D.ret v)))))) ?_
  exact persistent_and_sep_mp.trans (sep_mono intuitionistically_elim .rfl)

/-- The write-back: a forced thunk that reached the value `v` emits `update`
    and rewrites its cell to the memoized value, whose backing at the promise
    comes from `memo_ret_backing`; the running bound is below the promise. -/
theorem memo_cont_val_case (laws : AbstractionLaws V) (a : Addr) (d₁ : Discrete V)
    (v : Value D) (hv : v.isStuck = false) {ν' : Heap D} {dx : V}
    (hd₁ : dx ≤ (d₁ : V)) :
    iprop((FetchAbs (V := V) a d₁ : NeedProp V) ∧
        (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) ν')) ⊢
      Rel (V := V) L dx (D.runAt ν' (D.memo.cont a (D.memo a) v)) := by
  refine .trans ?_ (rel_proper (V := V) dx (D.memoCont_run a (D.memo a) hv ν')).2
  refine .trans ?_ (rel_step (V := V) dx .update _).2
  refine .trans ?_ (exists_intro dx)
  have hupd : AbstractDomain.step (D := V) .update dx ≤ dx := by
    rw [laws.update]
    exact Std.IsPreorder.le_refl (α := V) dx
  refine and_intro (pure_intro hupd) ?_
  refine .trans ?_ bupd_intro
  refine .trans ?_ later_intro
  refine .trans ?_ (rel_ret (V := V) dx _).2
  have hSV1 : iprop((FetchAbs (V := V) a d₁ : NeedProp V) ∧
      (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) ν')) ⊢
      iprop(□ SoundVal L (Rel (V := V) L) d₁ v) :=
    and_elim_r.trans (sep_elim_left.trans
      ((soundVal_mono_bound _ hd₁ v).trans persistent_intuitionistically))
  have hT : iprop((FetchAbs (V := V) a d₁ : NeedProp V) ∧
      (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) ν')) ⊢
      iprop(▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁
        ((D.memo a (Later.next (D.ret v))).car)) :=
    ((and_intro hSV1 and_elim_l).trans (memo_ret_backing laws a d₁ v hv)).trans
      ((intuitionistically_mono (thunk_proper_a _ _ _ (memo_car a (D.ret v))).2).trans
        later_intro)
  refine .trans (and_intro (and_elim_r.trans sep_elim_left) (.trans (and_intro
      (.trans (and_intro and_elim_l (and_elim_r.trans sep_elim_right))
        (persistent_and_sep_mp.trans sep_comm.1))
      hT) (heapInv_update ν' a d₁ (D.memo a (Later.next (D.ret v)))))) ?_
  exact persistent_and_sep_mp

/-- The backing of a freshly memoized rhs at the promise `d₁`: forcing it
    runs the rhs below `rhs₂ d₁`, the pre-fixpoint property caps the bound at
    `d₁`, and the write-back re-establishes the invariant with a memoized
    value cell. -/
theorem memo_backing (laws : AbstractionLaws V) (a : Addr) (d₁ : Discrete V)
    (rhs₁ : D -n> D) (rhs₂ : Discrete V -n> Discrete V)
    (hpre : LE.le (α := V) (rhs₂ d₁) d₁)
    (hfresh : ∀ y, y ∉ L → Fresh (D := Discrete V) y d₁) :
    iprop((□ ∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ → SoundR (V := V) L (rhs₁ a₁) (rhs₂ a₂)) ∧
        FetchAbs a d₁) ⊢
      iprop(□ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁
        ((D.memo a (Later.next (rhs₁ (fetch a)))).car)) := by
  have Hk : ∀ (v : Value D) (ν' : Heap D) (dx : V), dx ≤ (rhs₂ d₁ : V) →
      iprop((FetchAbs (V := V) a d₁ : NeedProp V) ∧
          (SoundVal L (Rel (V := V) L) dx v ∗ HeapInv (Rel (V := V) L) ν')) ⊢
        Rel (V := V) L dx (D.runAt ν' (D.memo.cont a (D.memo a) v)) := by
    intro v ν' dx hdx
    have hd₁ : dx ≤ (d₁ : V) := Std.IsPreorder.le_trans _ _ _ hdx hpre
    cases v with
    | stuck => exact and_elim_r.trans (rel_ret_run (V := V) _ Value.stuck ν').2
    | fn f => exact memo_cont_val_case laws a d₁ _ rfl hd₁
    | con K ds => exact memo_cont_val_case laws a d₁ _ rfl hd₁
  have hbase : iprop((□ ∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ →
        SoundR (V := V) L (rhs₁ a₁) (rhs₂ a₂)) ∧ FetchAbs a d₁) ⊢
      Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁
        (D.bind (rhs₁ (fetch a)) (D.memo.cont a (D.memo a))) := by
    show _ ⊢ iprop(∀ ν, HeapInv (Rel (V := V) L) ν -∗
      Rel (V := V) L d₁ (D.runAt ν (D.bind (rhs₁ (fetch a)) (D.memo.cont a (D.memo a)))))
    refine forall_intro fun ν => ?_
    refine wand_intro_left ?_
    refine .trans ?_ (rel_proper (V := V) d₁
      (D.bind_run (rhs₁ (fetch a)) (D.memo.cont a (D.memo a)) ν)).2
    refine .trans ?_ (rel_mono_bound hpre _)
    refine .trans ?_ (rel_bind (V := V) iprop(FetchAbs (V := V) a d₁)
      (D.memo.cont a (D.memo a)) (fun dx => dx)
      (fun h => h) (fun _ _ => Std.IsPreorder.le_refl _)
      (fun ev dx => laws.step_inc ev dx) (rhs₂ d₁) Hk
      (D.runAt ν (rhs₁ (fetch a))))
    refine and_intro (sep_elim_right.trans and_elim_r) ?_
    refine .trans (sep_mono .rfl ?_) (sep_comm.1.trans (soundR_elim _ _ ν))
    refine .trans (and_mono
      (intuitionistically_elim.trans ((forall_elim (fetch a)).trans (forall_elim d₁)))
      ((fetchAbs_to_isThunk a d₁ hfresh).trans intuitionistic_alias)) ?_
    exact imp_elim_left
  refine .trans (intuitionistic_alias.trans (intuitionistically_mono hbase)) ?_
  exact intuitionistically_mono (thunk_proper_a _ _ _ (memo_car a (rhs₁ (fetch a)))).2

/-- **Bind**: the by-need `let` allocates a fresh cell holding the memoized
    rhs; the ghost step promises the abstract pre-fixpoint `d₁` of the rhs to
    the fresh address, the memoized rhs backs the promise, and the body runs
    on the promise. The promise is fresh outside the let universe because the
    rhs is (`Fresh.bind_id`). -/
theorem soundR_bind (laws : AbstractionLaws V) (rhs₁ body₁ : D -n> D)
    (rhs₂ body₂ : Discrete V -n> Discrete V)
    (hff : ∀ y, y ∉ L → FreshFn (D := Discrete V) y (fun a => rhs₂ a)) :
    iprop((□ ∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ → SoundR (V := V) L (rhs₁ a₁) (rhs₂ a₂)) ∧
          (∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ → SoundR (V := V) L (body₁ a₁) (body₂ a₂))) ⊢
      SoundR (V := V) L (Domain.step .let1 (Domain.bind rhs₁ body₁))
        (Domain.step .let1 (Domain.bind rhs₂ body₂)) := by
  obtain ⟨d₁, hpre, hbody, hfresh⟩ : ∃ d₁ : V, Lat.le (a := V) (rhs₂ d₁) d₁ = true ∧
      Lat.le (a := V) (body₂ d₁)
        (AbstractDomain.bind (fun a => rhs₂ a) (fun a => body₂ a)) = true ∧
      (∀ y, y ∉ L → Fresh (D := Discrete V) y d₁) :=
    ⟨AbstractDomain.bind (fun a => rhs₂ a) id,
      laws.bind_prefix _, laws.bind_lazy _ _,
      fun y hy => Fresh.bind_id (hff y hy)⟩
  refine soundR_intro fun μ => ?_
  have hwand : iprop(□ ∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ →
      SoundR (V := V) L (rhs₁ a₁) (rhs₂ a₂)) ⊢
      iprop(FetchAbs (V := V) (Heap.nextFree μ) d₁ -∗
        ▷ □ Thunk (HeapInv (Rel (V := V) L)) (Rel (V := V) L) d₁
          ((D.memo (Heap.nextFree μ)
            (Later.next (rhs₁ (fetch (Heap.nextFree μ))))).car)) := by
    refine wand_intro_left ?_
    refine .trans sep_and ?_
    refine .trans (and_intro and_elim_r and_elim_l) ?_
    exact (memo_backing laws (Heap.nextFree μ) d₁ rhs₁ rhs₂ hpre hfresh).trans later_intro
  have happB : iprop(FetchAbs (V := V) (Heap.nextFree μ) d₁ ∗
      ((□ ∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ → SoundR (V := V) L (rhs₁ a₁) (rhs₂ a₂)) ∧
        (∀ a₁ a₂, □ IsThunk (V := V) L a₁ a₂ → SoundR (V := V) L (body₁ a₁) (body₂ a₂)))) ⊢
      SoundR (V := V) L (body₁ (fetch (Heap.nextFree μ))) (body₂ d₁) := by
    refine .trans sep_and ?_
    refine .trans (and_intro
      (and_elim_r.trans (and_elim_r.trans
        ((forall_elim (fetch (Heap.nextFree μ))).trans (forall_elim d₁))))
      (and_elim_l.trans ((fetchAbs_to_isThunk _ d₁ hfresh).trans intuitionistic_alias))) ?_
    exact imp_elim_left
  refine .trans ?_ (rel_step_run .let1 _ (D.bindLet rhs₁ body₁) μ).2
  refine .trans ?_ (exists_intro (body₂ d₁))
  refine and_intro (pure_intro (laws.mono_step .let1 hbody)) ?_
  refine .trans ?_ (bupd_mono (later_mono
    (rel_proper (V := V) (body₂ d₁) (D.bindLet_run rhs₁ body₁ μ)).2))
  refine .trans (sep_mono .rfl ((and_intro and_elim_l .rfl).trans persistent_and_sep_mp)) ?_
  refine .trans sep_assoc.2 ?_
  refine .trans (sep_mono (sep_mono .rfl hwand) .rfl) ?_
  refine .trans (sep_mono (heapInv_alloc μ (Heap.nextFree μ) d₁
    (D.memo (Heap.nextFree μ) (Later.next (rhs₁ (fetch (Heap.nextFree μ)))))
    (Heap.nextFree_spec μ)) .rfl) ?_
  refine .trans bupd_frame_right (bupd_mono ?_)
  refine .trans ?_ later_intro
  refine .trans sep_assoc.1 ?_
  exact (sep_mono .rfl happB).trans (sep_comm.1.trans (soundR_elim _ _ _))

/-! ## The instance and the fundamental lemma -/

/-- The by-need soundness `LR2` over `NeedProp V` at the let universe `L`:
    the relation is the invariant-indexed representation `SoundR`, thunks are
    ghost-table promises, and the closure fields are discharged from the
    abstraction laws. -/
def soundLR2 (laws : AbstractionLaws V) (L : List Var) :
    LR2 (NeedProp V) D (Discrete V) L where
  R := SoundR (V := V) L
  IsThunk := IsThunk (V := V) L
  IsThunk_to_R := soundR_isThunk_to_R
  IsThunk_fresh := fun _ _ => and_elim_r
  stuck := soundR_stuck
  fn := soundR_fn
  con := soundR_con
  apply := soundR_app laws
  select := soundR_case laws
  bind := soundR_bind laws

/-- **Abstract By-need Interpretation** (`thm:abstract-by-need`). Under the
    abstraction laws, the analysis `eval e` at `Discrete V` soundly abstracts
    the by-need denotation `evalByNeed e`, for every `e` scoped under the let
    universe `L` and related environments whose abstract entries are fresh
    outside `L`. -/
theorem byNeed_sound (laws : AbstractionLaws V) (e : Exp) (hsc : e.Scoped L)
    (ρ₁ : Env D) (ρ₂ : Env (Discrete V)) (hρ : EnvFresh L ρ₂) :
    (soundLR2 laws L).EnvOk ρ₁ ρ₂ ⊢ SoundR (V := V) L (evalByNeed e ρ₁) (eval e ρ₂) :=
  LR2.fundamental (soundLR2 laws L) e hsc ρ₁ ρ₂ hρ

end Need

/-! ## Application to usage analysis (`thm:usage-abstracts-need`) -/

/-- Usage analysis soundly abstracts the by-need semantics: an instance of
    `thm:abstract-by-need` at the bounded domain `UDk k`, for a Barendregt
    program under its own let binders. -/
theorem usage_abstracts_need (k : Nat) (e : Exp) (hb : Barendregt e)
    (ρ₁ : Env D) (ρ₂ : Env (Discrete (UDk k))) (hρ : EnvFresh e.letBV ρ₂) :
    (Need.soundLR2 (usageAbstractionLaws k) e.letBV).EnvOk ρ₁ ρ₂ ⊢
      Need.SoundR (V := UDk k) e.letBV (evalByNeed e ρ₁) (evalUsgk k e ρ₂) :=
  Need.byNeed_sound (usageAbstractionLaws k) e hb.scoped ρ₁ ρ₂ hρ

end AbsDen
