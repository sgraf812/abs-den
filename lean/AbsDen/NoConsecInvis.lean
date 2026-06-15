import AbsDen.ByNeed
import AbsDen.LR

/-!
# No Triple Consecutive Invisible Steps

Step-indexed predicates used to prove that traces from `evalByNeed` have at
most 2 consecutive `T.invis` steps.

The construction is loeb-based (`NewIdea` namespace): `GoodP` is the
guarded-fixed-point predicate on `D`-values; `TraceGoodP` is the trace
predicate it unfolds to; `RetGoodP` is the value-and-heap predicate at `.ret`.

`LR.good` (in `LRGood.lean`) packages this as a logical relation, and
`LR.fundamental` delivers the main theorems.
-/

open ByNeed
set_option maxHeartbeats 1600000
namespace ByNeed

/-! ## Equational lemmas for `D`-operations -/

theorem Value_F_Rep_restrict_stuck {n m : Nat} (hm : m ≤ n) :
    World.restrict (Value.F.toRep (▹ D) (.stuck : Value.F (▹ D) n)) hm
    = Value.F.toRep (▹ D) (.stuck : Value.F (▹ D) m) := by
  simp only [Value.F.toRep]
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    rw [@World.restrict_self (Value.F.Rep (▹ D))]
  | succ n' ih =>
    by_cases hmn : m = n'+1
    · subst hmn
      rw [@World.restrict_self (Value.F.Rep (▹ D))]
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      rw [heq, @World.restrict_succ (Value.F.Rep (▹ D))]
      have hstep : @World.restrictStep (Value.F.Rep (▹ D)) _ n' (Sum.inl ())
                 = (Sum.inl () : Value.F.Rep (▹ D) n') := rfl
      rw [hstep]
      exact ih hm'

/-- `W.restrict (Value.F.toRep _ (.fn g)) hm` matches `Sum.inr (Sum.inl _)` shape. -/
theorem Value_F_Rep_restrict_fn_shape : ∀ {n : Nat} (g : World.Function (▹ D) (▹ D) n)
    {m : Nat} (hm : m ≤ n),
    ∃ g', World.restrict (Value.F.toRep (▹ D) (.fn g)) hm = Sum.inr (Sum.inl g') := by
  intro n
  induction n with
  | zero =>
    intro g m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    refine ⟨g, ?_⟩
    show World.restrict (Value.F.toRep _ (.fn g)) hm = _
    rw [@World.restrict_self (Value.F.Rep (▹ D))]; rfl
  | succ n' ih =>
    intro g m hm
    by_cases hmn : m = n'+1
    · subst hmn
      refine ⟨g, ?_⟩
      rw [@World.restrict_self (Value.F.Rep (▹ D))]; rfl
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      rw [heq, @World.restrict_succ (Value.F.Rep (▹ D))]
      have hstep' : (@World.restrictStep (Value.F.Rep (▹ D)) _ n' (Value.F.toRep _ (.fn g))
                  : Value.F.Rep (▹ D) n')
                 = Value.F.toRep _ (.fn (World.restrictStep g)) := rfl
      rw [hstep']
      exact ih (World.restrictStep g) hm'

/-- `W.restrict (Value.F.toRep _ (.con K ds)) hm` matches `Sum.inr (Sum.inr _)` shape. -/
theorem Value_F_Rep_restrict_con_shape : ∀ {n : Nat} (K : ConTag)
    (ds : world(List (▹ D)) n) {m : Nat} (hm : m ≤ n),
    ∃ ds', World.restrict (Value.F.toRep (▹ D) (.con K ds)) hm = Sum.inr (Sum.inr (K, ds')) := by
  intro n
  induction n with
  | zero =>
    intro K ds m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    refine ⟨ds, ?_⟩
    rw [@World.restrict_self (Value.F.Rep (▹ D))]; rfl
  | succ n' ih =>
    intro K ds m hm
    by_cases hmn : m = n'+1
    · subst hmn
      refine ⟨ds, ?_⟩
      rw [@World.restrict_self (Value.F.Rep (▹ D))]; rfl
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      rw [heq, @World.restrict_succ (Value.F.Rep (▹ D))]
      have hstep' : (@World.restrictStep (Value.F.Rep (▹ D)) _ n' (Value.F.toRep _ (.con K ds))
                  : Value.F.Rep (▹ D) n')
                 = Value.F.toRep _ (.con K (World.restrictStep ds)) := rfl
      rw [hstep']
      exact ih K (World.restrictStep ds) hm'

@[simp] theorem D_ret_eq {n : Nat} (v : Value.F (▹ D) n) (m : Nat)
    (hm : m ≤ n) (μ : Heap (▹ D) m) :
    D.unfold (D.ret v) m hm μ = T.ret (World.restrict (Value.F.toRep _ v) hm, μ) := by
  simp [D.ret]

@[simp] theorem D_bind_eq {n : Nat} (d : D n) (kont : World.Function (Value.F (Later D)) D n)
    (m : Nat) (hm : m ≤ n) (μ : Heap (▹ D) m) :
    (D.bind d kont).unfold m hm μ =
    T.bind (d.unfold m hm μ) (fun j hj (v, μ') =>
      (kont j (by omega) (Value.F.ofRep _ v)).unfold j (Nat.le_refl j) μ') := by
  unfold D.bind; simp; rfl

@[simp] theorem D_invis_eq {n : Nat} (dl : ▹ D n) (m : Nat)
    (hm : m ≤ n) (μ : Heap (▹ D) m) :
    D.unfold (D.invis dl) m hm μ =
    T.fold (.invis (Later.hmap m (fun i _hi d =>
      d.unfold i (Nat.le_refl i) (World.restrict μ (by omega)))
      (World.restrict dl hm))) := by simp [D.invis]

@[simp] theorem T_uf {n : Nat} (x : T.F VH (Later (T VH)) n) : T.unfold (T.fold x) = x := by
  simp only [T.unfold, T.fold, Function.comp, World.Fix.fold, World.Fix.unfold, cast_cast, cast_eq]
  cases x <;> rfl

private theorem HashMap_get?_empty {α β : Type} [BEq α] [Hashable α]
    (a : α) : Std.HashMap.get? (∅ : Std.HashMap α β) a = none := by
  simp only [Std.HashMap.get?]; have : (∅ : Std.HashMap α β).inner = ∅ := rfl; rw [this]
  simp [Std.DHashMap.Const.get?, Std.DHashMap.Internal.Raw₀.Const.get?]

/-! ## Trace predicates -/

noncomputable def NotRet : (n : Nat) → T VH n → Prop
  | 0, _ => True
  | _n + 1, t => match T.unfold t with | .ret _ => False | _ => True

/-- The trace is `ret` with a stuck value (Sum.inl PUnit.unit). -/
noncomputable def IsRetStuck : (n : Nat) → T VH n → Prop
  | 0, _ => False
  | _n + 1, t => match T.unfold t with
    | .ret (v, _) => v = Sum.inl PUnit.unit
    | _ => False

noncomputable def StartsVisible : (n : Nat) → T VH n → Prop
  | 0, _ => True
  | _n + 1, t => match T.unfold t with | .ret _ => True | .step _ _ => True | .invis _ => False

noncomputable def StartsWithStep : (n : Nat) → T VH n → Prop
  | 0, _ => True
  | _n + 1, t => match T.unfold t with | .step _ _ => True | _ => False

/-- "No more than `S` consecutive invisible steps." The reset budget `S` is
    refreshed on every `.step` event (or `.ret`); only `.invis` consumes budget. -/
noncomputable def NCI (S : Nat) : Nat → (n : Nat) → T VH n → Prop
  | _, 0, _ => True
  | k, n + 1, t => match T.unfold t with
    | .ret _ => True
    | .step _ dl => NCI S S n dl
    | .invis dl => match k with | 0 => False | j + 1 => NCI S j n dl
termination_by _ n _ => n

abbrev NoTripleInvis (n : Nat) (t : T VH n) : Prop := NCI 2 2 n t

/-! ## Loeb-based "good" predicate

`GoodP` is the value-level "good" predicate, defined via `loeb` (guarded
fixed-point) on `world(D → Prop)`. The body checks that under a good heap,
the value's unfolded trace is `TraceGoodP`-good. The trace predicate
`TraceGoodP` is itself loeb-based; the `.ret` case is governed by
`RetGoodP`, which is the function-value/con-fields/heap-good triple. -/

namespace NewIdea

namespace Parametric

/-- A heap is `P`-good when every entry, viewed at one level down via `▷`
    (the later modality), satisfies `P`. -/
def Heap {n : Nat} (P : ▹ world(D → Prop) n) (μ : Heap (▹ D) n) : Prop :=
  ∀ (a : Addr) (dl : ▹ D n), Std.HashMap.get? μ a = some dl →
    Later.prop (Later.ap' _ P dl)

end Parametric

/-- HashMap.get? commutes with Functor.map on AddrMap. -/
theorem AddrMap_get?_map {V W : Type} (f : V → W) (m : AddrMap V) (a : Addr) :
    Std.HashMap.get? (Functor.map f m : AddrMap W) a =
    Option.map f (Std.HashMap.get? m a) := by
  simp only [Std.HashMap.get?_eq_getElem?]
  show (Std.HashMap.fold (fun (acc : Std.HashMap Nat W) k v => acc.insert k (f v)) ∅ m)[a]? = _
  rw [Std.HashMap.fold_eq_foldl_toList]
  rw [LR.foldl_insert_map_getElem?]
  · congr 1; exact LR.HashMap_rebuild_getElem? m a
  · intro b; simp

/-- `Param.Heap` is closed under `restrictStep` if the predicate satisfies an
    entry-wise closure. -/
theorem Parametric.Heap_restrictStep {n : Nat}
    (P : Later world(D → Prop) (n+1)) (μ : ByNeed.Heap (Later D) (n+1))
    (hμ : Parametric.Heap P μ)
    (h_close : ∀ (dl : Later D (n+1)),
                 ▷(Later.ap' (n+1) P dl)
                 → ▷(Later.ap' n (World.restrictStep P : Later world(D → Prop) n)
                      (World.restrictStep dl : Later D n))) :
    Parametric.Heap (World.restrictStep P) (World.restrictStep μ) := by
  intro a dl_k h_get
  have h_map : Std.HashMap.get? (World.restrictStep μ : ByNeed.Heap (Later D) n) a =
    Option.map World.restrictStep (Std.HashMap.get? μ a) := by
    show Std.HashMap.get? (Functor.map (@World.restrictStep (Later D) _ n) μ) a = _
    exact AddrMap_get?_map _ μ a
  rw [h_map] at h_get
  cases hget : Std.HashMap.get? μ a with
  | none => rw [hget] at h_get; simp at h_get
  | some dl_orig =>
    simp only [hget, Option.map] at h_get
    cases h_get
    exact h_close dl_orig (hμ a dl_orig hget)

/-- The body of `TraceGoodP`'s `loeb`. Restricts the outer `Recur` to the
    trace level `m` *first*, then applies `Later.ap'` at level `m`. This makes
    the body Kripke-natural across outer levels: the body's value at the
    trace level depends only on `Recur↓` (which is restrict-stable). -/
def TraceGoodPBody (S : Nat) {N : Nat} (RetGoodP : world(VH → Prop) N) :
    World.Function (Later world(Nat → T VH → Prop)) world(Nat → T VH → Prop) N :=
  fun n _ Recur _ _ steps m _ t =>
    let Recur (k : Nat) : Later world(T VH → Prop) m :=
      Later.ap' m (Recur↓) (Later.next k)
    match t.unfold with
    | .ret v => RetGoodP _ (by omega) v
    | .step _ tl =>
      Later.prop (Later.ap' m (Recur S) tl)
    | .invis dl => match steps with
      | (0 : Nat) => False
      | j + 1 =>
        (Later.prop (Later.map NotRet _ dl) ∨
         Later.prop (Later.map IsRetStuck _ dl)) ∧
        (Later.prop (Later.ap' m (Recur j) dl))

/-- The trace predicate, parameterised by the reset budget `S` and the
    value/heap predicate at `.ret`. Built via `loeb`: at `.step`, recurses
    with budget reset to `S`; at `.invis`, decrements budget; at `.ret`,
    defers to `RetGoodP`. -/
def TraceGoodP (S : Nat) {n : Nat} (RetGoodP : world(VH → Prop) n) :
    world(Nat → T VH → Prop) n :=
  loeb (A := world(Nat → T VH → Prop)) (n := n) (TraceGoodPBody S RetGoodP)

/-- `TraceGoodPBody` is Kripke-natural. Body uses `Recur↓` (restricted) — so
    the value depends only on `W.restrict Recur (m ≤ n)`, which by
    `World.restrict_succ` is invariant under the outer restriction. -/
theorem TraceGoodPBody_natural (S : Nat) {N : Nat} {RetGoodP : world(VH → Prop) N} :
    (TraceGoodPBody S RetGoodP).Natural := by
  intro m hm x
  funext m_body hm_body steps m'_body hm'_body t
  simp only [World.Function.restrictStep_eq]
  unfold TraceGoodPBody
  have h_eq := World.restrict_succ x (Nat.le_trans hm'_body hm_body)
  cases hu : T.unfold t with
  | ret v => simp [hu]
  | step ev tl =>
    simp only [hu]
    rw [h_eq]
  | invis dl =>
    cases steps with
    | zero => simp [hu]
    | succ j =>
      simp only [hu]
      rw [h_eq]

/-- The body's `.ret` case, as a rewritable equation. -/
theorem TraceGoodPBody_ret_eq (S : Nat) {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (steps : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (v : VH k)
    (hu : T.unfold t = .ret v) :
  TraceGoodPBody S RetGoodP n hn Recur m hm steps k hk t
  = RetGoodP k (Nat.le_trans hk (Nat.le_trans hm hn)) v := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.step` case, as a rewritable equation. The `.step` resets the
    budget to the reset value `S` (so consecutive `.invis` streaks restart). -/
theorem TraceGoodPBody_step_eq (S : Nat) {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (steps : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (ev : Event) (tl : Later (T VH) k)
    (hu : T.unfold t = .step ev tl) :
  TraceGoodPBody S RetGoodP n hn Recur m hm steps k hk t
  = ▷(Later.ap' k
       (Later.ap' k (World.restrict Recur (Nat.le_trans hk hm)) (Later.next S)) tl) := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.invis` case at `steps = j+1`. -/
theorem TraceGoodPBody_invis_eq (S : Nat) {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (j : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (dl : Later (T VH) k)
    (hu : T.unfold t = .invis dl) :
  TraceGoodPBody S RetGoodP n hn Recur m hm (j+1) k hk t
  = ((▷(Later.map NotRet k dl) ∨ ▷(Later.map IsRetStuck k dl)) ∧
     ▷(Later.ap' k
        (Later.ap' k (World.restrict Recur (Nat.le_trans hk hm)) (Later.next j)) dl)) := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.invis` case at `steps = 0` is `False`. -/
theorem TraceGoodPBody_invis_zero (S : Nat) {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (dl : Later (T VH) k)
    (hu : T.unfold t = .invis dl) :
  TraceGoodPBody S RetGoodP n hn Recur m hm (0 : Nat) k hk t = False := by
  unfold TraceGoodPBody
  rw [hu]

/-- `restrictStep (TraceGoodPBody S RetGoodP) = TraceGoodPBody S (restrictStep RetGoodP)`. -/
theorem TraceGoodPBody_restrictStep_RetGoodP (S : Nat) {N : Nat}
    (RetGoodP : world(VH → Prop) (N+1)) :
    World.restrictStep (TraceGoodPBody S RetGoodP)
      = TraceGoodPBody S (World.restrictStep RetGoodP) := by
  rfl

/-- `restrictStep` of `TraceGoodP S` is `TraceGoodP S` of `restrictStep RetGoodP`. -/
theorem TraceGoodP_restrictStep (S : Nat) {n : Nat} (RetGoodP : world(VH → Prop) (n+1)) :
    World.restrictStep (TraceGoodP S RetGoodP) = TraceGoodP S (World.restrictStep RetGoodP) := by
  show World.restrictStep (loeb (TraceGoodPBody S RetGoodP))
     = loeb (TraceGoodPBody S (World.restrictStep RetGoodP))
  rw [restrictStep_loeb_eq_loeb_restrictStep (TraceGoodPBody_natural S)]
  rw [TraceGoodPBody_restrictStep_RetGoodP]

/-- Iterated: `W.restrict (TraceGoodP S RetGoodP) hm = TraceGoodP S (W.restrict RetGoodP hm)`. -/
theorem TraceGoodP_restrict (S : Nat) : ∀ {n : Nat} (RetGoodP : world(VH → Prop) n)
    {m : Nat} (hm : m ≤ n),
    World.restrict (TraceGoodP S RetGoodP) hm = TraceGoodP S (World.restrict RetGoodP hm) := by
  intro n
  induction n with
  | zero =>
    intro RetGoodP m hm
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    rw [show World.restrict (TraceGoodP S RetGoodP) hm = TraceGoodP S RetGoodP from
        World.restrict_self _]
    rw [show World.restrict RetGoodP hm = RetGoodP from World.restrict_self _]
  | succ n' ih =>
    intro RetGoodP m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [show World.restrict (TraceGoodP S RetGoodP) hm = TraceGoodP S RetGoodP from
          World.restrict_self _]
      rw [show World.restrict RetGoodP hm = RetGoodP from World.restrict_self _]
    · have hm' : m ≤ n' := by omega
      rw [show World.restrict (TraceGoodP S RetGoodP) hm
           = World.restrict (World.restrictStep (TraceGoodP S RetGoodP)) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]
      rw [TraceGoodP_restrictStep]
      rw [ih (World.restrictStep RetGoodP) hm']
      rw [show World.restrict RetGoodP hm
            = World.restrict (World.restrictStep RetGoodP) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]

/-- Bridge: `Later.next (loeb _)` then `W.restrict` to lower level collapses to
    `TraceGoodP` with restricted `RetGoodP`. Used by `TraceGoodP_implies_NCI`. -/
theorem Later_next_loeb_restrict (S : Nat) {n : Nat} (RetGoodP : world(VH → Prop) n)
    {k : Nat} (hk : k + 1 ≤ n) :
    World.restrict (Later.next (loeb (TraceGoodPBody S RetGoodP))) hk
    = TraceGoodP S (World.restrict RetGoodP (Nat.le_of_succ_le hk)) := by
  cases n with
  | zero => omega
  | succ n' =>
    have hk' : k ≤ n' := Nat.le_of_succ_le_succ hk
    have h1 : (Later.next (loeb (TraceGoodPBody S RetGoodP)) :
                Later (world(Nat → T VH → Prop)) (n'+1))
            = World.restrictStep (loeb (TraceGoodPBody S RetGoodP)) := rfl
    rw [h1, restrictStep_loeb_eq_loeb_restrictStep (TraceGoodPBody_natural S),
        TraceGoodPBody_restrictStep_RetGoodP]
    have h2 : loeb (TraceGoodPBody S (World.restrictStep RetGoodP))
            = TraceGoodP S (World.restrictStep RetGoodP) := rfl
    rw [h2]
    rw [@World.restrict_Later_eq (world(Nat → T VH → Prop))]
    rw [TraceGoodP_restrict]
    congr 1
    exact (World.restrict_succ RetGoodP hk').symm

/-- The value-and-heap predicate for `.ret`, parameterised by the
    later-`GoodP`-style predicate on `D`-values. Function- and con-fields
    are `▷ DGoodP`-good (i.e., `IsLookup`-shape); the heap is
    `Parametric.Heap (DGoodP↓)`-good. -/
def RetGoodP {n : Nat} (DGoodP : ▹ world(D → Prop) n) : world(VH → Prop) n :=
  fun m _ (v, μ) =>
    -- Function-value condition.
    (∀ (g : World.Function (Later D) (Later D) m),
      v = .inr (.inl g) →
      ∀ l (hl : l ≤ m) (dl : ▹ D l),
        Later.prop (Later.ap' _ (DGoodP↓) dl) →
        ∀ j (hj : j ≤ l) (μ' : Heap (▹ D) j),
          Parametric.Heap (DGoodP↓) μ' →
          Later.prop (Later.ap' _ (DGoodP↓) (g l hl dl))) ∧
    -- Constructor-field condition.
    (∀ (K : ConTag) (ds : List (▹ D m)),
      v = .inr (.inr (K, ds)) →
      ∀ (dl : ▹ D m), dl ∈ ds → Later.prop (Later.ap' _ (DGoodP↓) dl)) ∧
    -- Heap-good condition.
    Parametric.Heap (DGoodP↓) μ

/-- `RetGoodP` applied at the `.ret`-style payload `(v, μ)`. -/
theorem RetGoodP_apply {n : Nat} (DGoodP : ▹ world(D → Prop) n)
    (m : Nat) (hm : m ≤ n) (v : Value.F.Rep (▹ D) m) (μ : Heap (▹ D) m) :
    RetGoodP DGoodP m hm (v, μ)
    = ((∀ (g : World.Function (Later D) (Later D) m),
          v = .inr (.inl g) →
          ∀ l (hl : l ≤ m) (dl : ▹ D l),
            Later.prop (Later.ap' _ (DGoodP↓) dl) →
            ∀ j (hj : j ≤ l) (μ' : Heap (▹ D) j),
              Parametric.Heap (DGoodP↓) μ' →
              Later.prop (Later.ap' _ (DGoodP↓) (g l hl dl))) ∧
       (∀ (K : ConTag) (ds : List (▹ D m)),
          v = .inr (.inr (K, ds)) →
          ∀ (dl : ▹ D m), dl ∈ ds → Later.prop (Later.ap' _ (DGoodP↓) dl)) ∧
       Parametric.Heap (DGoodP↓) μ) := rfl

/-- The body of `GoodP`'s `loeb`. Parameterised by the initial step count `S`
    for the outer trace; the reset value (refresh on `.step`) is fixed at 2.
    Heap entries are recursively `GoodP S`-good — pick `S=0` for entries that
    must start visibly. -/
def GoodPBody (S : Nat) {N : Nat} : World.Function (Later world(D → Prop)) world(D → Prop) N :=
  fun n _ Recur m _ d =>
    let Recur_m : Later world(D → Prop) m := Recur↓
    ∀ μ : Heap (▹ D) m, Parametric.Heap Recur_m μ →
      TraceGoodP 2 (RetGoodP Recur_m) m (Nat.le_refl _) S m (Nat.le_refl _)
        (d.unfold m (Nat.le_refl _) (μ↓))

/-- The value-level "good" predicate at initial step count `S`. -/
def GoodP (S : Nat) {n : Nat} : world(D → Prop) n :=
  loeb (A := world(D → Prop)) (n := n) (GoodPBody S)

/-- The body of `GoodP` is Kripke-natural across outer levels: at sub-level
    `m`, the body depends on `Recur` only through `Recur↓` (restricted to
    level `m`) and through `RetGoodP Recur` (which itself only uses
    `Recur↓`). By `World.restrict_succ`, these are invariant under the
    outer restriction `n+1 → n`. Sub-proof needs:
      * `W.restrict Recur (hm.trans le_succ) = W.restrict (restrictStep Recur) hm`
        (`World.restrict_succ`).
      * `TraceGoodP (RetGoodP Recur) at outer k+1, sub-args (m, _, ...) =
        TraceGoodP (RetGoodP (restrictStep Recur)) at outer k, sub-args (m, _, ...)`
        (`TraceGoodP_restrictStep` + RetGoodP natural in its arg).
    Full proof TBD. -/
theorem GoodPBody_natural (S : Nat) {N : Nat} :
    (GoodPBody S : World.Function _ _ N).Natural := by
  intro m hm x
  funext m_body hm_body d
  simp only [World.Function.restrictStep_eq]
  unfold GoodPBody
  rw [World.restrict_succ x hm_body]

/-- W.restrict is proof-irrelevant: any two proofs of `m ≤ n` give the same
    result. Useful to rewrite a generic `m ≤ n+1` to the specific
    `Nat.le_succ_of_le h` shape so `World.restrict_succ` fires. -/
theorem World.restrict_proof_irrel {F : Nat → Type u} [World F]
    {n m : Nat} (x : F n) (h₁ h₂ : m ≤ n) :
    World.restrict x h₁ = World.restrict x h₂ := by
  congr

/-- `restrict` at a generic `m ≤ n+1` proof equals `restrict` at the
    `Nat.le_succ_of_le` form, provided we have `m ≤ n`. -/
theorem World.restrict_le_succ {F : Nat → Type u} [World F]
    {n m : Nat} (x : F (n+1)) (hm : m ≤ n+1) (hm' : m ≤ n) :
    World.restrict x hm = World.restrict (World.restrictStep x) hm' := by
  rw [World.restrict_proof_irrel x hm (Nat.le_succ_of_le hm'),
      World.restrict_succ]

/-- `restrictStep ∘ W.restrict` at `k+1` equals `W.restrict` at `k` (proof-irrelevant version
    accepting a generic `p' : k ≤ N`). The base lemma `World.restrictStep_restrict` in
    `World/Basic.lean` produces `restrict x (Nat.le_of_succ_le h)`; this wrapper lets us
    pass an arbitrary `p' : k ≤ N`. -/
theorem World.restrictStep_restrict' {F : Nat → Type u} [World F]
    {N k : Nat} (x : F N) (p : k+1 ≤ N) (p' : k ≤ N) :
    World.restrictStep (World.restrict x p : F (k+1)) = World.restrict x p' := by
  rw [World.restrictStep_restrict x p, World.restrict_proof_irrel x _ p']

/-- The W.restrict on a Later world(D → Prop) commutes through restrictStep on
    the outer Later instance at corresponding inner levels (proof-irrelevant
    version, no `Nat.le_succ_of_le` pattern required). -/
theorem World.restrict_Later_outer_succ {n m : Nat}
    (DGoodP : Later world(D → Prop) (n+1)) (hm : m ≤ n+1) (hm' : m ≤ n) :
    @World.restrict (Later world(D → Prop)) _ (n+1) m DGoodP hm
    = @World.restrict (Later world(D → Prop)) _ n m (World.restrictStep DGoodP) hm' :=
  World.restrict_le_succ DGoodP hm hm'

/-- `RetGoodP` commutes with `restrictStep` on its `DGoodP` argument. -/
theorem RetGoodP_restrictStep {n : Nat} (DGoodP : ▹ world(D → Prop) (n+1)) :
    World.restrictStep (RetGoodP DGoodP : world(VH → Prop) (n+1))
    = RetGoodP (World.restrictStep DGoodP) := by
  funext m hm vμ
  obtain ⟨v, μ⟩ := vμ
  show RetGoodP DGoodP m (Nat.le_succ_of_le hm) (v, μ)
     = RetGoodP (World.restrictStep DGoodP) m hm (v, μ)
  unfold RetGoodP
  dsimp only []
  -- Equational lemma for W.restrict DGoodP at any sub-level k ≤ n.
  have key_m : World.restrict (F := Later world(D → Prop)) DGoodP
                  (Nat.le_succ_of_le hm)
              = World.restrict (World.restrictStep DGoodP) hm :=
    World.restrict_le_succ DGoodP _ hm
  -- Build the And-wise equation.
  refine (congrArg (· ∧ _) ?_).trans ((congrArg (_ ∧ ·) ?_))
  · -- Function-cond piece A = A'.
    apply propext
    refine Iff.intro (fun h g hg l hl dl hdl j hj μ' hμ' => ?_)
                    (fun h g hg l hl dl hdl j hj μ' hμ' => ?_)
    · have hl_n : l ≤ n := Nat.le_trans hl hm
      have hj_n : j ≤ n := Nat.le_trans hj hl_n
      have h_eq_l : World.restrict (F := Later world(D → Prop)) DGoodP
                      (Nat.le_trans hl (Nat.le_succ_of_le hm))
                  = World.restrict (World.restrictStep DGoodP) hl_n :=
        World.restrict_le_succ DGoodP _ hl_n
      have h_eq_j : World.restrict (F := Later world(D → Prop)) DGoodP
                      (Nat.le_trans hj (Nat.le_trans hl (Nat.le_succ_of_le hm)))
                  = World.restrict (World.restrictStep DGoodP) hj_n :=
        World.restrict_le_succ DGoodP _ hj_n
      rw [← h_eq_l] at hdl
      have := h g hg l hl dl hdl j hj μ' (by rw [h_eq_j]; exact hμ')
      rwa [h_eq_l] at this
    · have hl_n : l ≤ n := Nat.le_trans hl hm
      have hj_n : j ≤ n := Nat.le_trans hj hl_n
      have h_eq_l : World.restrict (F := Later world(D → Prop)) DGoodP
                      (Nat.le_trans hl (Nat.le_succ_of_le hm))
                  = World.restrict (World.restrictStep DGoodP) hl_n :=
        World.restrict_le_succ DGoodP _ hl_n
      have h_eq_j : World.restrict (F := Later world(D → Prop)) DGoodP
                      (Nat.le_trans hj (Nat.le_trans hl (Nat.le_succ_of_le hm)))
                  = World.restrict (World.restrictStep DGoodP) hj_n :=
        World.restrict_le_succ DGoodP _ hj_n
      rw [h_eq_l] at hdl
      have := h g hg l hl dl hdl j hj μ' (by rw [← h_eq_j]; exact hμ')
      rwa [← h_eq_l] at this
  · -- Combined con-cond ∧ heap-cond
    refine (congrArg (· ∧ _) ?_).trans ((congrArg (_ ∧ ·) ?_))
    · -- Con-cond
      apply propext
      refine Iff.intro (fun h K ds heq dl hdl => ?_) (fun h K ds heq dl hdl => ?_)
      · have := h K ds heq dl hdl; rwa [← key_m]
      · have := h K ds heq dl hdl; rwa [key_m]
    · -- Heap-cond
      apply propext
      unfold Parametric.Heap
      refine Iff.intro (fun h a dl h_ => ?_) (fun h a dl h_ => ?_)
      · have := h a dl h_; rwa [← key_m]
      · have := h a dl h_; rwa [key_m]

/-- Iterated: `W.restrict` on `RetGoodP DGoodP` equals `RetGoodP (W.restrict DGoodP)`. -/
theorem RetGoodP_restrict : ∀ {n : Nat} (DGoodP : ▹ world(D → Prop) n)
    {m : Nat} (hm : m ≤ n),
    World.restrict (RetGoodP DGoodP : world(VH → Prop) n) hm
    = RetGoodP (World.restrict DGoodP hm) := by
  intro n
  induction n with
  | zero =>
    intro DGoodP m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) 0) hm
            = RetGoodP DGoodP from World.restrict_self _]
    rw [show World.restrict DGoodP hm = DGoodP from World.restrict_self _]
  | succ n' ih =>
    intro DGoodP m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) (n'+1)) hm
              = RetGoodP DGoodP from World.restrict_self _]
      rw [show World.restrict DGoodP hm = DGoodP from World.restrict_self _]
    · have hm' : m ≤ n' := by omega
      rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) (n'+1)) hm
            = World.restrict (World.restrictStep (RetGoodP DGoodP)) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]
      rw [RetGoodP_restrictStep]
      rw [ih (World.restrictStep DGoodP) hm']
      rw [show World.restrict DGoodP hm
            = World.restrict (World.restrictStep DGoodP) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]

/-! ## `goodP : World.Pred D` — wrapping `GoodP` for `LR.good.P` -/

/-- `GoodP S` at outer level `n+1`, restricted, equals `GoodP S` at outer level `n`. -/
theorem GoodP_restrictStep (S : Nat) {n : Nat} :
    World.restrictStep (GoodP S : world(D → Prop) (n+1)) = (GoodP S : world(D → Prop) n) := by
  show World.restrictStep (loeb (GoodPBody S)) = loeb (GoodPBody S)
  rw [restrictStep_loeb_eq_loeb_restrictStep (GoodPBody_natural S)]
  rfl

/-- `goodP_holds d` says the predicate holds at every sub-level. -/
noncomputable def goodP_holds (S : Nat) {n : Nat} (d : D n) : Prop :=
  ∀ m (hm : m ≤ n), (GoodP S : world(D → Prop) n) m hm (World.restrict d hm)

/-- Iterated GoodP restrict: `W.restrict (GoodP S : world n) hm = GoodP S : world m`. -/
theorem GoodP_restrict (S : Nat) : ∀ {n m : Nat} (hm : m ≤ n),
    @World.restrict (world(D → Prop)) _ n m (GoodP S : world(D → Prop) n) hm
    = (GoodP S : world(D → Prop) m) := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    rw [@World.restrict_self (world(D → Prop))]
  | succ n' ih =>
    intro m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [@World.restrict_self (world(D → Prop))]
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      rw [heq, @World.restrict_succ (world(D → Prop))]
      rw [GoodP_restrictStep]
      exact ih hm'

/-- `W.restrict (Later.next (loeb (GoodPBody S))) at Later world(...) (k+1) =
    GoodP S at level k`. -/
theorem Later_next_GoodP_restrict (S : Nat) {n k : Nat} (hk : k + 1 ≤ n) :
    World.restrict (Later.next (loeb (GoodPBody S) : world(D → Prop) n)) hk
    = (GoodP S : world(D → Prop) k) := by
  cases n with
  | zero => omega
  | succ n' =>
    have hk' : k ≤ n' := Nat.le_of_succ_le_succ hk
    have h1 : (Later.next (loeb (GoodPBody S)) : Later world(D → Prop) (n'+1))
            = World.restrictStep (loeb (GoodPBody S)) := rfl
    rw [h1]
    rw [@World.restrict_Later_eq (world(D → Prop)) _ n' k _ hk]
    rw [restrictStep_loeb_eq_loeb_restrictStep (GoodPBody_natural S)]
    show World.restrict (loeb (GoodPBody S)) hk' = _
    exact GoodP_restrict S hk'

/-- Closure under `restrictStep`. -/
theorem goodP_holds_closed (S : Nat) {n : Nat} (d : D (n+1))
    (hd : goodP_holds S d) : goodP_holds S (World.restrictStep d) := by
  intro m hm
  have h1 := hd m (Nat.le_succ_of_le hm)
  rw [World.restrict_succ d hm] at h1
  rw [← GoodP_restrictStep]
  exact h1

/-- `goodP S` packaged as a `World.Pred D`, parameterised by the initial step
    count `S` for the outer trace. Pick `S=0` for "starts visibly" traces;
    larger `S` allows more initial invis (still bounded by NCI's reset budget
    of 2 on every visible step). -/
noncomputable def goodP (S : Nat) : World.Pred D :=
  World.Pred.ofClosed (fun {n} (d : D n) => goodP_holds S d) (goodP_holds_closed S)

theorem goodP_iff (S : Nat) {n : Nat} (d : D n) :
    (goodP S).holds d ↔ goodP_holds S d :=
  World.Pred.ofClosed_holds _ _ d

/-! ## Forgetful map: `TraceGoodP 2 → NCI 2` -/

theorem TraceGoodP_implies_NCI (S : Nat) :
    ∀ (m' : Nat) {n : Nat} (RetGoodP : world(VH → Prop) n)
      (m : Nat) (hm : m ≤ n) (steps : Nat) (hm' : m' ≤ m) (t : T VH m'),
      TraceGoodP S RetGoodP m hm steps m' hm' t → NCI S steps m' t := by
  intro m'
  induction m' with
  | zero => intro _ _ _ _ _ _ _ _; unfold NCI; trivial
  | succ k ih =>
    intro n RetGoodP m hm steps hm' t htg
    unfold NCI
    unfold TraceGoodP at htg
    rw [loeb.eq (TraceGoodPBody_natural S)] at htg
    cases hu : T.unfold t with
    | ret _ => trivial
    | step ev tl =>
      rw [TraceGoodPBody_step_eq S RetGoodP (Nat.le_refl _)
            (Later.next (loeb (TraceGoodPBody S RetGoodP))) hm steps hm' t ev tl hu] at htg
      simp only [hu]
      simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                 World.Function.restrictStep_eq, World.Const.restrictStep_eq,
                 Later.Function.restrict_apply] at htg
      have hkn : k ≤ n := Nat.le_of_succ_le (Nat.le_trans hm' hm)
      have h_bridge : World.restrict (Later.next (loeb (TraceGoodPBody S RetGoodP)))
                        (Nat.le_trans hm' hm)
                    = TraceGoodP S (World.restrict RetGoodP hkn) :=
        Later_next_loeb_restrict S RetGoodP (Nat.le_trans hm' hm)
      rw [h_bridge] at htg
      exact ih (n := k) (World.restrict RetGoodP hkn) k (Nat.le_refl _) S (Nat.le_refl _) tl htg
    | invis dl =>
      cases steps with
      | zero =>
        rw [TraceGoodPBody_invis_zero S RetGoodP (Nat.le_refl _)
              (Later.next (loeb (TraceGoodPBody S RetGoodP))) hm hm' t dl hu] at htg
        exact htg.elim
      | succ j =>
        rw [TraceGoodPBody_invis_eq S RetGoodP (Nat.le_refl _)
              (Later.next (loeb (TraceGoodPBody S RetGoodP))) hm j hm' t dl hu] at htg
        simp only [hu]
        obtain ⟨_, h_rec⟩ := htg
        simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                   World.Function.restrictStep_eq, World.Const.restrictStep_eq,
                   Later.Function.restrict_apply] at h_rec
        have hkn : k ≤ n := Nat.le_of_succ_le (Nat.le_trans hm' hm)
        have h_bridge : World.restrict (Later.next (loeb (TraceGoodPBody S RetGoodP)))
                          (Nat.le_trans hm' hm)
                      = TraceGoodP S (World.restrict RetGoodP hkn) :=
          Later_next_loeb_restrict S RetGoodP (Nat.le_trans hm' hm)
        rw [h_bridge] at h_rec
        exact ih (n := k) (World.restrict RetGoodP hkn) k (Nat.le_refl _) j (Nat.le_refl _) dl h_rec

end NewIdea

open NewIdea

/-! ## `LR.good` — using the loeb-based `goodP` -/

/-- The logical relation packaged as an `LR ByNeed.D`. Field proofs sorried
    pending full proof of each closure law against the `loeb`-style `goodP`
    (which unfolds to `TraceGoodP (RetGoodP Recur) …` after `loeb.eq`). -/
noncomputable def good : LR D where
  P := goodP 2
  stuck := by
    intro n
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP 2 : world(D → Prop) n) m hm (World.restrict (D.stuck : D n) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq (NewIdea.GoodPBody_natural 2)]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.stuck, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq (NewIdea.TraceGoodPBody_natural 2)]
    rw [NewIdea.TraceGoodPBody_ret_eq 2 _ _ _ _ _ _ _ _
        (by unfold T.ret; rw [T_uf] : T.unfold (T.ret _) = .ret _)]
    rw [NewIdea.RetGoodP_apply]
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [Value_F_Rep_restrict_stuck] at hg
      nomatch hg
    · intro K ds hg
      rw [Value_F_Rep_restrict_stuck] at hg
      nomatch hg
    · simp only [World.restrict_self]
      exact h_heap
  step := by
    intro n ev d h_goodP
    rw [NewIdea.goodP_iff]
    intro m hm
    show (NewIdea.GoodP 2 : world(D → Prop) n) m hm
      (World.restrict (D.step ev (Later.next d)) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq (NewIdea.GoodPBody_natural 2)]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D_step_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq (NewIdea.TraceGoodPBody_natural 2)]
    rw [NewIdea.TraceGoodPBody_step_eq 2 _ _ _ _ _ _ _ _ _
        (by unfold T.step; rw [T_uf] : T.unfold (T.step _ _) = .step _ _)]
    cases m with
    | zero => trivial
    | succ k =>
      simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                 World.restrict_self, World.Const.restrictStep_eq]
      rw [restrictStep_loeb_eq_loeb_restrictStep (NewIdea.TraceGoodPBody_natural 2),
          NewIdea.TraceGoodPBody_restrictStep_RetGoodP,
          NewIdea.RetGoodP_restrictStep]
      have hk : k ≤ n := Nat.le_of_succ_le hm
      have h_recur_step : World.restrictStep _Recur_m
                       = World.restrict (Later.next (loeb (NewIdea.GoodPBody 2))) hk :=
        World.restrictStep_restrict' (Later.next (loeb (NewIdea.GoodPBody 2))) hm hk
      rw [h_recur_step]
      -- Strategy: at this point the goal is
      --   loeb (TGB (RetGoodP (W.restrict (Later.next loeb) hk))) k _ 2 k _ tl_k
      -- where tl_k = Later.hmap (k+1) ... (W.restrict (Later.next d) hm).
      -- This matches h_goodP at sub-level k after applying GoodPBody. The
      -- remaining gap is showing Param.Heap holds for the restricted heap.
      sorry
  fn := by
    intro n f h_param
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP 2 : world(D → Prop) n) m hm
      (World.restrict (Domain.fn' f) hm)
    show (NewIdea.GoodP 2 : world(D → Prop) n) m hm
      (World.restrict (D.fn f) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq (NewIdea.GoodPBody_natural 2)]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.fn, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq (NewIdea.TraceGoodPBody_natural 2)]
    rw [NewIdea.TraceGoodPBody_ret_eq 2 _ _ _ _ _ _ _ _
        (by unfold T.ret; rw [T_uf] : T.unfold (T.ret _) = .ret _)]
    rw [NewIdea.RetGoodP_apply]
    refine ⟨?_, ?_, ?_⟩
    · -- function-cond: from hg, extract that g equals our restricted version.
      sorry
    · -- con-cond: vacuous (v has shape Sum.inr (Sum.inl _), not Sum.inr (Sum.inr _))
      intro K ds hg
      obtain ⟨g', hg'⟩ := Value_F_Rep_restrict_fn_shape _ hm
      rw [hg'] at hg
      nomatch hg
    · simp only [World.restrict_self]
      exact h_heap
  con := by
    intro n K ds h_param
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP 2 : world(D → Prop) n) m hm
      (World.restrict (Domain.con' K ds) hm)
    show (NewIdea.GoodP 2 : world(D → Prop) n) m hm
      (World.restrict (D.con K ds) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq (NewIdea.GoodPBody_natural 2)]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.con, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq (NewIdea.TraceGoodPBody_natural 2)]
    rw [NewIdea.TraceGoodPBody_ret_eq 2 _ _ _ _ _ _ _ _
        (by unfold T.ret; rw [T_uf] : T.unfold (T.ret _) = .ret _)]
    rw [NewIdea.RetGoodP_apply]
    refine ⟨?_, ?_, ?_⟩
    · -- function-cond: vacuous (v has shape Sum.inr (Sum.inr _), not Sum.inr (Sum.inl _))
      intro g hg
      obtain ⟨ds', hds'⟩ := Value_F_Rep_restrict_con_shape K (ds.map Later.next) hm
      rw [hds'] at hg
      nomatch hg
    · -- con-cond: derive from Parametric.Con hypothesis
      sorry
    · simp only [World.restrict_self]
      exact h_heap
  app_closed := by sorry
  case_closed := by sorry
  bind_closed := by sorry

/-! ## Main theorems -/

private theorem emptyEnv_good (n : Nat) : good.env (Env.empty : Env (D n)) :=
  good.env_empty

/-- Every trace produced by `evalByNeed` has at most 2 consecutive invisible
    steps. -/
theorem evalByNeed_noTripleInvis (n : Nat) (e : Exp) :
    NoTripleInvis n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) := by
  have h_goodP : (goodP 2).holds (eval (D := D) e n (Nat.le_refl n) Env.empty) :=
    LR.fundamental good e Env.empty (emptyEnv_good n)
  have h_holds := (NewIdea.goodP_iff 2 _).mp h_goodP
  unfold NewIdea.goodP_holds at h_holds
  have h_n := h_holds n (Nat.le_refl n)
  rw [show World.restrict (eval (D := D) e n (Nat.le_refl n) Env.empty) (Nat.le_refl n)
        = eval (D := D) e n (Nat.le_refl n) Env.empty from World.restrict_self _] at h_n
  show NCI 2 2 n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅)
  unfold NewIdea.GoodP at h_n
  have hloeb : (loeb (NewIdea.GoodPBody 2) : world(D → Prop) n)
             = NewIdea.GoodPBody 2 n (Nat.le_refl _) (Later.next (loeb (NewIdea.GoodPBody 2))) :=
    loeb.eq (NewIdea.GoodPBody_natural 2)
  rw [hloeb] at h_n
  have h_emp : NewIdea.Parametric.Heap
      (Later.next (loeb (NewIdea.GoodPBody 2)) : ▹ world(D → Prop) n)↓
      (∅ : Heap (▹ D) n) := by
    intro a dl h
    rw [HashMap_get?_empty] at h; nomatch h
  have h_tg := h_n ∅ h_emp
  rw [show World.restrict (∅ : Heap (▹ D) n) (Nat.le_refl n) = ∅ from World.restrict_self _] at h_tg
  show NCI 2 2 n (((eval (D := D) e n (Nat.le_refl n) Env.empty).unfold n (Nat.le_refl n) ∅))
  exact NewIdea.TraceGoodP_implies_NCI 2 _ _ _ _ _ _ _ h_tg

private theorem Env_empty_find?_none {V : Type} (x : Var) :
    (Env.empty : Env V).find? x = none := by
  unfold Env.find? Env.empty; exact HashMap_get?_empty x

private theorem StartsVisible_of_ret {n : Nat} (v : VH n) :
    StartsVisible n (T.ret v) := by
  cases n with
  | zero => trivial
  | succ k =>
    show match T.unfold (T.ret v) with | .ret _ => True | .step _ _ => True | .invis _ => False
    unfold T.ret; rw [T_uf]; trivial

private theorem StartsVisible_of_step {n : Nat} (ev : Event) (tl : Later (T VH) n) :
    StartsVisible n (T.step ev tl) := by
  cases n with
  | zero => trivial
  | succ k =>
    show match T.unfold (T.step ev tl) with | .ret _ => True | .step _ _ => True | .invis _ => False
    unfold T.step; rw [T_uf]; trivial

/-- The trace of `evalByNeed n e` starts visibly. Proven directly by case
    analysis on `e`: every `eval` result has a `.ret` or `.step` at the top. -/
theorem evalByNeed_startsVisible (n : Nat) (e : Exp) :
    StartsVisible n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) := by
  unfold evalByNeed
  cases e with
  | ref x =>
    simp only [eval, Env_empty_find?_none]
    show StartsVisible _ ((D.stuck : D n).unfold _ _ _)
    unfold D.stuck; rw [D_ret_eq]; exact StartsVisible_of_ret _
  | conapp K xs =>
    simp only [eval]
    cases h : (Env.empty : Env (D n)).pmapList xs with
    | none =>
      simp only [h]
      show StartsVisible _ ((D.stuck : D n).unfold _ _ _)
      unfold D.stuck; rw [D_ret_eq]; exact StartsVisible_of_ret _
    | some ds =>
      simp only [h]
      show StartsVisible _ ((Domain.con' K ds : D n).unfold _ _ _)
      unfold Domain.con'
      show StartsVisible _ ((D.con K ds : D n).unfold _ _ _)
      unfold D.con D.ret; rw [D_fold_unfold]
      exact StartsVisible_of_ret _
  | lam x body =>
    simp only [eval]
    show StartsVisible _ ((Domain.fn' _ : D n).unfold _ _ _)
    unfold Domain.fn'
    show StartsVisible _ ((D.fn _ : D n).unfold _ _ _)
    unfold D.fn D.ret; rw [D_fold_unfold]
    exact StartsVisible_of_ret _
  | app e₁ x =>
    simp only [eval, Env_empty_find?_none]
    show StartsVisible _ ((D.stuck : D n).unfold _ _ _)
    unfold D.stuck; rw [D_ret_eq]; exact StartsVisible_of_ret _
  | case' eₛ alts =>
    simp only [eval]
    show StartsVisible _ ((Domain.step' .case1 _ : D n).unfold _ _ _)
    unfold Domain.step'
    show StartsVisible _ ((D.step .case1 _ : D n).unfold _ _ _)
    rw [D_step_eq]; exact StartsVisible_of_step _ _
  | let' x e₁ e₂ =>
    simp only [eval]
    show StartsVisible _ ((Domain.step' .let1 _ : D n).unfold _ _ _)
    unfold Domain.step'
    show StartsVisible _ ((D.step .let1 _ : D n).unfold _ _ _)
    rw [D_step_eq]; exact StartsVisible_of_step _ _

end ByNeed
