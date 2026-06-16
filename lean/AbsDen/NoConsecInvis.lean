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

/-- `W.restrict (Value.F.toRep _ (.fn g)) hm` is `Sum.inr (Sum.inl (W.restrict g hm))`. -/
theorem Value_F_Rep_restrict_fn_eq : ∀ {n : Nat} (g : World.Function (▹ D) (▹ D) n)
    {m : Nat} (hm : m ≤ n),
    World.restrict (Value.F.toRep (▹ D) (.fn g)) hm = Sum.inr (Sum.inl (World.restrict g hm)) := by
  intro n
  induction n with
  | zero =>
    intro g m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    rw [@World.restrict_self (Value.F.Rep (▹ D))]
    rw [@World.restrict_self (World.Function (▹ D) (▹ D))]
    rfl
  | succ n' ih =>
    intro g m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [@World.restrict_self (Value.F.Rep (▹ D))]
      rw [@World.restrict_self (World.Function (▹ D) (▹ D))]
      rfl
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      have hg_eq : World.restrict g hm
                 = World.restrict (World.restrictStep g) hm' := by
        rw [heq]
        exact @World.restrict_succ (World.Function (Later D) (Later D)) _ n' m g hm'
      rw [hg_eq]
      rw [heq, @World.restrict_succ (Value.F.Rep (▹ D))]
      have hstep' : (@World.restrictStep (Value.F.Rep (▹ D)) _ n' (Value.F.toRep _ (.fn g))
                  : Value.F.Rep (▹ D) n')
                 = Value.F.toRep _ (.fn (World.restrictStep g)) := rfl
      rw [hstep']
      exact ih (World.restrictStep g) hm'

/-- `W.restrict (Value.F.toRep _ (.fn g)) hm` matches `Sum.inr (Sum.inl _)` shape. -/
theorem Value_F_Rep_restrict_fn_shape {n : Nat} (g : World.Function (▹ D) (▹ D) n)
    {m : Nat} (hm : m ≤ n) :
    ∃ g', World.restrict (Value.F.toRep (▹ D) (.fn g)) hm = Sum.inr (Sum.inl g') :=
  ⟨_, Value_F_Rep_restrict_fn_eq g hm⟩

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

/-- `NCI` is monotone in its current-budget argument: more initial budget allows
    everything the smaller budget did. -/
theorem NCI_mono (S : Nat) : ∀ {k₁ k₂ : Nat} (_ : k₁ ≤ k₂) (n : Nat) (t : T VH n),
    NCI S k₁ n t → NCI S k₂ n t := by
  intro k₁ k₂ hk n
  induction n generalizing k₁ k₂ with
  | zero => intro t _; unfold NCI; trivial
  | succ n' ih =>
    intro t h
    unfold NCI at h ⊢
    cases hu : T.unfold t with
    | ret _ => trivial
    | step _ dl =>
      simp only [hu] at h ⊢
      exact ih (Nat.le_refl S) dl h
    | invis dl =>
      simp only [hu] at h ⊢
      cases k₁ with
      | zero => exact h.elim
      | succ j₁ =>
        cases k₂ with
        | zero => omega
        | succ j₂ => exact ih (by omega : j₁ ≤ j₂) dl h

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
  ∀ m (_ : m ≤ n) (a : Addr) (dl : ▹ D m), Std.HashMap.get? (μ↓) a = some dl →
    Later.prop (Later.ap' _ (P↓) dl)

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

/-- `Param.Heap` is naturally closed under `restrictStep`: the all-sub-levels
    formulation lets us simply specialize the input at the lower bound. -/
theorem Parametric.Heap_restrictStep {n : Nat}
    (P : Later world(D → Prop) (n+1)) (μ : ByNeed.Heap (Later D) (n+1))
    (hμ : Parametric.Heap P μ) :
    Parametric.Heap (World.restrictStep P) (World.restrictStep μ) := by
  intro m hm a dl h_get
  have hm1 : m ≤ n+1 := Nat.le_succ_of_le hm
  have h_eq_μ : @World.restrict (ByNeed.Heap (Later D)) _ n m (World.restrictStep μ) hm
              = @World.restrict (ByNeed.Heap (Later D)) _ (n+1) m μ hm1 :=
    (World.restrict_succ μ hm).symm
  have h_eq_P : @World.restrict (Later (World.Function D (World.Const Prop))) _ n m
                  (World.restrictStep P) hm
              = @World.restrict (Later (World.Function D (World.Const Prop))) _ (n+1) m P hm1 :=
    (World.restrict_succ P hm).symm
  rw [h_eq_μ] at h_get
  rw [h_eq_P]
  exact hμ m hm1 a dl h_get

/-- The body of `TraceGoodP`'s `loeb`. Restricts the outer `Recur` to the
    trace level `m` *first*, then applies `Later.ap'` at level `m`. This makes
    the body Kripke-natural across outer levels: the body's value at the
    trace level depends only on `Recur↓` (which is restrict-stable). -/
def TraceGoodPBody {N : Nat} (RetGoodP : world(VH → Prop) N) :
    World.Function (Later world(Nat → T VH → Prop)) world(Nat → T VH → Prop) N :=
  fun n _ Recur _ _ steps m _ t =>
    let Recur (k : Nat) : Later world(T VH → Prop) m :=
      Later.ap' m (Recur↓) (Later.next k)
    match t.unfold with
    | .ret v => RetGoodP _ (by omega) v
    | .step _ tl =>
      Later.prop (Later.ap' m (Recur 2) tl)
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
def TraceGoodP {n : Nat} (RetGoodP : world(VH → Prop) n) :
    world(Nat → T VH → Prop) n :=
  loeb (TraceGoodPBody RetGoodP)

/-- `TraceGoodPBody` is Kripke-natural. Body uses `Recur↓` (restricted) — so
    the value depends only on `W.restrict Recur (m ≤ n)`, which by
    `World.restrict_succ` is invariant under the outer restriction. -/
theorem TraceGoodPBody_natural {N : Nat} {RetGoodP : world(VH → Prop) N} :
    (TraceGoodPBody RetGoodP).Natural := by
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
theorem TraceGoodPBody_ret_eq {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (steps : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (v : VH k)
    (hu : T.unfold t = .ret v) :
  TraceGoodPBody RetGoodP n hn Recur m hm steps k hk t
  = RetGoodP k (Nat.le_trans hk (Nat.le_trans hm hn)) v := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.step` case, as a rewritable equation. `.step` refreshes the
    budget to `2` (the hard-coded reset value). -/
theorem TraceGoodPBody_step_eq {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (steps : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (ev : Event) (tl : Later (T VH) k)
    (hu : T.unfold t = .step ev tl) :
  TraceGoodPBody RetGoodP n hn Recur m hm steps k hk t
  = ▷(Later.ap' k
       (Later.ap' k (World.restrict Recur (Nat.le_trans hk hm))
         (Later.next (2 : Nat))) tl) := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.invis` case at `steps = j+1`. -/
theorem TraceGoodPBody_invis_eq {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) (j : Nat) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (dl : Later (T VH) k)
    (hu : T.unfold t = .invis dl) :
  TraceGoodPBody RetGoodP n hn Recur m hm (j+1) k hk t
  = ((▷(Later.map NotRet k dl) ∨ ▷(Later.map IsRetStuck k dl)) ∧
     ▷(Later.ap' k
        (Later.ap' k (World.restrict Recur (Nat.le_trans hk hm)) (Later.next j)) dl)) := by
  unfold TraceGoodPBody
  rw [hu]

/-- The body's `.invis` case at `steps = 0` is `False`. -/
theorem TraceGoodPBody_invis_zero {N : Nat} (RetGoodP : world(VH → Prop) N)
    {n : Nat} (hn : n ≤ N) (Recur : Later world(Nat → T VH → Prop) n)
    {m : Nat} (hm : m ≤ n) {k : Nat} (hk : k ≤ m) (t : T VH k)
    (dl : Later (T VH) k)
    (hu : T.unfold t = .invis dl) :
  TraceGoodPBody RetGoodP n hn Recur m hm (0 : Nat) k hk t = False := by
  unfold TraceGoodPBody
  rw [hu]

/-- `restrictStep (TraceGoodPBody RetGoodP) = TraceGoodPBody (restrictStep RetGoodP)`. -/
theorem TraceGoodPBody_restrictStep_RetGoodP {N : Nat}
    (RetGoodP : world(VH → Prop) (N+1)) :
    World.restrictStep (TraceGoodPBody RetGoodP)
      = TraceGoodPBody (World.restrictStep RetGoodP) := by
  rfl

/-- `restrictStep` of `TraceGoodP` is `TraceGoodP` of `restrictStep RetGoodP`. -/
theorem TraceGoodP_restrictStep {n : Nat} (RetGoodP : world(VH → Prop) (n+1)) :
    World.restrictStep (TraceGoodP RetGoodP) = TraceGoodP (World.restrictStep RetGoodP) := by
  show World.restrictStep (loeb (TraceGoodPBody RetGoodP))
     = loeb (TraceGoodPBody (World.restrictStep RetGoodP))
  rw [restrictStep_loeb_eq_loeb_restrictStep TraceGoodPBody_natural]
  rw [TraceGoodPBody_restrictStep_RetGoodP]

/-- Iterated: `W.restrict (TraceGoodP RetGoodP) hm = TraceGoodP (W.restrict RetGoodP hm)`. -/
theorem TraceGoodP_restrict : ∀ {n : Nat} (RetGoodP : world(VH → Prop) n)
    {m : Nat} (hm : m ≤ n),
    World.restrict (TraceGoodP RetGoodP) hm = TraceGoodP (World.restrict RetGoodP hm) := by
  intro n
  induction n with
  | zero =>
    intro RetGoodP m hm
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    rw [show World.restrict (TraceGoodP RetGoodP) hm = TraceGoodP RetGoodP from
        World.restrict_self _]
    rw [show World.restrict RetGoodP hm = RetGoodP from World.restrict_self _]
  | succ n' ih =>
    intro RetGoodP m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [show World.restrict (TraceGoodP RetGoodP) hm = TraceGoodP RetGoodP from
          World.restrict_self _]
      rw [show World.restrict RetGoodP hm = RetGoodP from World.restrict_self _]
    · have hm' : m ≤ n' := by omega
      rw [show World.restrict (TraceGoodP RetGoodP) hm
           = World.restrict (World.restrictStep (TraceGoodP RetGoodP)) hm' by
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
theorem Later_next_loeb_restrict {n : Nat} (RetGoodP : world(VH → Prop) n)
    {k : Nat} (hk : k + 1 ≤ n) :
    World.restrict (Later.next (loeb (TraceGoodPBody RetGoodP))) hk
    = TraceGoodP (World.restrict RetGoodP (Nat.le_of_succ_le hk)) := by
  cases n with
  | zero => omega
  | succ n' =>
    have hk' : k ≤ n' := Nat.le_of_succ_le_succ hk
    have h1 : (Later.next (loeb (TraceGoodPBody RetGoodP)) :
                Later (world(Nat → T VH → Prop)) (n'+1))
            = World.restrictStep (loeb (TraceGoodPBody RetGoodP)) := rfl
    rw [h1, restrictStep_loeb_eq_loeb_restrictStep TraceGoodPBody_natural,
        TraceGoodPBody_restrictStep_RetGoodP]
    have h2 : loeb (TraceGoodPBody (World.restrictStep RetGoodP))
            = TraceGoodP (World.restrictStep RetGoodP) := rfl
    rw [h2]
    rw [@World.restrict_Later_eq (world(Nat → T VH → Prop))]
    rw [TraceGoodP_restrict]
    congr 1
    exact (World.restrict_succ RetGoodP hk').symm

/-- Look-shape of a `▹ D`: at the next level, `dl` is `step' (.look x) d'`.
    Vacuously true at level 0. -/
def IsLookShape : {n : Nat} → ▹ D n → Prop
  | 0,   _  => True
  | _+1, dl => ∃ (x : Var) (d' : D _), (dl : D _) = Domain.step' (.look x) d'

/-- The value-and-heap predicate for `.ret`, parameterised by the
    later-`GoodP`-style predicate on `D`-values. Function- and con-fields
    are `▷ DGoodP`-good (i.e., `IsLookup`-shape); the heap is
    `Parametric.Heap (DGoodP↓)`-good. -/
def RetGoodP {n : Nat} (DGoodP : Nat → ▹ world(D → Prop) n) : world(VH → Prop) n :=
  fun m _ (v, μ) =>
    -- Function-value condition.
    (∀ (g : World.Function (Later D) (Later D) m),
      v = .inr (.inl g) →
      ∀ l (hl : l ≤ m) (dl : ▹ D l),
        Later.prop (Later.ap' _ ((DGoodP 2)↓) dl) →
        IsLookShape dl →
        ∀ j (hj : j ≤ l) (μ' : Heap (▹ D) j),
          Parametric.Heap ((DGoodP 1)↓) μ' →
          Later.prop (Later.ap' _ ((DGoodP 2)↓) (g l hl dl))) ∧
    -- Constructor-field condition.
    (∀ (K : ConTag) (ds : List (▹ D m)),
      v = .inr (.inr (K, ds)) →
      ∀ (dl : ▹ D m), dl ∈ ds → Later.prop (Later.ap' _ ((DGoodP 2)↓) dl)) ∧
    -- Heap-good condition.
    Parametric.Heap ((DGoodP 2)↓) μ

/-- `RetGoodP` applied at the `.ret`-style payload `(v, μ)`. -/
theorem RetGoodP_apply {n : Nat} (DGoodP : Nat → ▹ world(D → Prop) n)
    (m : Nat) (hm : m ≤ n) (v : Value.F.Rep (▹ D) m) (μ : Heap (▹ D) m) :
    RetGoodP DGoodP m hm (v, μ)
    = ((∀ (g : World.Function (Later D) (Later D) m),
          v = .inr (.inl g) →
          ∀ l (hl : l ≤ m) (dl : ▹ D l),
            Later.prop (Later.ap' _ ((DGoodP 2)↓) dl) →
            IsLookShape dl →
            ∀ j (hj : j ≤ l) (μ' : Heap (▹ D) j),
              Parametric.Heap ((DGoodP 1)↓) μ' →
              Later.prop (Later.ap' _ ((DGoodP 2)↓) (g l hl dl))) ∧
       (∀ (K : ConTag) (ds : List (▹ D m)),
          v = .inr (.inr (K, ds)) →
          ∀ (dl : ▹ D m), dl ∈ ds → Later.prop (Later.ap' _ ((DGoodP 2)↓) dl)) ∧
       Parametric.Heap ((DGoodP 2)↓) μ) := rfl

/-- The body of `GoodP`'s `loeb`. The outer trace's initial step count is
    threaded through as the `world(Nat → ...)` argument `steps`; the inner
    `Recur (k)` projector picks heap entries at `k=1` (NCI 1: at most one
    invis at start) and function/con-fields at `k=2` (NCI 2). -/
def GoodPBody {N : Nat} : World.Function (Later world(Nat → D → Prop)) world(Nat → D → Prop) N :=
  fun n _ Recur _ _ steps m _ d =>
    let Recur (k : Nat) : Later world(D → Prop) m :=
      Later.ap' _ (Recur↓) (Later.next k)
    ∀ μ : Heap (▹ D) m, Parametric.Heap (Recur 1) μ →
      TraceGoodP (RetGoodP Recur) m (Nat.le_refl _) steps m (Nat.le_refl _)
        (d.unfold m (Nat.le_refl _) (μ↓))

/-- The value-level "good" predicate, parameterised over an initial step count
    by the `world(Nat → ...)` shape. -/
def GoodP {n : Nat} : world(Nat → D → Prop) n :=
  loeb GoodPBody

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
theorem GoodPBody_natural {N : Nat} :
    (GoodPBody : World.Function _ _ N).Natural := by
  intro m hm x
  funext m_body hm_body steps m'_body hm'_body d
  simp only [World.Function.restrictStep_eq]
  unfold GoodPBody
  rw [World.restrict_succ x (Nat.le_trans hm'_body hm_body)]

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

/-- `RetGoodP` commutes with `restrictStep` on its `DGoodP` argument
    (pointwise on the Nat parameter). -/
theorem RetGoodP_restrictStep {n : Nat} (DGoodP : Nat → ▹ world(D → Prop) (n+1)) :
    World.restrictStep (RetGoodP DGoodP : world(VH → Prop) (n+1))
    = RetGoodP (fun k => World.restrictStep (DGoodP k)) := by
  funext m hm vμ
  obtain ⟨v, μ⟩ := vμ
  show RetGoodP DGoodP m (Nat.le_succ_of_le hm) (v, μ)
     = RetGoodP (fun k => World.restrictStep (DGoodP k)) m hm (v, μ)
  unfold RetGoodP
  dsimp only []
  -- Equational lemma for W.restrict (DGoodP k) at any sub-level.
  have key_m : ∀ (k : Nat),
        World.restrict (F := Later world(D → Prop)) (DGoodP k)
                  (Nat.le_succ_of_le hm)
              = World.restrict (World.restrictStep (DGoodP k)) hm :=
    fun k => World.restrict_le_succ (DGoodP k) _ hm
  refine (congrArg (· ∧ _) ?_).trans ((congrArg (_ ∧ ·) ?_))
  · -- Function-cond piece.
    apply propext
    refine Iff.intro (fun h g hg l hl dl hdl hlook j hj μ' hμ' => ?_)
                    (fun h g hg l hl dl hdl hlook j hj μ' hμ' => ?_)
    · have hl_n : l ≤ n := Nat.le_trans hl hm
      have hj_n : j ≤ n := Nat.le_trans hj hl_n
      have h_eq_l : ∀ (k : Nat), World.restrict (F := Later world(D → Prop)) (DGoodP k)
                      (Nat.le_trans hl (Nat.le_succ_of_le hm))
                  = World.restrict (World.restrictStep (DGoodP k)) hl_n :=
        fun k => World.restrict_le_succ (DGoodP k) _ hl_n
      have h_eq_j : ∀ (k : Nat), World.restrict (F := Later world(D → Prop)) (DGoodP k)
                      (Nat.le_trans hj (Nat.le_trans hl (Nat.le_succ_of_le hm)))
                  = World.restrict (World.restrictStep (DGoodP k)) hj_n :=
        fun k => World.restrict_le_succ (DGoodP k) _ hj_n
      rw [← h_eq_l 2] at hdl
      have := h g hg l hl dl hdl hlook j hj μ' (by rw [h_eq_j 1]; exact hμ')
      rwa [h_eq_l 2] at this
    · have hl_n : l ≤ n := Nat.le_trans hl hm
      have hj_n : j ≤ n := Nat.le_trans hj hl_n
      have h_eq_l : ∀ (k : Nat), World.restrict (F := Later world(D → Prop)) (DGoodP k)
                      (Nat.le_trans hl (Nat.le_succ_of_le hm))
                  = World.restrict (World.restrictStep (DGoodP k)) hl_n :=
        fun k => World.restrict_le_succ (DGoodP k) _ hl_n
      have h_eq_j : ∀ (k : Nat), World.restrict (F := Later world(D → Prop)) (DGoodP k)
                      (Nat.le_trans hj (Nat.le_trans hl (Nat.le_succ_of_le hm)))
                  = World.restrict (World.restrictStep (DGoodP k)) hj_n :=
        fun k => World.restrict_le_succ (DGoodP k) _ hj_n
      rw [h_eq_l 2] at hdl
      have := h g hg l hl dl hdl hlook j hj μ' (by rw [← h_eq_j 1]; exact hμ')
      rwa [← h_eq_l 2] at this
  · refine (congrArg (· ∧ _) ?_).trans ((congrArg (_ ∧ ·) ?_))
    · apply propext
      refine Iff.intro (fun h K ds heq dl hdl => ?_) (fun h K ds heq dl hdl => ?_)
      · have := h K ds heq dl hdl; rwa [← key_m 2]
      · have := h K ds heq dl hdl; rwa [key_m 2]
    · apply propext
      unfold Parametric.Heap
      refine Iff.intro (fun h a dl h_ => ?_) (fun h a dl h_ => ?_)
      · have := h a dl h_; rwa [← key_m 2]
      · have := h a dl h_; rwa [key_m 2]

/-- Iterated: `W.restrict` on `RetGoodP DGoodP` equals `RetGoodP` of the pointwise
    `W.restrict`-ed `DGoodP`. -/
theorem RetGoodP_restrict : ∀ {n : Nat} (DGoodP : Nat → ▹ world(D → Prop) n)
    {m : Nat} (hm : m ≤ n),
    World.restrict (RetGoodP DGoodP : world(VH → Prop) n) hm
    = RetGoodP (fun k => World.restrict (DGoodP k) hm) := by
  intro n
  induction n with
  | zero =>
    intro DGoodP m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) 0) hm
            = RetGoodP DGoodP from World.restrict_self _]
    congr
  | succ n' ih =>
    intro DGoodP m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) (n'+1)) hm
              = RetGoodP DGoodP from World.restrict_self _]
      congr 1
      funext k
      rw [show World.restrict (DGoodP k) hm = DGoodP k from World.restrict_self _]
    · have hm' : m ≤ n' := by omega
      rw [show World.restrict (RetGoodP DGoodP : world(VH → Prop) (n'+1)) hm
            = World.restrict (World.restrictStep (RetGoodP DGoodP)) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]
      rw [RetGoodP_restrictStep]
      rw [ih (fun k => World.restrictStep (DGoodP k)) hm']
      congr 1
      funext k
      rw [show World.restrict (DGoodP k) hm
            = World.restrict (World.restrictStep (DGoodP k)) hm' by
        show World.restrict _ hm = _
        rw [World.restrict.eq_1, dif_neg hmn]]

/-! ## `goodP : World.Pred D` — wrapping `GoodP` for `LR.good.P` -/

/-- `GoodP` at outer level `n+1`, restricted, equals `GoodP` at outer level `n`. -/
theorem GoodP_restrictStep {n : Nat} :
    World.restrictStep (GoodP : world(Nat → D → Prop) (n+1))
    = (GoodP : world(Nat → D → Prop) n) := by
  show World.restrictStep (loeb GoodPBody) = loeb GoodPBody
  rw [restrictStep_loeb_eq_loeb_restrictStep GoodPBody_natural]
  rfl

/-- `goodP_holds S d` says the predicate holds at every sub-level for the
    specified initial step count `S`. -/
noncomputable def goodP_holds (S : Nat) {n : Nat} (d : D n) : Prop :=
  ∀ m (hm : m ≤ n),
    (GoodP : world(Nat → D → Prop) n) m hm S m (Nat.le_refl _) (World.restrict d hm)

/-- Iterated GoodP restrict. -/
theorem GoodP_restrict : ∀ {n m : Nat} (hm : m ≤ n),
    @World.restrict (world(Nat → D → Prop)) _ n m
      (GoodP : world(Nat → D → Prop) n) hm
    = (GoodP : world(Nat → D → Prop) m) := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := Nat.le_zero.mp hm; subst this
    rw [@World.restrict_self (world(Nat → D → Prop))]
  | succ n' ih =>
    intro m hm
    by_cases hmn : m = n'+1
    · subst hmn
      rw [@World.restrict_self (world(Nat → D → Prop))]
    · have hm' : m ≤ n' := by omega
      have heq : hm = Nat.le_succ_of_le hm' := rfl
      rw [heq, @World.restrict_succ (world(Nat → D → Prop))]
      rw [GoodP_restrictStep]
      exact ih hm'

/-- `W.restrict (Later.next (loeb GoodPBody)) at Later world(...) (k+1) =
    GoodP at level k`. -/
theorem Later_next_GoodP_restrict {n k : Nat} (hk : k + 1 ≤ n) :
    World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hk
    = (GoodP : world(Nat → D → Prop) k) := by
  cases n with
  | zero => omega
  | succ n' =>
    have hk' : k ≤ n' := Nat.le_of_succ_le_succ hk
    have h1 : (Later.next (loeb GoodPBody) : Later world(Nat → D → Prop) (n'+1))
            = World.restrictStep (loeb GoodPBody) := rfl
    rw [h1]
    rw [@World.restrict_Later_eq (world(Nat → D → Prop)) _ n' k _ hk]
    rw [restrictStep_loeb_eq_loeb_restrictStep GoodPBody_natural]
    show World.restrict (loeb GoodPBody) hk' = _
    exact GoodP_restrict hk'

/-- Closure under `restrictStep`. -/
theorem goodP_holds_closed (S : Nat) {n : Nat} (d : D (n+1))
    (hd : goodP_holds S d) : goodP_holds S (World.restrictStep d) := by
  intro m hm
  have h1 := hd m (Nat.le_succ_of_le hm)
  rw [World.restrict_succ d hm] at h1
  -- h1 : (GoodP : world (n+1)) m (Nat.le_succ_of_le hm) S m _ (W.restrict (restrictStep d) hm)
  -- Goal: (GoodP : world n) m hm S m _ (W.restrict (restrictStep d) hm).
  -- By GoodP_restrictStep, (GoodP : world n) = restrictStep (GoodP : world (n+1)).
  rw [show (GoodP : world(Nat → D → Prop) n) = World.restrictStep GoodP from
        GoodP_restrictStep.symm]
  exact h1

/-- `goodP S` packaged as a `World.Pred D`, parameterised by the initial step
    count `S` for the outer trace. Pick `S=0` for "starts visibly" traces. -/
noncomputable def goodP (S : Nat) : World.Pred D :=
  World.Pred.ofClosed (fun {n} (d : D n) => goodP_holds S d) (goodP_holds_closed S)

theorem goodP_iff (S : Nat) {n : Nat} (d : D n) :
    (goodP S).holds d ↔ goodP_holds S d :=
  World.Pred.ofClosed_holds _ _ d

/-! ## `TraceGoodP` is monotone in its budget argument `steps`. -/

theorem TraceGoodP_mono_S :
    ∀ (m' : Nat) {n : Nat} (RetGoodP : world(VH → Prop) n)
      (m : Nat) (hm : m ≤ n) (S₁ S₂ : Nat) (hS : S₁ ≤ S₂)
      (hm' : m' ≤ m) (t : T VH m'),
      TraceGoodP RetGoodP m hm S₁ m' hm' t → TraceGoodP RetGoodP m hm S₂ m' hm' t := by
  intro m'
  induction m' with
  | zero =>
    intro n RetGoodP m hm S₁ S₂ hS hm' t hP
    unfold TraceGoodP at hP ⊢
    rw [loeb.eq TraceGoodPBody_natural] at hP ⊢
    cases hu : T.unfold t with
    | ret v =>
      rw [TraceGoodPBody_ret_eq RetGoodP (Nat.le_refl _) _ hm S₁ hm' t v hu] at hP
      rw [TraceGoodPBody_ret_eq RetGoodP (Nat.le_refl _) _ hm S₂ hm' t v hu]
      exact hP
    | step ev tl =>
      rw [TraceGoodPBody_step_eq RetGoodP (Nat.le_refl _) _ hm S₁ hm' t ev tl hu] at hP
      rw [TraceGoodPBody_step_eq RetGoodP (Nat.le_refl _) _ hm S₂ hm' t ev tl hu]
      -- ▷ at level 0 is True.
      trivial
    | invis dl =>
      cases S₁ with
      | zero =>
        rw [TraceGoodPBody_invis_zero RetGoodP (Nat.le_refl _) _ hm hm' t dl hu] at hP
        exact hP.elim
      | succ j₁ =>
        obtain ⟨j₂, hj₂⟩ : ∃ j₂, S₂ = j₂ + 1 := by
          cases S₂ with | zero => omega | succ j₂ => exact ⟨j₂, rfl⟩
        subst hj₂
        rw [TraceGoodPBody_invis_eq RetGoodP (Nat.le_refl _) _ hm j₂ hm' t dl hu]
        -- ▷ at level 0 is True for both halves.
        refine ⟨Or.inl ?_, ?_⟩ <;> trivial
  | succ k ih =>
    intro n RetGoodP m hm S₁ S₂ hS hm' t hP
    unfold TraceGoodP at hP ⊢
    rw [loeb.eq TraceGoodPBody_natural] at hP ⊢
    cases hu : T.unfold t with
    | ret v =>
      rw [TraceGoodPBody_ret_eq RetGoodP (Nat.le_refl _) _ hm S₁ hm' t v hu] at hP
      rw [TraceGoodPBody_ret_eq RetGoodP (Nat.le_refl _) _ hm S₂ hm' t v hu]
      exact hP
    | step ev tl =>
      rw [TraceGoodPBody_step_eq RetGoodP (Nat.le_refl _) _ hm S₁ hm' t ev tl hu] at hP
      rw [TraceGoodPBody_step_eq RetGoodP (Nat.le_refl _) _ hm S₂ hm' t ev tl hu]
      exact hP
    | invis dl =>
      cases S₁ with
      | zero =>
        rw [TraceGoodPBody_invis_zero RetGoodP (Nat.le_refl _) _ hm hm' t dl hu] at hP
        exact hP.elim
      | succ j₁ =>
        obtain ⟨j₂, hj₂⟩ : ∃ j₂, S₂ = j₂ + 1 := by
          cases S₂ with | zero => omega | succ j₂ => exact ⟨j₂, rfl⟩
        subst hj₂
        rw [TraceGoodPBody_invis_eq RetGoodP (Nat.le_refl _) _ hm j₁ hm' t dl hu] at hP
        rw [TraceGoodPBody_invis_eq RetGoodP (Nat.le_refl _) _ hm j₂ hm' t dl hu]
        obtain ⟨h_nr, h_rec⟩ := hP
        refine ⟨h_nr, ?_⟩
        simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                   World.Function.restrictStep_eq, World.Const.restrictStep_eq,
                   Later.Function.restrict_apply] at h_rec ⊢
        have hkn : k ≤ n := Nat.le_of_succ_le (Nat.le_trans hm' hm)
        have h_bridge : World.restrict (Later.next (loeb (TraceGoodPBody RetGoodP)))
                          (Nat.le_trans hm' hm)
                      = TraceGoodP (World.restrict RetGoodP hkn) :=
          Later_next_loeb_restrict RetGoodP (Nat.le_trans hm' hm)
        rw [h_bridge] at h_rec ⊢
        exact ih (n := k) (World.restrict RetGoodP hkn) k (Nat.le_refl _) j₁ j₂
                  (by omega) (Nat.le_refl _) dl h_rec

/-- Value-level monotonicity in budget: a `D`-value good at `S₁` is good at `S₂`
    when `S₁ ≤ S₂`. Closely mirrors `Param_Heap_GoodP_mono` but for a single
    `D`-value, not a whole heap. -/
theorem GoodP_S_mono {n m : Nat} (hm : m ≤ n) (d : D m) (S₁ S₂ : Nat) (hS : S₁ ≤ S₂)
    (h : (GoodP : world(Nat → D → Prop) n) m hm S₁ m (Nat.le_refl _) d) :
    (GoodP : world(Nat → D → Prop) n) m hm S₂ m (Nat.le_refl _) d := by
  unfold GoodP at h ⊢
  rw [loeb.eq GoodPBody_natural] at h ⊢
  intro μ h_heap
  exact TraceGoodP_mono_S _ _ _ _ S₁ S₂ hS _ _ (h μ h_heap)

/-- `Later.ap'` of the `Later.next loeb`-shape predicate commutes with
    `W.restrict`. Provable directly via `Later_next_GoodP_restrict` + body
    invariance of `GoodPBody` in `m_outer`. The right-hand side encodes the
    "restricted" predicate at the lower level. -/
theorem Later_ap'_W_restrict_GoodP {n : Nat} : ∀ {m m' : Nat}
    (hm : m ≤ n) (hm' : m' ≤ m) (S : Nat),
    @World.restrict (Later (World.Function D (World.Const Prop))) _ m m'
      (Later.ap' m
        (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
        (Later.next S)) hm'
    = Later.ap' m'
        (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n))
          (Nat.le_trans hm' hm))
        (Later.next S) := by
  intro m
  induction m with
  | zero =>
    intro m' hm hm' S
    have : m' = 0 := Nat.le_zero.mp hm'; subst this
    rfl
  | succ M ih =>
    intro m' hm hm' S
    by_cases hmn : m' = M+1
    · subst hmn
      rw [@World.restrict_self (Later (World.Function D (World.Const Prop))) _ (M+1)]
    · have hm'' : m' ≤ M := by omega
      have hM : M ≤ n := Nat.le_of_succ_le hm
      have heq : hm' = Nat.le_succ_of_le hm'' := rfl
      rw [heq, @World.restrict_succ (Later (World.Function D (World.Const Prop))) _ M m' _ hm'']
      -- W.restrictStep on Later.ap'_(M+1): commutes — TODO via the natural
      -- property of the inner predicate.
      have h_step : (World.restrictStep (Later.ap' (M+1)
                        (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
                        (Later.next S))
                    : Later (World.Function D (World.Const Prop)) M)
                  = Later.ap' M
                      (World.restrict (Later.next (loeb GoodPBody)) hM)
                      (Later.next S) := by
        cases M with
        | zero => rfl
        | succ K =>
          -- Both sides reduce to world(D → Prop) K. Compare pointwise.
          funext k' hk' d
          -- LHS k' hk' d = W.restrictStep applied to Later.ap' (K+2) result.
          -- By Later.ap'_succ + W.Function.restrictStep_eq, LHS reduces to
          -- f (K+1) _ S k' (Nat.le_succ_of_le hk') d where f = W.restrict (Later.next loeb) hm.
          -- RHS k' hk' d = Later.ap' (K+1) f' (Later.next S) at k' hk' d
          --              = f' K (Nat.le_refl K) S k' hk' d where f' = W.restrict (Later.next loeb) hM.
          -- By Later_next_GoodP_restrict, f = GoodP at K+1 and f' = GoodP at K.
          -- By GoodP_restrictStep + body invariance of GoodPBody, LHS = RHS.
          rw [Later_next_GoodP_restrict hm, Later_next_GoodP_restrict hM]
          -- Goal: W.restrictStep (Later.ap' (K+2) (GoodP at K+1) (Later.next S)) k' hk' d
          --     = Later.ap' (K+1) (GoodP at K) (Later.next S) k' hk' d.
          show World.restrictStep ((GoodP : world(Nat → D → Prop) (K+1)) (K+1)
                  (Nat.le_refl (K+1)) S) k' hk' d
              = (GoodP : world(Nat → D → Prop) K) K (Nat.le_refl K) S k' hk' d
          rw [show (GoodP : world(Nat → D → Prop) K)
                = World.restrictStep (GoodP : world(Nat → D → Prop) (K+1)) from
              GoodP_restrictStep.symm]
          -- Both sides now W.restrictStep on the same GoodP.
          show ((GoodP : world(Nat → D → Prop) (K+1)) (K+1) _ S) k' (Nat.le_succ_of_le hk') d
              = ((GoodP : world(Nat → D → Prop) (K+1)) K (Nat.le_succ_of_le (Nat.le_refl K)) S) k' hk' d
          -- By body invariance of GoodPBody in m_outer (the M_outer arg),
          -- (GoodP at K+1) M_outer _ S k' _ d is independent of M_outer.
          unfold GoodP
          rw [loeb.eq GoodPBody_natural]
          rfl
      rw [h_step]
      have h_proof : Nat.le_trans hm' hm = Nat.le_trans hm'' hM :=
        Subsingleton.elim _ _
      rw [h_proof]
      exact ih hM hm'' S

/-- `W.restrictStep` commutes with `Later.ap'` of the `W.restrict (Later.next loeb)`
    shape, giving the analogous predicate one level down. -/
theorem Later_ap'_W_restrictStep_GoodP {n M : Nat} (hm : M+1 ≤ n) (hM : M ≤ n) (S : Nat) :
    (World.restrictStep (Later.ap' (M+1)
        (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
        (Later.next S))
      : Later (World.Function D (World.Const Prop)) M)
    = Later.ap' M
        (World.restrict (Later.next (loeb GoodPBody)) hM)
        (Later.next S) := by
  cases M with
  | zero => rfl
  | succ K =>
    funext k' hk' d
    rw [Later_next_GoodP_restrict hm, Later_next_GoodP_restrict hM]
    show World.restrictStep ((GoodP : world(Nat → D → Prop) (K+1)) (K+1)
            (Nat.le_refl (K+1)) S) k' hk' d
        = (GoodP : world(Nat → D → Prop) K) K (Nat.le_refl K) S k' hk' d
    rw [show (GoodP : world(Nat → D → Prop) K)
          = World.restrictStep (GoodP : world(Nat → D → Prop) (K+1)) from
        GoodP_restrictStep.symm]
    show ((GoodP : world(Nat → D → Prop) (K+1)) (K+1) _ S) k' (Nat.le_succ_of_le hk') d
        = ((GoodP : world(Nat → D → Prop) (K+1)) K (Nat.le_succ_of_le (Nat.le_refl K)) S) k' hk' d
    unfold GoodP
    rw [loeb.eq GoodPBody_natural]
    rfl

/-- Bridge: a `▷((Recur S)↓ dl)` claim at outer level `k'+1` (where `Recur` is
    the `Later.ap'`-of-`Later.next-loeb` shape) unfolds to a `GoodP at k'`
    statement on `dl`. The `▷` strips, the outer `Later.ap'` becomes pointwise,
    and `Later.next loeb` restricted to `k'+1` is `GoodP at k'`. -/
theorem Later_ap'_Recur_succ_eq {n m : Nat} (hm : m ≤ n) (k' : Nat)
    (hl : k'+1 ≤ m) (S : Nat) (dl : ▹ D (k'+1)) :
    Later.prop (Later.ap' (k'+1)
        (World.restrict (Later.ap' m
            (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
            (Later.next S)) hl) dl)
    = (GoodP : world(Nat → D → Prop) k') k' (Nat.le_refl k') S k' (Nat.le_refl k')
        (dl : D k') := by
  rw [Later_ap'_W_restrict_GoodP hm hl S]
  simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ, World.Const.restrictStep_eq]
  rw [Later_next_GoodP_restrict (Nat.le_trans hl hm)]

/-- Heap-entry-wise monotonicity in budget: a heap good at S₁ is good at S₂
    when S₁ ≤ S₂. Per sub-level + entry, lift via `TraceGoodP_mono_S`. -/
theorem Param_Heap_GoodP_mono {n m : Nat} (hm : m ≤ n)
    (μ : Heap (▹ D) m) (S₁ S₂ : Nat) (hS : S₁ ≤ S₂)
    (h : Parametric.Heap (Later.ap' m
            (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
            (Later.next S₁)) μ) :
    Parametric.Heap (Later.ap' m
            (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hm)
            (Later.next S₂)) μ := by
  intro m' hm' a dl h_get
  have h_at := h m' hm' a dl h_get
  cases m' with
  | zero => trivial
  | succ M =>
    have hMn : M + 1 ≤ n := Nat.le_trans hm' hm
    -- Push W.restrict through Later.ap' on both sides via the commutativity
    -- lemma, then resolve via Later_next_GoodP_restrict + GoodP_S_mono.
    rw [Later_ap'_W_restrict_GoodP hm hm' S₁] at h_at
    rw [Later_ap'_W_restrict_GoodP hm hm' S₂]
    simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
               World.Const.restrictStep_eq] at h_at ⊢
    rw [Later_next_GoodP_restrict hMn] at h_at ⊢
    exact GoodP_S_mono _ _ S₁ S₂ hS h_at

/-- Restricting a heap from level `k+1` to level `k`: a `Param.Heap`-good heap
    at `(k+1)` with the `loeb GoodPBody` predicate gives a `Param.Heap`-good
    heap at `k` for the corresponding predicate at level `k`.

    With the all-sub-levels `Parametric.Heap` definition, this follows
    structurally: specialize the input at each `m' ≤ k`, then the
    `W.restrict`-composition collapses the proof. -/
theorem Param_Heap_GoodP_succ_down {n k : Nat} (hk1 : k+1 ≤ n) (S : Nat)
    (μ : Heap (▹ D) (k+1))
    (h : Parametric.Heap (Later.ap' (k+1)
            (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n)) hk1)
            (Later.next S)) μ) :
    Parametric.Heap (Later.ap' k
            (World.restrict (Later.next (loeb GoodPBody : world(Nat → D → Prop) n))
              (Nat.le_of_succ_le hk1))
            (Later.next S))
            (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) := by
  intro m hm a dl h_get
  have hmk1 : m ≤ k+1 := Nat.le_succ_of_le hm
  -- Restriction composition: (W.restrict (W.restrict μ ...) hm) = W.restrict μ ?
  -- We need to align the two restricted heaps so we can apply h.
  have h_eq_μ : @World.restrict (Heap (▹ D)) _ k m
                  (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) hm
              = @World.restrict (Heap (▹ D)) _ (k+1) m μ hmk1 := by
    have h_inner : @World.restrict (Heap (▹ D)) _ (k+1) k μ (Nat.le_succ_of_le (Nat.le_refl k))
                = @World.restrictStep (Heap (▹ D)) _ k μ := by
      rw [@World.restrict_succ (Heap (▹ D)) _ k k μ (Nat.le_refl k),
          @World.restrict_self (Heap (▹ D)) _ k _]
    rw [h_inner]
    show @World.restrict (Heap (▹ D)) _ k m (@World.restrictStep (Heap (▹ D)) _ k μ) hm = _
    rw [show hmk1 = Nat.le_succ_of_le hm from rfl,
        @World.restrict_succ (Heap (▹ D)) _ k m μ hm]
  rw [h_eq_μ] at h_get
  have h_at := h m hmk1 a dl h_get
  -- The two predicate values, after `W.restrict` to `Later world(D → Prop) m`,
  -- agree pointwise by body invariance of `GoodPBody` in `m_outer`. Use that
  -- `W.restrict` on `Later.ap'` of a loeb-shape commutes through to the inner
  -- loeb application, modulo proof irrelevance.
  cases m with
  | zero =>
    -- Later (W.Const Prop) 0 = PUnit; ▷ at 0 is True.
    trivial
  | succ M =>
    have hMk : M + 1 ≤ k+1 := hmk1
    have hMn : M + 1 ≤ n := Nat.le_trans hMk hk1
    -- Push W.restrict through Later.ap' on both sides via the commutativity lemma.
    rw [Later_ap'_W_restrict_GoodP (Nat.le_of_succ_le hk1) hm S] at ⊢
    rw [Later_ap'_W_restrict_GoodP hk1 hmk1 S] at h_at
    simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
               World.Const.restrictStep_eq] at h_at ⊢
    rw [Later_next_GoodP_restrict hMn] at h_at ⊢
    -- Both reduce to (GoodP at M) M _ S M _ dl — equal.
    exact h_at

/-! ## Forgetful map: `TraceGoodP → NCI 2` (reset budget hard-coded at 2). -/

theorem TraceGoodP_implies_NCI :
    ∀ (m' : Nat) {n : Nat} (RetGoodP : world(VH → Prop) n)
      (m : Nat) (hm : m ≤ n) (steps : Nat) (hm' : m' ≤ m) (t : T VH m'),
      TraceGoodP RetGoodP m hm steps m' hm' t → NCI 2 steps m' t := by
  intro m'
  induction m' with
  | zero => intro _ _ _ _ _ _ _ _; unfold NCI; trivial
  | succ k ih =>
    intro n RetGoodP m hm steps hm' t htg
    unfold NCI
    unfold TraceGoodP at htg
    rw [loeb.eq TraceGoodPBody_natural] at htg
    cases hu : T.unfold t with
    | ret _ => trivial
    | step ev tl =>
      rw [TraceGoodPBody_step_eq RetGoodP (Nat.le_refl _)
            (Later.next (loeb (TraceGoodPBody RetGoodP))) hm steps hm' t ev tl hu] at htg
      simp only [hu]
      simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                 World.Function.restrictStep_eq, World.Const.restrictStep_eq,
                 Later.Function.restrict_apply] at htg
      have hkn : k ≤ n := Nat.le_of_succ_le (Nat.le_trans hm' hm)
      have h_bridge : World.restrict (Later.next (loeb (TraceGoodPBody RetGoodP)))
                        (Nat.le_trans hm' hm)
                    = TraceGoodP (World.restrict RetGoodP hkn) :=
        Later_next_loeb_restrict RetGoodP (Nat.le_trans hm' hm)
      rw [h_bridge] at htg
      exact ih (n := k) (World.restrict RetGoodP hkn) k (Nat.le_refl _) 2 (Nat.le_refl _) tl htg
    | invis dl =>
      cases steps with
      | zero =>
        rw [TraceGoodPBody_invis_zero RetGoodP (Nat.le_refl _)
              (Later.next (loeb (TraceGoodPBody RetGoodP))) hm hm' t dl hu] at htg
        exact htg.elim
      | succ j =>
        rw [TraceGoodPBody_invis_eq RetGoodP (Nat.le_refl _)
              (Later.next (loeb (TraceGoodPBody RetGoodP))) hm j hm' t dl hu] at htg
        simp only [hu]
        obtain ⟨_, h_rec⟩ := htg
        simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                   World.Function.restrictStep_eq, World.Const.restrictStep_eq,
                   Later.Function.restrict_apply] at h_rec
        have hkn : k ≤ n := Nat.le_of_succ_le (Nat.le_trans hm' hm)
        have h_bridge : World.restrict (Later.next (loeb (TraceGoodPBody RetGoodP)))
                          (Nat.le_trans hm' hm)
                      = TraceGoodP (World.restrict RetGoodP hkn) :=
          Later_next_loeb_restrict RetGoodP (Nat.le_trans hm' hm)
        rw [h_bridge] at h_rec
        exact ih (n := k) (World.restrict RetGoodP hkn) k (Nat.le_refl _) j (Nat.le_refl _) dl h_rec

/-- Helper: `D.invis (fetch a)`'s trace at level `m` is `TraceGoodP`-good at
    `S=2`, given the heap is good with entries satisfying the `NCI 1`
    projection of the outer GoodP loeb. The trace structure is
    `.invis ; (.invis ∣ .ret stuck) ; memo-content`, and the heap-good
    invariant on entry `a` gives the memo content `NCI 0` goodness. -/
theorem TraceGoodP_D_invis_fetch {n : Nat} (a : Addr)
    {m : Nat} (hm : m ≤ n) (μ : Heap (▹ D) m)
    (h_heap : Parametric.Heap
                (Later.ap' m
                  (World.restrict (Later.next (loeb GoodPBody) :
                                    ▹ world(Nat → D → Prop) n) hm)
                  (Later.next (1 : Nat))) μ) :
    TraceGoodP
      (RetGoodP (fun k => Later.ap' m
                  (World.restrict (Later.next (loeb GoodPBody)) hm)
                  (Later.next k)))
      m (Nat.le_refl _) (2 : Nat) m (Nat.le_refl _)
      ((D.invis (fetch (n := n) a)).unfold m hm μ) := by
  -- Unfold the D.invis trace.
  rw [D_invis_eq]
  -- T.unfold of T.fold (.invis _) reduces.
  unfold TraceGoodP
  rw [loeb.eq TraceGoodPBody_natural]
  rw [TraceGoodPBody_invis_eq _ _ _ _ _ _ _ _
      (by show T.unfold (T.fold (.invis _)) = .invis _; rw [T_uf])]
  -- Goal: (▷(NotRet dl) ∨ ▷(IsRetStuck dl)) ∧ ▷(Recur 1 of dl)
  -- where dl = Later.hmap m _ (W.restrict (fetch a) hm) : Later (T VH) m
  cases m with
  | zero =>
    -- ▷ at level 0 is trivially True for both halves.
    refine ⟨Or.inl ?_, ?_⟩ <;> trivial
  | succ k =>
    -- dl at level k: by restrict_later_next' + D_unfold_restrict + D_fold_unfold,
    -- this reduces to match (W.restrict μ (k≤k+1)).get? a with
    --   | some d => T.invis (Later.hmap k ... d)
    --   | none => T.ret stuck.
    -- Both cases satisfy NotRet ∨ IsRetStuck:
    --   • some → T.invis: NotRet is True (.invis ≠ .ret).
    --   • none → T.ret stuck: IsRetStuck is True.
    -- For Recur 1 of dl: at S=1, the .invis case further recurses with j=0,
    -- and the .ret case is RetGoodP at stuck (vacuous fn/con conds + heap).
    have hk : k ≤ n := Nat.le_of_succ_le hm
    -- Reduce dl to the concrete match expression on heap state at a.
    -- dl = Later.hmap (k+1) f (W.restrict (fetch a) hm) at Later (T VH) (k+1) = T VH k.
    -- = f k _ (W.restrict (fetch a) hm at Later D (k+1))
    -- = (W.restrict (D.fold inner_fetch) hk).unfold k _ μ_k          [restrict_later_next']
    -- = (D.fold inner_fetch).unfold k hk μ_k                          [D_unfold_restrict]
    -- = inner_fetch k hk μ_k                                          [D_fold_unfold]
    -- = match μ_k.get? a with | some d => T.fold (.invis _) | none => T.ret stuck.
    let μ_k : Heap (▹ D) k := World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))
    -- dl = Later.hmap (k+1) f (W.restrict (fetch a) hm) at level k+1.
    -- Reduce: Later.hmap (k+1) is application of f to its arg at level k;
    -- W.restrict (Later.next (D.fold inner)) hm = W.restrict (D.fold inner) (k≤n);
    -- (W.restrict (D.fold inner)).unfold k _ μ_k = inner k _ μ_k
    -- = match Std.HashMap.get? μ_k a with | some d => T.fold (.invis ...) | none => T.ret stuck.
    have h_dl_reduce :
        (Later.hmap (k+1) (fun i _hi (d : D i) =>
              d.unfold i (Nat.le_refl i)
                (World.restrict μ (by omega : i ≤ k+1)))
              (@World.restrict (Later D) _ n (k+1) (fetch (n := n) a) hm)
          : T VH k)
        = match Std.HashMap.get? μ_k a with
          | some d => T.fold (.invis (Later.hmap k (fun i _hi (d' : D i) =>
              d'.unfold i (Nat.le_refl i)
                (World.restrict μ_k (by omega : i ≤ k))) d))
          | none => T.ret (Value.F.toRep _ .stuck, μ_k) := by
      show (fun (d : D k) => d.unfold k (Nat.le_refl k) μ_k)
            (@World.restrict (Later D) _ n (k+1) (fetch (n := n) a) hm) = _
      unfold fetch
      rw [restrict_later_next' _ k hm]
      change (@World.restrict D _ n k (D.fold _) (by omega)).unfold k _ μ_k = _
      rw [D_unfold_restrict, D_fold_unfold]
      rfl
    refine ⟨?_, ?_⟩
    · -- (NotRet ∨ IsRetStuck) — reduce via h_dl_reduce, then case on heap.
      simp only [Later.prop_succ, Later.map]
      rw [h_dl_reduce]
      cases hget : Std.HashMap.get? μ_k a with
      | none =>
        -- T.ret stuck: at k=0, NotRet trivially; at k=k'+1, IsRetStuck.
        cases k with
        | zero => left; trivial
        | succ k' =>
          right
          show IsRetStuck (k'+1) (T.ret (Value.F.toRep _ Value.F.stuck, _))
          simp only [IsRetStuck, T.ret, T_uf]
          -- Value.F.toRep .stuck = Sum.inl PUnit.unit by Value.F.toRep computation.
          rfl
      | some d =>
        -- T.invis _: at k=0, NotRet trivially; at k=k'+1, NotRet via T_uf.
        left
        cases k with
        | zero => trivial
        | succ k' =>
          show NotRet (k'+1) (T.fold (T.F.invis _))
          simp only [NotRet, T_uf]
    · -- ▷(Recur 1 of dl): TraceGoodPBody at steps=1 on dl, which is the
      -- match-on-heap-state trace. Case on Std.HashMap.get? μ_k a:
      --   • none → dl = T.ret stuck. RetGoodP at stuck has vacuous
      --     function/con-cond, needs heap-cond Param.Heap (Recur 2) μ_k.
      --     From h_heap at level k+1, restrict to level k.
      --   • some d → dl = T.invis inner. Requires inner trace to start
      --     visibly + ▷(Recur 0 of inner). The heap-good invariant on d
      --     gives TraceGoodP at S=1 of d.unfold, which captures both.
      sorry

end NewIdea

open NewIdea

/-! ## `LR.good` — using the loeb-based `goodP` -/

/-- Restricting `D.invis (fetch a)` from level `n+1` to level `n` gives
    `D.invis (fetch a)` at level `n`. Proven by `D_ext` plus the fact that
    `fetch a`'s underlying closure is level-polymorphic. -/
private theorem D_invis_fetch_restrictStep {n : Nat} (a : Addr) :
    @World.restrictStep D _ n (D.invis (fetch (n := n+1) a))
    = D.invis (fetch (n := n) a) := by
  apply D_ext
  intro m hm μ
  rw [D_unfold_restrictStep, D_invis_eq, D_invis_eq]
  congr 2
  cases m with
  | zero => rfl
  | succ k =>
    -- At level k+1, Later.hmap (k+1) f x = f k _ x, so both sides reduce to
    -- (W.restrict (D.fold inner)).unfold k _ μ_k at the inner level k.
    -- After D_unfold_restrict + D_fold_unfold both reduce to inner k _ μ_k,
    -- where inner is the same closure on both sides (parametrized by m' and μ).
    show (fun (d : D k) => d.unfold k (Nat.le_refl k)
            (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))))
            (@World.restrict (Later D) _ (n+1) (k+1) (fetch (n := n+1) a) _)
        = (fun (d : D k) => d.unfold k (Nat.le_refl k)
            (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))))
            (@World.restrict (Later D) _ n (k+1) (fetch (n := n) a) _)
    unfold fetch
    rw [restrict_later_next' _ k (Nat.le_succ_of_le hm),
        restrict_later_next' _ k hm]
    -- β-reduce, then unfold via D_unfold_restrict + D_fold_unfold.
    change (@World.restrict D _ (n+1) k (D.fold _) _).unfold k _ _
         = (@World.restrict D _ n k (D.fold _) _).unfold k _ _
    rw [D_unfold_restrict, D_unfold_restrict, D_fold_unfold, D_fold_unfold]

/-- Closure of the `D.invis (fetch a)` shape under `restrictStep`. -/
private theorem isThunk_closed {n : Nat} (d : D (n+1))
    (h : ∃ a : Addr, d = D.invis (fetch (n := n+1) a)) :
    ∃ a : Addr, World.restrictStep d = D.invis (fetch (n := n) a) := by
  obtain ⟨a, hd⟩ := h
  exact ⟨a, by rw [hd]; exact D_invis_fetch_restrictStep a⟩

/-- ByNeed's `IsThunk` predicate: heap-fetched thunks of the form
    `D.invis (fetch a)` for some address `a`. Captures what `D.bind` actually
    passes to `body`/`rhs`. -/
noncomputable def isThunk : World.Pred D :=
  World.Pred.ofClosed
    (holds := fun {n} (d : D n) => ∃ a : Addr, d = D.invis (fetch (n := n) a))
    (closed := isThunk_closed)

theorem isThunk_iff {n : Nat} (d : D n) :
    isThunk.holds d ↔ ∃ a : Addr, d = D.invis (fetch (n := n) a) :=
  World.Pred.ofClosed_holds _ _ d

/-- The logical relation packaged as an `LR ByNeed.D`. -/
noncomputable def good : LR D where
  P := goodP 2
  IsThunk := isThunk
  IsThunk_to_P := by
    intro n x d hT
    obtain ⟨a, hd⟩ := (isThunk_iff d).mp hT
    subst hd
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (Domain.step' (.look x) (D.invis (fetch a))) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq NewIdea.GoodPBody_natural]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict]
    -- Goal includes (Domain.step' (.look x) (D.invis (fetch a))).unfold.
    -- Domain.step' = D.step ∘ Later.next for ByNeed; D_step_eq unfolds the trace.
    change NewIdea.TraceGoodP _ m _ (2 : Nat) m _
      ((D.step (.look x) (Later.next (D.invis (fetch a)))).unfold m _ (μ↓))
    rw [D_step_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq NewIdea.TraceGoodPBody_natural]
    rw [NewIdea.TraceGoodPBody_step_eq _ _ _ _ _ _ _ _ _
        (by unfold T.step; rw [T_uf] : T.unfold (T.step _ _) = .step _ _)]
    -- Goal: ▷(Later.ap' m (Later.ap' m (W.restrict (Later.next loeb) refl)
    --         (Later.next 2)) tl)
    cases m with
    | zero => trivial
    | succ k =>
      simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                 World.restrict_self, World.Const.restrictStep_eq]
      rw [restrictStep_loeb_eq_loeb_restrictStep NewIdea.TraceGoodPBody_natural,
          NewIdea.TraceGoodPBody_restrictStep_RetGoodP,
          NewIdea.RetGoodP_restrictStep]
      have hk : k ≤ n := Nat.le_of_succ_le hm
      have h_tl : (Later.hmap (k+1) (fun i _hi (d' : D i) =>
              d'.unfold i (Nat.le_refl i) (World.restrict μ (by omega : i ≤ k+1)))
              (@World.restrict (Later D) _ n (k+1)
                (Later.next (D.invis (fetch (n := n) a))) hm) : T VH k)
            = (World.restrict (D.invis (fetch (n := n) a)) hk).unfold k (Nat.le_refl k)
                (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) := by
        show (fun (a' : D k) => a'.unfold k (Nat.le_refl k) (World.restrict μ _))
              (@World.restrict (Later D) _ n (k+1)
                (Later.next (D.invis (fetch (n := n) a))) hm) = _
        congr 1
        exact restrict_later_next' (D.invis (fetch (n := n) a)) k hm
      rw [h_tl, D_unfold_restrict]
      -- Bridge: same shape as in `step` — goal has RetGoodP applied to
      -- `fun k_1 => W.restrictStep (_Recur_m k_1)`; rewrite pointwise via
      -- Later_ap'_W_restrictStep_GoodP to match the helper's expected form.
      have h_dgoodp_eq :
          (fun k_1 => World.restrictStep (_Recur_m k_1))
          = (fun k_1 => Later.ap' k
              (World.restrict (Later.next (loeb NewIdea.GoodPBody :
                world(Nat → D → Prop) n)) hk)
              (Later.next k_1)) := by
        funext k_1
        show World.restrictStep (Later.ap' (k+1)
              (World.restrict (Later.next (loeb NewIdea.GoodPBody)) hm)
              (Later.next k_1)) = _
        rw [NewIdea.Later_ap'_W_restrictStep_GoodP hm hk k_1]
      rw [h_dgoodp_eq]
      -- h_heap at level k+1 restricts to a (Recur 1)-good heap at level k.
      have h_heap_at_k : Parametric.Heap (Later.ap' k
              (World.restrict (Later.next (loeb NewIdea.GoodPBody :
                world(Nat → D → Prop) n)) hk) (Later.next (1 : Nat)))
              (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) :=
        NewIdea.Param_Heap_GoodP_succ_down hm 1 μ h_heap
      exact NewIdea.TraceGoodP_D_invis_fetch a hk _ h_heap_at_k
  stuck := by
    intro n
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (D.stuck : D n) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq NewIdea.GoodPBody_natural]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.stuck, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq NewIdea.TraceGoodPBody_natural]
    rw [NewIdea.TraceGoodPBody_ret_eq _ _ _ _ _ _ _ _
        (by unfold T.ret; rw [T_uf] : T.unfold (T.ret _) = .ret _)]
    rw [NewIdea.RetGoodP_apply]
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [Value_F_Rep_restrict_stuck] at hg
      nomatch hg
    · intro K ds hg
      rw [Value_F_Rep_restrict_stuck] at hg
      nomatch hg
    · -- Heap-cond: lift Recur 1 → Recur 2 via Param_Heap_GoodP_mono.
      simp only [World.restrict_self]
      exact NewIdea.Param_Heap_GoodP_mono hm μ 1 2 (by omega) h_heap
  step := by
    intro n ev d h_goodP
    rw [NewIdea.goodP_iff]
    intro m hm
    show (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (D.step ev (Later.next d)) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq NewIdea.GoodPBody_natural]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D_step_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq NewIdea.TraceGoodPBody_natural]
    rw [NewIdea.TraceGoodPBody_step_eq _ _ _ _ _ _ _ _ _
        (by unfold T.step; rw [T_uf] : T.unfold (T.step _ _) = .step _ _)]
    cases m with
    | zero => trivial
    | succ k =>
      simp only [Later.prop_succ, Later.ap'_succ, Later.next_succ,
                 World.restrict_self, World.Const.restrictStep_eq]
      rw [restrictStep_loeb_eq_loeb_restrictStep NewIdea.TraceGoodPBody_natural,
          NewIdea.TraceGoodPBody_restrictStep_RetGoodP,
          NewIdea.RetGoodP_restrictStep]
      have hk : k ≤ n := Nat.le_of_succ_le hm
      -- Reduce tl to (W.restrict d hk).unfold k _ μ_k.
      have h_tl : (Later.hmap (k+1) (fun i _hi (d' : D i) =>
              d'.unfold i (Nat.le_refl i) (World.restrict μ (by omega : i ≤ k+1)))
              (@World.restrict (Later D) _ n (k+1) (Later.next d) hm) : T VH k)
            = (World.restrict d hk).unfold k (Nat.le_refl k)
                (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) := by
        show (fun (a' : D k) => a'.unfold k (Nat.le_refl k) (World.restrict μ _))
              (@World.restrict (Later D) _ n (k+1) (Later.next d) hm) = _
        congr 1
        exact restrict_later_next' d k hm
      rw [h_tl]
      -- Now: TraceGoodP (RetGoodP (W.restrictStep ...)) k _ 2 k _ ((W.restrict d hk).unfold k _ μ_k)
      -- Use h_goodP : goodP_holds 0 d at sub-level k, then lift S=0 → S=2.
      rw [NewIdea.goodP_iff 2] at h_goodP
      have h_at_k : (NewIdea.GoodP : world(Nat → D → Prop) n) k hk
                      (2 : Nat) k (Nat.le_refl k) (World.restrict d hk) :=
        (h_goodP k hk)
      unfold NewIdea.GoodP at h_at_k
      rw [loeb.eq NewIdea.GoodPBody_natural] at h_at_k
      -- h_heap at level k+1 restricts to a (Recur 1)-good heap at level k.
      have h_heap_at_k : Parametric.Heap (Later.ap' k
              (World.restrict (Later.next (loeb NewIdea.GoodPBody :
                world(Nat → D → Prop) n)) hk) (Later.next (1 : Nat)))
              (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k))) :=
        NewIdea.Param_Heap_GoodP_succ_down hm 1 μ h_heap
      have h_trace := h_at_k _ h_heap_at_k
      -- Bridge: the goal's `RetGoodP (fun k_1 => W.restrictStep (_Recur_m k_1))`
      -- equals h_trace's `RetGoodP (fun k_1 => Later.ap' k (W.restrict ... hk) (Later.next k_1))`
      -- by Later_ap'_W_restrictStep_GoodP applied pointwise.
      have h_dgoodp_eq :
          (fun k_1 => World.restrictStep
            (_Recur_m k_1))
          = (fun k_1 => Later.ap' k
              (World.restrict (Later.next (loeb NewIdea.GoodPBody :
                world(Nat → D → Prop) n)) hk)
              (Later.next k_1)) := by
        funext k_1
        show World.restrictStep (Later.ap' (k+1)
              (World.restrict (Later.next (loeb NewIdea.GoodPBody)) hm)
              (Later.next k_1)) = _
        rw [NewIdea.Later_ap'_W_restrictStep_GoodP hm hk k_1]
      rw [h_dgoodp_eq]
      -- Collapse the double W.restrict on μ in h_trace.
      rw [show World.restrict (World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k)))
                (Nat.le_refl k)
            = World.restrict μ (Nat.le_succ_of_le (Nat.le_refl k)) from
          @World.restrict_self (Heap (▹ D)) _ k _] at h_trace
      exact h_trace
  fn := by
    intro n f h_param
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (Domain.fn' f) hm)
    show (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (D.fn f) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq NewIdea.GoodPBody_natural]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.fn, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq NewIdea.TraceGoodPBody_natural]
    rw [NewIdea.TraceGoodPBody_ret_eq _ _ _ _ _ _ _ _
        (by unfold T.ret; rw [T_uf] : T.unfold (T.ret _) = .ret _)]
    rw [NewIdea.RetGoodP_apply]
    refine ⟨?_, ?_, ?_⟩
    · -- function-cond. Bridge: hdl → (GoodP at k') k' _ 2 k' _ dl_inner.
      -- To call h_param at level k', need IsLookup_holds (goodP 2) dl_inner,
      -- which requires the full goodP_holds (all-m). The current bridge only
      -- gives single-level info; need a "single-level → all-m" closure lemma.
      sorry
    · -- con-cond: vacuous (v has shape Sum.inr (Sum.inl _), not Sum.inr (Sum.inr _))
      intro K ds hg
      obtain ⟨g', hg'⟩ := Value_F_Rep_restrict_fn_shape _ hm
      rw [hg'] at hg
      nomatch hg
    · -- Heap-cond: lift Recur 1 → Recur 2 via Param_Heap_GoodP_mono.
      simp only [World.restrict_self]
      exact NewIdea.Param_Heap_GoodP_mono hm μ 1 2 (by omega) h_heap
  con := by
    intro n K ds h_param
    rw [NewIdea.goodP_iff 2]
    intro m hm
    change (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (Domain.con' K ds) hm)
    show (NewIdea.GoodP : world(Nat → D → Prop) n) m hm (2 : Nat) m (Nat.le_refl _)
      (World.restrict (D.con K ds) hm)
    unfold NewIdea.GoodP
    rw [loeb.eq NewIdea.GoodPBody_natural]
    unfold NewIdea.GoodPBody
    intro _Recur_m μ h_heap
    rw [D_unfold_restrict, D.con, D_ret_eq]
    unfold NewIdea.TraceGoodP
    rw [loeb.eq NewIdea.TraceGoodPBody_natural]
    rw [NewIdea.TraceGoodPBody_ret_eq _ _ _ _ _ _ _ _
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
    · -- Heap-cond: lift Recur 1 → Recur 2 via Param_Heap_GoodP_mono.
      simp only [World.restrict_self]
      exact NewIdea.Param_Heap_GoodP_mono hm μ 1 2 (by omega) h_heap
  app_closed := by sorry
  case_closed := by sorry
  bind_closed := by
    intro n rhs body h_rhs h_body
    -- Goal: (goodP 0).holds (Domain.step' .let1 (Domain.bind' rhs body)).
    -- Strategy:
    --   The outer `step .let1` exposes a `T.step .let1 tl` trace, where `tl` is
    --   the trace of `bind' rhs body`. By TraceGoodPBody at .step the inner check
    --   is at `Recur 2`. By bind'-unfold, the inner trace is body's trace under
    --   the heap extended with memo'd rhs thunk. IsThunk holds for `D.invis (fetch a)`,
    --   so by h_body, `body _ _ (D.invis (fetch a))` is P-good. Lifted via
    --   TraceGoodP_mono_S 0 → 2, the trace is Recur 2-good. The extended heap
    --   stays Param.Heap-good after adding the memo'd entry (memoThunk's trace
    --   starts with `.step .update`, so it's Recur 1-good).
    sorry

/-! ## Main theorems -/

private theorem emptyEnv_good (n : Nat) : good.env (Env.empty : Env (D n)) :=
  good.env_empty

/-- The empty heap is `Parametric.Heap`-good for any predicate, vacuously. -/
private theorem Parametric.Heap_empty {n : Nat} (P : ▹ world(D → Prop) n) :
    Parametric.Heap P (∅ : Heap (▹ D) n) := by
  intro m hm a dl h_get
  -- TODO: prove `get? (W.restrict ∅ hm) a = none` by induction on `n`.
  sorry

/-- Every trace produced by `evalByNeed` has at most 2 consecutive invisible
    steps. -/
theorem evalByNeed_noTripleInvis (n : Nat) (e : Exp) :
    NoTripleInvis n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) := by
  have h_goodP : (goodP 2).holds (eval (D := D) e n (Nat.le_refl n) Env.empty) :=
    show good.P.holds _ from LR.fundamental good e Env.empty (emptyEnv_good n)
  rw [goodP_iff 2] at h_goodP
  -- Specialize at m = n.
  have h_at_n := h_goodP n (Nat.le_refl n)
  rw [World.restrict_self] at h_at_n
  -- Unfold GoodP at level n via loeb.eq, then expand GoodPBody.
  unfold GoodP at h_at_n
  rw [loeb.eq GoodPBody_natural] at h_at_n
  unfold GoodPBody at h_at_n
  -- Apply with empty heap.
  have h_trace := h_at_n ∅ (Parametric.Heap_empty _)
  -- Rewrite ∅↓ = ∅.
  rw [show (∅ : Heap (▹ D) n)↓ = (∅ : Heap (▹ D) n) from
        @World.restrict_self (Heap (▹ D)) _ n ∅] at h_trace
  -- h_trace : TraceGoodP _ n _ 2 n _ (eval.unfold n _ ∅).
  show NCI 2 2 n ((eval (D := D) e n _ Env.empty).unfold n _ ∅)
  exact TraceGoodP_implies_NCI n _ n _ 2 _ _ h_trace

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
