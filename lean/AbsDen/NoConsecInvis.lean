import AbsDen.ByNeed
import AbsDen.World.Naturality

/-!
# No Triple Consecutive Invisible Steps

We prove that traces produced by `evalByNeed` have at most 2 consecutive `T.invis`
steps (no triple invis).

## Proof strategy

We define a step-indexed logical relation using a combined `TraceGood` predicate that
captures four properties simultaneously:

1. **NCI (No Consecutive Invis)**: At most `k` consecutive invisible steps.
2. **NIBR (No Invis Before Ret)**: After `invis`, the next step is never `ret`.
3. **Heap preservation**: Return heaps satisfy `GoodHeap`.
4. **Value goodness**: Returned function values preserve `GoodLater`, and
   returned constructor values have `GoodLater` fields.

Property 4 is crucial for the `apply` and `select` cases of the fundamental lemma.
-/

open ByNeed
set_option maxHeartbeats 1600000
namespace ByNeed

/-! ## Equational lemmas -/

@[simp] theorem D_fold_unfold {n : Nat} (f : world(Heap (▹ D) → T VH) n) (m : Nat)
    (hm : m ≤ n) (μ : Heap (▹ D) m) :
    D.unfold (D.fold f) m hm μ = f m hm μ := by
  simp [D.unfold, D.fold, World.Fix.unfold, World.Fix.fold]

@[simp] theorem D_step_eq {n : Nat} (ev : Event) (dl : ▹ D n) (m : Nat)
    (hm : m ≤ n) (μ : Heap (▹ D) m) :
    D.unfold (D.step ev dl) m hm μ =
    T.step ev (Later.hmap m (fun i _hi d => d.unfold i (Nat.le_refl i) (World.restrict μ (by omega)))
      (World.restrict dl hm)) := by simp [D.step]

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

noncomputable def NCI : Nat → (n : Nat) → T VH n → Prop
  | _, 0, _ => True
  | k, n + 1, t => match T.unfold t with
    | .ret _ => True | .step _ dl => NCI 2 n dl
    | .invis dl => match k with | 0 => False | j + 1 => NCI j n dl
termination_by _ n _ => n

abbrev NoTripleInvis (n : Nat) (t : T VH n) : Prop := NCI 2 n t

/-! ## Combined TraceGood and GoodLater with value conditions -/

@[inline, reducible] noncomputable def unfoldLater {m : Nat} (dl : ▹ D (m + 1))
    (k : Nat) (hk : k ≤ m) (μ : Heap (▹ D) k) : T VH k := @D.unfold m dl k hk μ

mutual
noncomputable def GoodLater : (m : Nat) → ▹ D m → Prop
  | 0, _ => True
  | m + 1, dl =>
    ∀ k (hk : k ≤ m) (μ : Heap (▹ D) k),
      (∀ a (dl' : ▹ D k), Std.HashMap.get? μ a = some dl' → GoodLater k dl') →
      StartsWithStep k (unfoldLater dl k hk μ) ∧ TraceGood 2 k (unfoldLater dl k hk μ)
  termination_by m _ => (m, 0)

noncomputable def TraceGood : Nat → (n : Nat) → T VH n → Prop
  | _, 0, _ => True
  | _b, n + 1, t => match T.unfold t with
    | .ret (v, μ) =>
        -- Function value condition: if v is .fn g, then g preserves GoodLater
        (∀ (g : World.Function (Later D) (Later D) (n+1)),
          v = .inr (.inl g) →
          ∀ k (hk : k ≤ n) (dl : ▹ D (k+1)),
            GoodLater (k+1) dl → GoodLater (k+1) (g (k+1) (by omega) dl)) ∧
        -- Constructor field condition: if v is .con K ds, fields are GoodLater
        (∀ (K : ConTag) (ds : List (▹ D (n+1))),
          v = .inr (.inr (K, ds)) →
          ∀ (dl : ▹ D (n+1)), dl ∈ ds → GoodLater (n+1) dl) ∧
        -- Heap condition
        (∀ a (dl : ▹ D (n + 1)), Std.HashMap.get? μ a = some dl → GoodLater (n + 1) dl)
    | .step _ dl => TraceGood 2 n dl
    | .invis dl => match _b with | 0 => False | j + 1 => (NotRet n dl ∨ IsRetStuck n dl) ∧ TraceGood j n dl
  termination_by _ n _ => (n, 1)
  decreasing_by all_goals simp_wf; omega
end

noncomputable def GoodHeap (m : Nat) (μ : Heap (▹ D) m) : Prop :=
  ∀ (a : Addr) (dl : ▹ D m), Std.HashMap.get? μ a = some dl → GoodLater m dl

noncomputable def GoodD (n : Nat) (d : D n) : Prop :=
  ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
    StartsVisible m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)

/-- Env entries satisfy the stronger StartsWithStep condition (not just StartsVisible).
    This is needed because env entries are always wrapped in D.step (.look x). -/
noncomputable def GoodEnv {n : Nat} (ρ : Env (D n)) : Prop :=
  ∀ x d, ρ.find? x = some d →
    ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)

/-! ## Basic lemmas -/

theorem TraceGood_zero (k : Nat) (t : T VH 0) : TraceGood k 0 t := by unfold TraceGood; trivial
theorem StartsVisible_zero (t : T VH 0) : StartsVisible 0 t := by unfold StartsVisible; trivial
theorem GoodLater_zero (dl : ▹ D 0) : GoodLater 0 dl := by unfold GoodLater; trivial

theorem TraceGood_implies_NCI (k n : Nat) (t : T VH n) : TraceGood k n t → NCI k n t := by
  induction n generalizing k with
  | zero => intro _; unfold NCI; trivial
  | succ n ih =>
    intro h; unfold TraceGood at h; unfold NCI
    generalize heq : T.unfold t = tu at h ⊢
    cases tu with
    | ret v => trivial | step ev dl => exact ih 2 dl h
    | invis dl => cases k with | zero => exact h | succ j => exact ih j dl h.2

/-! ## Naturality + restriction lemmas -/

theorem D_unfold_restrictStep {n : Nat} (d : D (n+1)) (m : Nat) (hm : m ≤ n)
    (μ : Heap (▹ D) m) :
    (World.restrictStep d).unfold m hm μ = d.unfold m (Nat.le_succ_of_le hm) μ := by
  unfold D.unfold; exact congrFun (World.Fix.unfold_restrictStep_Function d m hm) μ

theorem D_unfold_restrict {n : Nat} (d : D n) (m : Nat) (hm : m ≤ n)
    (k : Nat) (hk : k ≤ m) (μ : Heap (▹ D) k) :
    (World.restrict d hm).unfold k hk μ = d.unfold k (Nat.le_trans hk hm) μ := by
  match n with
  | 0 => have : m = 0 := Nat.le_zero.mp hm; subst this; simp [World.restrict.eq_1]
  | n + 1 =>
    rw [World.restrict.eq_1]; split
    · next heq => subst heq; simp
    · next hne =>
      have hm' := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hm hne)
      exact (D_unfold_restrict (World.restrictStep d) m hm' k hk μ).trans
        (D_unfold_restrictStep d k (Nat.le_trans hk hm') μ)
  termination_by n

private theorem GoodLater_restrictStep {n : Nat} (dl : Later D (n + 1))
    (hdl : GoodLater (n + 1) dl) : GoodLater n (World.restrictStep dl) := by
  cases n with
  | zero => exact GoodLater_zero _
  | succ n' =>
    unfold GoodLater; intro k hk μ hμ
    show StartsWithStep k (unfoldLater (World.restrictStep dl) k hk μ) ∧
         TraceGood 2 k (unfoldLater (World.restrictStep dl) k hk μ)
    simp only [unfoldLater]
    rw [show @D.unfold n' (@World.restrictStep (Later D) _ (n' + 1) dl) k hk μ =
          @D.unfold n' (@World.restrictStep D _ n' dl) k hk μ from rfl]
    rw [D_unfold_restrictStep dl k hk μ]
    unfold GoodLater at hdl; exact hdl k (Nat.le_succ_of_le hk) μ hμ

theorem GoodLater_restrict {n : Nat} (dl : Later D n) (hdl : GoodLater n dl)
    (m : Nat) (hm : m ≤ n) : GoodLater m (World.restrict dl hm) := by
  rw [World.restrict.eq_1]; split
  · next heq => subst heq; exact hdl
  · next hne => match n with
    | 0 => exact absurd (Nat.le_zero.mp hm) hne
    | _ + 1 => exact GoodLater_restrict _ (GoodLater_restrictStep dl hdl) m _
  termination_by n

/-! ## Heap operations -/

private theorem foldl_insert_map_getElem? {V W : Type} (f : V → W)
    (l : List (Nat × V))
    (acc_f : Std.HashMap Nat W) (acc_v : Std.HashMap Nat V)
    (hinv : ∀ a : Nat, (acc_f[a]? : Option W) = Option.map f (acc_v[a]? : Option V))
    (a : Nat) :
    ((l.foldl (fun acc (p : Nat × V) => Std.HashMap.insert acc p.1 (f p.2)) acc_f)[a]? : Option W) =
    Option.map f ((l.foldl (fun acc (p : Nat × V) => Std.HashMap.insert acc p.1 p.2) acc_v)[a]? : Option V) := by
  induction l generalizing acc_f acc_v with
  | nil => exact hinv a
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    intro b
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    split
    · simp
    · exact hinv b

private theorem foldl_insert_eq_insertMany {V : Type} (l : List (Nat × V)) (acc : Std.HashMap Nat V) :
    l.foldl (fun (acc : Std.HashMap Nat V) (p : Nat × V) => acc.insert p.1 p.2) acc = acc.insertMany l := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih, Std.HashMap.insertMany_cons]

private theorem findSome?_key_lookup {V : Type} {a : Nat}
    {l : List (Nat × V)} {v : V}
    (hmem : (a, v) ∈ l)
    (hdistinct : l.Pairwise (fun p q => (p.1 == q.1) = false)) :
    l.findSome? (fun p => if (p.1 == a) = true then some p.2 else none) = some v := by
  revert l; intro l
  induction l <;> simp_all +decide [List.pairwise_cons]; grind

private theorem findSomeRev?_toList_eq_getElem? {V : Type} (m : Std.HashMap Nat V) (a : Nat) :
    m.toList.findSomeRev? (fun (p : Nat × V) => if (p.1 == a) = true then some p.2 else none) =
    m[a]? := by
  rw [List.findSomeRev?_eq_findSome?_reverse]
  cases h : m[a]? with
  | none =>
    rw [List.findSome?_eq_none_iff]
    intro p hp
    have hp_mem : p ∈ m.toList := List.mem_reverse.mp hp
    split
    · next heq =>
      have h_eq : p.1 = a := beq_iff_eq.mp heq
      have hmem' : (a, p.2) ∈ m.toList := h_eq ▸ hp_mem
      have : m[a]? = some p.2 :=
        Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mpr
          ⟨a, beq_self_eq_true _, hmem'⟩
      rw [h] at this; exact absurd this (by simp)
    · rfl
  | some v =>
    have ⟨k', hbeq, hmem_list⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp h
    have hk'_eq : k' = a := by rw [BEq.comm] at hbeq; exact beq_iff_eq.mp hbeq
    subst hk'_eq
    have hdist := Std.HashMap.distinct_keys_toList (m := m)
    have hdist_rev : m.toList.reverse.Pairwise (fun p q => (p.1 == q.1) = false) := by
      rw [List.pairwise_reverse]
      exact hdist.imp (fun {a b} h => by rw [BEq.comm]; exact h)
    exact findSome?_key_lookup (List.mem_reverse.mpr hmem_list) hdist_rev

private theorem HashMap_rebuild_getElem? {V : Type} (m : Std.HashMap Nat V) (a : Nat) :
    (m.toList.foldl (fun (acc : Std.HashMap Nat V) (p : Nat × V) => acc.insert p.1 p.2) ∅)[a]? =
    m[a]? := by
  rw [foldl_insert_eq_insertMany, Std.HashMap.getElem?_insertMany_list,
      Std.HashMap.getElem?_empty, Option.or_none, findSomeRev?_toList_eq_getElem?]

/-- HashMap.get? commutes with Functor.map on AddrMap. -/
theorem AddrMap_get?_map {V W : Type} (f : V → W) (m : AddrMap V) (a : Addr) :
    Std.HashMap.get? (Functor.map f m : AddrMap W) a =
    Option.map f (Std.HashMap.get? m a) := by
  simp only [Std.HashMap.get?_eq_getElem?]
  show (Std.HashMap.fold (fun (acc : Std.HashMap Nat W) k v => acc.insert k (f v)) ∅ m)[a]? = _
  rw [Std.HashMap.fold_eq_foldl_toList]
  rw [foldl_insert_map_getElem?]
  · congr 1; exact HashMap_rebuild_getElem? m a
  · intro b; simp

theorem GoodHeap_restrictStep {n : Nat} (μ : Heap (▹ D) (n+1)) (hμ : GoodHeap (n+1) μ) :
    GoodHeap n (World.restrictStep μ) := by
  intro a dl ha
  have h_map : Std.HashMap.get? (World.restrictStep μ) a =
    Option.map World.restrictStep (Std.HashMap.get? μ a) := by
    show Std.HashMap.get? (Functor.map World.restrictStep μ) a = _
    exact AddrMap_get?_map _ μ a
  rw [h_map] at ha
  cases hget : Std.HashMap.get? μ a with
  | none => rw [hget] at ha; simp at ha
  | some dl_orig =>
    simp only [hget, Option.map] at ha; cases ha
    exact GoodLater_restrictStep dl_orig (hμ a dl_orig hget)

theorem GoodHeap_restrict {n m : Nat} (μ : Heap (▹ D) n) (hμ : GoodHeap n μ)
    (hm : m ≤ n) : GoodHeap m (World.restrict μ hm) := by
  rw [World.restrict.eq_1]; split
  · next heq => subst heq; exact hμ
  · next hne => match n with
    | 0 => exact absurd (Nat.le_zero.mp hm) hne
    | _ + 1 => exact GoodHeap_restrict _ (GoodHeap_restrictStep μ hμ) _
  termination_by n

/-! ## Closure properties -/

private theorem restrict_fn_rep {n m : Nat} (g : World.Function (Later D) (Later D) n) (hm : m ≤ n) :
    @World.restrict (Value.F.Rep (Later D)) _ n m
      ((Sum.inr (Sum.inl g) : Value.F.Rep (Later D) n)) hm =
    (Sum.inr (Sum.inl (World.restrict g hm)) : Value.F.Rep (Later D) m) := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hm; simp [World.restrict.eq_1]
  | succ n ih =>
    rw [World.restrict.eq_1]; split
    · next h => subst h; rw [World.restrict.eq_1, dif_pos rfl]; simp only [cast_eq]
    · next h =>
      dsimp only []
      show @World.restrict (Value.F.Rep (Later D)) _ n m
        (Sum.inr (Sum.inl (World.restrictStep g)) : Value.F.Rep (Later D) n) _ = _
      rw [ih]; congr 1; congr 1; symm; rw [World.restrict.eq_1, dif_neg h]

private theorem restrict_con_rep {n m : Nat} (K : Nat) (ds : List (Later D n)) (hm : m ≤ n) :
    @World.restrict (Value.F.Rep (Later D)) _ n m
      ((Sum.inr (Sum.inr (K, ds)) : Value.F.Rep (Later D) n)) hm =
    (Sum.inr (Sum.inr (K, World.restrict ds hm)) : Value.F.Rep (Later D) m) := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hm; simp [World.restrict.eq_1]
  | succ n ih =>
    rw [World.restrict.eq_1]; split
    · next h => subst h; rw [World.restrict.eq_1, dif_pos rfl]; simp only [cast_eq]
    · next h =>
      dsimp only []
      show @World.restrict (Value.F.Rep (Later D)) _ n m
        (Sum.inr (Sum.inr (K, World.restrictStep ds)) : Value.F.Rep (Later D) n) _ = _
      rw [ih]; congr 1; congr 1; congr 1; symm; rw [World.restrict.eq_1, dif_neg h]

private theorem restrict_Function_apply {A B : Nat → Type} {n m : Nat}
    (f : World.Function A B n) (hm : m ≤ n) (k : Nat) (hk : k ≤ m) (a : A k) :
    (World.restrict f hm) k hk a = f k (Nat.le_trans hk hm) a := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hm; simp [World.restrict.eq_1]
  | succ n ih =>
    rw [World.restrict.eq_1]; split
    · next h => subst h; simp [cast_eq]
    · next h =>
      show (World.restrict (World.restrictStep f) _) k hk a = f k _ a
      rw [ih]; rfl

private theorem mem_restrict_list {F : Nat → Type} [World F] {n m : Nat}
    (xs : List (F n)) (dl : F m) (hm : m ≤ n)
    (h : List.Mem dl (World.restrict (F := World.Comp List F) xs hm)) :
    ∃ x, List.Mem x xs ∧ dl = World.restrict x hm := by
  induction n generalizing m with
  | zero =>
    cases Nat.le_zero.mp hm
    simp only [World.restrict.eq_1, cast_eq] at h
    exact ⟨dl, h, by simp [World.restrict.eq_1]⟩
  | succ n ih =>
    rw [World.restrict.eq_1] at h; split at h
    · next heq =>
      subst heq; simp only [cast_eq] at h
      exact ⟨dl, h, by simp [World.restrict.eq_1]⟩
    · next hne =>
      change List.Mem dl (World.restrict (F := World.Comp List F) (xs.map World.restrictStep) _) at h
      have ⟨x', hx'_mem, hx'_eq⟩ := ih _ _ _ h
      obtain ⟨x, hx_mem, hx_rs⟩ := List.mem_map.mp hx'_mem
      refine ⟨x, hx_mem, ?_⟩
      subst hx_rs; rw [hx'_eq]
      symm; rw [World.restrict.eq_1]; simp only [dif_neg hne]

private theorem restrict_inl_unit {n m : Nat} (hm : m ≤ n) :
    @World.restrict (Value.F.Rep (Later D)) _ n m (Sum.inl PUnit.unit) hm = Sum.inl PUnit.unit := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hm; simp [World.restrict.eq_1]
  | succ n ih =>
    rw [World.restrict.eq_1]; split
    · next h => subst h; rfl
    · next h => exact ih (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hm h))

/-- `GoodD` for `D.ret .stuck`. -/
theorem GoodD_stuck {n : Nat} : GoodD n D.stuck := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  · simp only [D_ret_eq, D.stuck]; unfold StartsVisible TraceGood; simp
    exact ⟨trivial, fun g hg => absurd (restrict_inl_unit hm ▸ hg) nofun,
      fun K ds hds => absurd (restrict_inl_unit hm ▸ hds) nofun, hμ⟩

/-- `GoodD` for `D.ret (.fn g)` with the function value condition. -/
theorem GoodD_fn {n : Nat} (f : world(D → D) n)
    (hf : ∀ m (hm : m ≤ n) (dl : ▹ D m),
      GoodLater m dl → GoodLater m (Later.hmap m (fun k hk => f k (by omega)) dl)) :
    GoodD n (D.fn f) := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  · simp only [D_ret_eq, D.fn, Value.F.toRep, restrict_fn_rep]
    constructor
    · unfold StartsVisible; simp [T.ret, T_uf]
    · unfold TraceGood; simp [T.ret, T_uf]
      refine ⟨?_, ?_, ?_⟩
      · -- fn condition
        intro g' hg' k hk dl hdl
        have hinj := Sum.inl.inj (Sum.inr.inj hg')
        subst hinj
        rw [restrict_Function_apply]
        exact hf _ (Nat.le_trans (by omega) hm) dl hdl
      · -- con condition: vacuous
        intro K ds hds; exact absurd (Sum.inr.inj hds) nofun
      · -- heap condition
        exact hμ

/-- `GoodD` for `D.ret (.con K ds)` with the constructor field condition. -/
theorem GoodD_con {n : Nat} (K : ConTag) (ds : List (D n))
    (hds : ∀ d, d ∈ ds → GoodLater n (Later.next d)) :
    GoodD n (D.con K ds) := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  · simp only [D_ret_eq, D.con, Value.F.toRep, restrict_con_rep]
    constructor
    · unfold StartsVisible; simp [T.ret, T_uf]
    · unfold TraceGood; simp [T.ret, T_uf]
      refine ⟨?_, ?_, ?_⟩
      · -- fn condition: vacuous
        intro g hg; exact absurd (Sum.inr.inj hg) nofun
      · -- con condition
        intro K' ds' hds' dl hdl
        have ⟨hK, hds_eq⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hds'))
        subst hK; subst hds_eq
        -- dl ∈ World.restrict (ds.map Later.next) hm
        have ⟨x, hx_mem, hx_eq⟩ := mem_restrict_list _ _ _ hdl
        obtain ⟨d, hd_mem, rfl⟩ := List.mem_map.mp hx_mem
        rw [hx_eq]
        exact GoodLater_restrict _ (hds d hd_mem) _ _
      · -- heap condition
        exact hμ

theorem TraceGood_mono (k k' : Nat) (hkk : k ≤ k') (n : Nat) (t : T VH n) :
    TraceGood k n t → TraceGood k' n t := by
  induction n generalizing k k' with
  | zero => intro _; exact TraceGood_zero k' _
  | succ n ih =>
    intro h; unfold TraceGood at h ⊢
    generalize heq : T.unfold t = tu at h ⊢
    cases tu with
    | ret _ => exact h
    | step _ dl => exact ih 2 2 (Nat.le_refl _) dl h
    | invis dl =>
      cases k with
      | zero => exact absurd h id
      | succ j =>
        cases k' with
        | zero => omega
        | succ j' => exact ⟨h.1, ih j j' (by omega) dl h.2⟩

/-! ## T.bind preservation -/

theorem T_bind_NotRet' {n : Nat} (t : T VH n)
    (kont : world(VH → T VH) n) (ht_nr : NotRet n t) :
    NotRet n (T.bind t kont) := by
  cases n <;> simp_all +decide [NotRet]
  unfold T.bind
  cases h : t.unfold <;> simp_all +decide

/-
The core T.bind preservation lemma. The continuation receives the value conditions
    from the `ret` case of `TraceGood`.
-/
theorem T_bind_TraceGood (k : Nat) (hk : k ≤ 2) {n : Nat} (t : T VH n)
    (kont : world(VH → T VH) n) (ht : TraceGood k n t)
    (ht_nr : k < 2 → NotRet n t ∨ IsRetStuck n t)
    (hkont : ∀ j (hj : j ≤ n) (v : VH j),
      -- fn condition at level j
      (∀ (g : World.Function (Later D) (Later D) j),
        v.1 = .inr (.inl g) →
        ∀ k' (hk' : k' ≤ j) (dl : ▹ D k'),
          GoodLater k' dl → GoodLater k' (g k' (by omega) dl)) →
      -- con condition at level j
      (∀ (K : ConTag) (ds : List (▹ D j)),
        v.1 = .inr (.inr (K, ds)) →
        ∀ (dl : ▹ D j), dl ∈ ds → GoodLater j dl) →
      -- heap condition at level j
      (∀ a (dl : ▹ D j), Std.HashMap.get? v.2 a = some dl → GoodLater j dl) →
      TraceGood 2 j (kont j hj v))
    (hkont_stuck : ∀ j (hj : j ≤ n) (vh : VH j),
        vh.1 = Sum.inl PUnit.unit →
        (∀ a (dl : ▹ D j), Std.HashMap.get? vh.2 a = some dl → GoodLater j dl) →
        (NotRet j (kont j hj vh) ∨ IsRetStuck j (kont j hj vh)) ∧
        ∀ k', TraceGood k' j (kont j hj vh)) :
    TraceGood k n (T.bind t kont) := by
  induction n generalizing k with
  | zero => exact TraceGood_zero k _
  | succ n ih =>
    rw [T.bind.eq_1]
    generalize heq : T.unfold t = tu
    cases tu with
    | ret vh =>
      unfold TraceGood at ht; rw [heq] at ht
      by_cases h : vh.1 = Sum.inl PUnit.unit
      · exact (hkont_stuck _ (Nat.le_refl _) _ h ht.2.2).2 _
      · have hk2 : k = 2 := by
          have : ¬ k < 2 := fun hlt => by
            rcases ht_nr hlt with hr | hr
            · simp only [NotRet] at hr; rw [heq] at hr; exact hr
            · simp only [IsRetStuck] at hr; rw [heq] at hr; exact h hr
          omega
        subst hk2
        exact hkont (n+1) (Nat.le_refl _) vh
          (fun g hg k' hk' dl hdl => match k' with
            | 0 => GoodLater_zero _ | _ + 1 => ht.1 g hg _ (by omega) dl hdl)
          ht.2.1 ht.2.2
    | step ev dl =>
      dsimp only []
      unfold TraceGood; simp only [T_uf]
      unfold TraceGood at ht; rw [heq] at ht
      apply ih 2 (by omega) dl (World.restrict kont) ht
      · intro h; omega
      · intro j hj v hfn hcon hheap
        rw [restrict_Function_apply]
        exact hkont j (by omega) v hfn hcon hheap
      · intro j hj vh hv hheap
        constructor
        · have := (hkont_stuck j (by omega) vh hv hheap).1
          rwa [restrict_Function_apply]
        · intro k'
          have := (hkont_stuck j (by omega) vh hv hheap).2 k'
          rwa [restrict_Function_apply]
    | invis dl =>
      dsimp only []
      unfold TraceGood; simp only [T_uf]
      unfold TraceGood at ht; rw [heq] at ht
      cases k with
      | zero => exact ht
      | succ j =>
        obtain ⟨hnr, htj⟩ := ht
        constructor
        · cases hnr with
          | inl h => exact Or.inl (T_bind_NotRet' dl (World.restrict kont) h)
          | inr h =>
            rcases n with ( _ | n );
            · cases h;
            · obtain ⟨μ', hμ'⟩ : ∃ μ', T.unfold dl = .ret (Sum.inl PUnit.unit, μ') := by
                cases huf : T.unfold dl <;> simp +decide [IsRetStuck, huf] at h ⊢
                rename_i v; exact ⟨v.2, Prod.ext h rfl⟩
              unfold Later.hmap; simp +decide
              rw [show T.bind dl (World.restrict kont (by omega)) =
                    kont (n + 1) (by omega) (Sum.inl PUnit.unit, μ') from ?_]
              · exact (hkont_stuck _ _ _ rfl (fun a dl h => by
                    unfold TraceGood at htj; simp +decide [hμ'] at htj; exact htj a dl h)).1
              · grind +suggestions
        · apply ih j (by omega) dl (World.restrict kont) htj
          · intro _; exact hnr
          · intro j' hj' v hfn hcon hheap
            rw [restrict_Function_apply]
            exact hkont j' (by omega) v hfn hcon hheap
          · intro j' hj' vh hv hheap
            constructor
            · have := (hkont_stuck j' (by omega) vh hv hheap).1
              rwa [restrict_Function_apply]
            · intro k'
              have := (hkont_stuck j' (by omega) vh hv hheap).2 k'
              rwa [restrict_Function_apply]

theorem T_bind_StartsVisible {n : Nat} (t : T VH n)
    (kont : world(VH → T VH) n) (ht_sv : StartsVisible n t) (ht_nr : NotRet n t) :
    StartsVisible n (T.bind t kont) := by
  cases n
  · exact StartsVisible_zero _
  · unfold T.bind StartsVisible at *; cases h : t.unfold <;> simp_all +decide [NotRet]

theorem T_bind_NotRet {n : Nat} (t : T VH n)
    (kont : world(VH → T VH) n) (ht_nr : NotRet n t) :
    NotRet n (T.bind t kont) := by
  cases n <;> simp_all +decide [NotRet]
  unfold T.bind; cases h : t.unfold <;> simp_all +decide

/-! ## D.step closure -/

theorem GoodD_step_of_GoodLater {n : Nat} (ev : Event) (dl : ▹ D n)
    (hdl : GoodLater n dl) : GoodD n (D.step ev dl) := by
  intro m hm μ hμ; rcases m with _ | m
  · exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  · simp only [D_step_eq]; unfold StartsVisible TraceGood; simp +decide [T.step, T_uf]
    have h_gl := GoodLater_restrict dl hdl (m + 1) hm
    unfold GoodLater at h_gl
    exact (h_gl m (Nat.le_refl m) _ (GoodHeap_restrict μ hμ (by omega))).2

private theorem restrict_later_next {n : Nat} (d : D n) (k : Nat) (hk : k + 1 ≤ n) :
    @World.restrict (Later D) _ n (k+1) (Later.next d) hk =
    @World.restrict D _ n k d (by omega) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases hkn' : k = n
    · subst hkn'
      rw [World.restrict.eq_1 (F := Later D), dif_pos rfl]
      rw [World.restrict.eq_1 (F := D), dif_neg (by omega)]
      dsimp only []
      rw [World.restrict.eq_1, dif_pos rfl]
      simp only [cast_eq]; rfl
    · rw [World.restrict.eq_1 (F := Later D), dif_neg (by omega)]
      dsimp only []
      rw [World.restrict.eq_1 (F := D), dif_neg (by omega)]
      dsimp only []
      exact ih (World.restrictStep d) k (by omega)

/-- `GoodD d` implies `GoodLater (n+1) (D.step ev (Later.next d))`.
    Wrapping any GoodD value in a step produces a GoodLater value. -/
theorem GoodLater_of_step {n : Nat} (ev : Event) (d : D n) (hd : GoodD n d) :
    GoodLater (n + 1) (D.step ev (Later.next d)) := by
  unfold GoodLater; intro k hk μ hμ
  simp only [unfoldLater, D_step_eq]
  constructor
  · rcases k with _ | k <;> simp [StartsWithStep, T.step, T_uf]
  · rcases k with _ | k
    · exact TraceGood_zero 2 _
    · unfold TraceGood; simp [T.step, T_uf]
      show TraceGood 2 k ((World.restrict (Later.next d) hk).unfold k (Nat.le_refl k) (World.restrict μ (by omega)))
      rw [restrict_later_next, D_unfold_restrict]
      exact (hd k (by omega) _ (GoodHeap_restrict μ hμ (by omega))).2

/-! ## Fundamental lemma -/

/-
`GoodHeap` is preserved by `Heap.set`.
-/
theorem GoodHeap_set {n : Nat} (μ : Heap (▹ D) n) (hμ : GoodHeap n μ)
    (a : Addr) (dl : ▹ D n) (hdl : GoodLater n dl) :
    GoodHeap n (Heap.set μ a dl) := by
  intro b db hdb
  simp only [Heap.set, Std.HashMap.get?_eq_getElem?] at hdb
  rw [Std.HashMap.getElem?_insert] at hdb
  split at hdb
  · cases hdb; exact hdl
  · exact hμ b db (by rwa [Std.HashMap.get?_eq_getElem?])

/-
`GoodEnv` is preserved by restriction (Functor.map version).
-/
theorem GoodEnv_restrict {n m : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (hm : m ≤ n) : GoodEnv (Functor.map (World.restrict (hm := hm)) ρ) := by
  intro x d hd k hk μ hμ
  have hfind : Env.find? ((fun x => World.restrict x hm) <$> ρ) x =
      Option.map (fun x => World.restrict x hm) (Env.find? ρ x) := AddrMap_get?_map _ _ _
  rw [hfind] at hd
  cases hget : Env.find? ρ x with
  | none => simp [hget] at hd
  | some d' =>
    simp [hget] at hd; subst hd; simp only [D_unfold_restrict]
    exact hρ x d' hget k (Nat.le_trans hk hm) μ hμ

/-- `GoodEnv` is preserved by `World.restrictStep`. -/
theorem GoodEnv_restrictStep {n : Nat} (ρ : Heap D (n+1)) (hρ : GoodEnv ρ) :
    GoodEnv (World.restrictStep (F := Heap D) ρ) := by
  intro x d hd k hk μ hμ
  have h_map : Std.HashMap.get? (World.restrictStep (F := Heap D) ρ) x =
      Option.map World.restrictStep (Std.HashMap.get? ρ x) := by
    show Std.HashMap.get? (Functor.map World.restrictStep ρ) x = _
    exact AddrMap_get?_map _ ρ x
  rw [show Env.find? _ x = Std.HashMap.get? _ x from rfl, h_map] at hd
  cases hget : Std.HashMap.get? ρ x with
  | none => rw [hget] at hd; exact absurd hd (by simp [Option.map])
  | some d' =>
    rw [hget] at hd; simp [Option.map] at hd; subst hd
    rw [D_unfold_restrictStep]
    exact hρ x d' (by rwa [show Env.find? ρ x = Std.HashMap.get? ρ x from rfl])
           k (Nat.le_succ_of_le hk) μ hμ

/-- `GoodEnv` is preserved by `World.restrict` (direct version). -/
theorem GoodEnv_world_restrict {n m : Nat} (ρ : Heap D n) (hρ : GoodEnv ρ)
    (hm : m ≤ n) : GoodEnv (World.restrict (F := Heap D) ρ hm) := by
  rw [World.restrict.eq_1]; split
  · next heq => subst heq; exact hρ
  · next hne => match n with
    | 0 => exact absurd (Nat.le_zero.mp hm) hne
    | _ + 1 => exact GoodEnv_world_restrict _ (GoodEnv_restrictStep ρ hρ) _

/-
`GoodEnv` is preserved by bind.
-/
theorem GoodEnv_bind {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (x : Var) (d : D n)
    (hd : ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)) :
    GoodEnv (ρ.bind x d) := by
  intro y d' hfind k hk μ hμ
  simp only [Env.bind, Env.find?, Std.HashMap.get?_eq_getElem?] at hfind
  rw [Std.HashMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind; exact hd k hk μ hμ
  · exact hρ y d' (by rwa [Env.find?, Std.HashMap.get?_eq_getElem?]) k hk μ hμ

theorem StartsWithStep_imp_StartsVisible {n : Nat} {t : T VH n}
    (h : StartsWithStep n t) : StartsVisible n t := by
  cases n with
  | zero => trivial
  | succ n => simp only [StartsWithStep] at h; simp only [StartsVisible]
              generalize T.unfold t = tu at h ⊢; cases tu <;> simp_all +decide

theorem TraceGood_0_of_StartsWithStep (n : Nat) (t : T VH n)
    (hs : StartsWithStep n t) (hg : TraceGood 2 n t) : TraceGood 0 n t := by
  cases n with
  | zero => exact TraceGood_zero 0 t
  | succ n =>
    simp only [StartsWithStep] at hs
    unfold TraceGood at hg ⊢
    generalize heq : T.unfold t = tu at hs hg ⊢
    cases tu with
    | ret _ => exact hg
    | step _ dl => exact hg
    | invis _ => simp_all +decide

theorem StartsWithStep_imp_NotRet {n : Nat} {t : T VH n}
    (h : StartsWithStep n t) : NotRet n t := by
  cases n with
  | zero => trivial
  | succ n => simp only [StartsWithStep] at h; simp only [NotRet]
              generalize T.unfold t = tu at h ⊢; cases tu <;> simp_all +decide

theorem GoodD_of_GoodLater {n : Nat} (d : D n) (hd : GoodLater (n + 1) d) :
    GoodD n d := by
  intro m hm μ hμ
  unfold GoodLater at hd
  have h' := hd m hm μ hμ
  simp only [unfoldLater] at h'
  exact ⟨StartsWithStep_imp_StartsVisible h'.1, h'.2⟩

theorem GoodEnv_to_GoodD {n : Nat} {ρ : Env (D n)} (hρ : GoodEnv ρ) (x : Var) (d : D n)
    (hfind : ρ.find? x = some d) : GoodD n d := by
  intro m hm μ hμ
  have h := hρ x d hfind m hm μ hμ
  exact ⟨StartsWithStep_imp_StartsVisible h.1, h.2⟩

theorem GoodEnv_to_GoodLater_next {n : Nat} {ρ : Env (D n)} (hρ : GoodEnv ρ) (x : Var) (d : D n)
    (hfind : ρ.find? x = some d) : GoodLater n (Later.next d) := by
  cases n with
  | zero => exact GoodLater_zero _
  | succ n =>
    unfold GoodLater; intro k hk μ hμ
    simp only [unfoldLater]
    show StartsWithStep k ((World.restrictStep d).unfold k hk μ) ∧
         TraceGood 2 k ((World.restrictStep d).unfold k hk μ)
    rw [D_unfold_restrictStep]
    exact hρ x d hfind k (Nat.le_succ_of_le hk) μ hμ

/-
Helper: Env.pmapList gives entries with GoodEnv-strength conditions.
-/
theorem pmapList_good {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (xs : List Var) (ds : List (D n)) (hds : ρ.pmapList xs = some ds) :
    ∀ d, d ∈ ds → ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ) := by
  have h_exists_x : ∀ d ∈ ds, ∃ x ∈ xs, ρ.find? x = some d := by
    induction xs generalizing ds <;> simp_all +decide [Env.pmapList]
    cases h : ρ.find? ‹_› <;> simp_all +decide [Option.bind_eq_some_iff]; grind
  exact fun d hd m hm μ hμ =>
    hρ _ _ (h_exists_x d hd |> Classical.choose_spec |> And.right) m hm μ hμ

/-
Helper: Env.bindMany preserves GoodEnv.
-/
theorem GoodEnv_bindMany {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (xs : List Var) (ds : List (D n))
    (hds : ∀ d, d ∈ ds → ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)) :
    GoodEnv (ρ.bindMany xs ds) := by
  unfold Env.bindMany; induction xs generalizing ρ ds with
  | nil => simp [List.zip]; exact hρ
  | cons x xs ih => cases ds with
    | nil => simp [List.zip]; exact hρ
    | cons d ds =>
      simp [List.zip]
      apply ih (Std.HashMap.insert ρ x d)
      · exact GoodEnv_bind ρ hρ x d (fun m hm μ hμ => hds d (.head _) m hm μ hμ)
      · intro d' hd' m hm μ hμ; exact hds d' (.tail _ hd') m hm μ hμ

/-- Fundamental lemma for .ref -/
theorem fundamental_ref (x : Var) {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ) :
    GoodD n (eval (D := D) (.ref x) n (Nat.le_refl n) ρ) := by
  simp [eval]
  cases h : ρ.find? x with
  | none => exact GoodD_stuck
  | some d => exact GoodEnv_to_GoodD hρ x d h

/-- Fundamental lemma for .conapp -/
theorem fundamental_conapp (K : ConTag) (xs : List Var) {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ) :
    GoodD n (eval (D := D) (.conapp K xs) n (Nat.le_refl n) ρ) := by
  simp [eval, Domain.con']
  cases h : ρ.pmapList xs with
  | none => exact GoodD_stuck
  | some ds =>
    apply GoodD_con
    intro d hd
    have hgood := pmapList_good ρ hρ xs ds h d hd
    -- Convert StartsWithStep + TraceGood to GoodLater n (Later.next d)
    cases n with
    | zero => exact GoodLater_zero _
    | succ n =>
      unfold GoodLater; intro k hk μ hμ
      simp only [unfoldLater]
      show StartsWithStep k ((World.restrictStep d).unfold k hk μ) ∧
           TraceGood 2 k ((World.restrictStep d).unfold k hk μ)
      rw [D_unfold_restrictStep]
      exact hgood k (Nat.le_succ_of_le hk) μ hμ

/-- Helper: GoodLater (k+1) dl gives the GoodEnv condition for dl : D k -/
theorem GoodLater_to_GoodEnv_cond {k : Nat} (dl : D k) (hdl : GoodLater (k+1) dl) :
    ∀ m (hm : m ≤ k) μ, GoodHeap m μ →
      StartsWithStep m (dl.unfold m hm μ) ∧ TraceGood 2 m (dl.unfold m hm μ) := by
  intro m hm μ hμ
  unfold GoodLater at hdl
  exact hdl m hm μ hμ

/-
If d produces TraceGood 2 at all levels, then D.step ev (Later.next d) has GoodD.
-/
theorem GoodD_step_of_TraceGood {n : Nat} (ev : Event) (d : D n)
    (hd : ∀ m (hm : m ≤ n) μ, GoodHeap m μ → TraceGood 2 m (d.unfold m hm μ)) :
    GoodD n (D.step ev (Later.next d)) := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  · simp only [D_step_eq]
    constructor
    · unfold StartsVisible; simp [T.step, T_uf]
    · unfold TraceGood; simp [T.step, T_uf]
      rw [restrict_later_next]
      show TraceGood 2 m ((World.restrict d (by omega)).unfold m (Nat.le_refl m) (World.restrict μ (by omega)))
      rw [D_unfold_restrict]
      exact hd m (by omega) _ (GoodHeap_restrict μ hμ _)

/-
D.bind preserves TraceGood 2 when d has GoodD and kont produces GoodD from value conditions.
-/
theorem D_bind_TraceGood {n : Nat} (d : D n)
    (kont : World.Function (Value.F (Later D)) D n)
    (hd : GoodD n d)
    (hkont : ∀ j (hj : j ≤ n) (vh : VH j),
      (∀ (g : World.Function (Later D) (Later D) j),
        vh.1 = .inr (.inl g) →
        ∀ k' (hk' : k' ≤ j) (dl : ▹ D k'),
          GoodLater k' dl → GoodLater k' (g k' (by omega) dl)) →
      (∀ (K : ConTag) (ds : List (▹ D j)),
        vh.1 = .inr (.inr (K, ds)) →
        ∀ (dl : ▹ D j), dl ∈ ds → GoodLater j dl) →
      (∀ a (dl : ▹ D j), Std.HashMap.get? vh.2 a = some dl → GoodLater j dl) →
      TraceGood 2 j ((kont j hj (Value.F.ofRep _ vh.1)).unfold j (Nat.le_refl j) vh.2))
    (hkont_stuck : ∀ j (hj : j ≤ n) (μ' : Heap (▹ D) j),
      (∀ a (dl : ▹ D j), Std.HashMap.get? μ' a = some dl → GoodLater j dl) →
      (NotRet j ((kont j (by omega) (Value.F.ofRep _ (Sum.inl PUnit.unit))).unfold j (Nat.le_refl j) μ') ∨
       IsRetStuck j ((kont j (by omega) (Value.F.ofRep _ (Sum.inl PUnit.unit))).unfold j (Nat.le_refl j) μ')) ∧
      ∀ k', TraceGood k' j ((kont j (by omega) (Value.F.ofRep _ (Sum.inl PUnit.unit))).unfold j (Nat.le_refl j) μ')) :
    ∀ m (hm : m ≤ n) μ, GoodHeap m μ →
      TraceGood 2 m ((D.bind d kont).unfold m hm μ) := by
  simp +decide [D_bind_eq]; intro m hm μ hμ
  exact T_bind_TraceGood 2 (by omega) _ _ (hd m hm μ hμ).2
    (by omega) (fun j hj v hv₁ hv₂ hv₃ => hkont j (by omega) v hv₁ hv₂ hv₃)
    (fun j hj ⟨v, μ'⟩ hvh hheap => by subst hvh; exact hkont_stuck j (by omega) μ' hheap)

/-
At a step-starting trace, TraceGood is independent of budget.
-/
theorem TraceGood_of_StartsWithStep {k k' n : Nat} {t : T VH n}
    (hs : StartsWithStep n t) (ht : TraceGood k n t) : TraceGood k' n t := by
  cases n with
  | zero => exact TraceGood_zero k' t
  | succ => unfold TraceGood at *; cases h : t.unfold <;> simp_all +decide [StartsWithStep]

/-
GoodD for D.invis wrapping a GoodLater value.
-/
theorem GoodD_invis_of_GoodLater {n : Nat} (dl : ▹ D n) (hdl : GoodLater n dl) :
    ∀ m (hm : m ≤ n) μ, GoodHeap m μ → TraceGood 2 m ((D.invis dl).unfold m hm μ) := by
  intro m hm μ hμ; cases m with
  | zero => exact TraceGood_zero 2 _
  | succ m₁ =>
    simp only [D_invis_eq]; unfold TraceGood; simp [T_uf]
    have hgl := GoodLater_restrict dl hdl (m₁ + 1) (by omega)
    unfold GoodLater at hgl
    have hp := hgl m₁ (Nat.le_refl m₁) _ (GoodHeap_restrict μ hμ (by omega))
    exact ⟨Or.inl (StartsWithStep_imp_NotRet hp.1), TraceGood_of_StartsWithStep hp.1 hp.2⟩

/-
`Later.next (World.restrict entry hj)` is `GoodLater j` when `entry` comes from a `GoodEnv`.
-/
theorem GoodLater_entry_restrict {n j : Nat} {ρ : Env (D n)} (hρ : GoodEnv ρ)
    (x : Var) (entry : D n) (hfind : ρ.find? x = some entry) (hj : j ≤ n) :
    GoodLater j (Later.next (World.restrict entry hj)) := by
  cases j with
  | zero => exact GoodLater_zero _
  | succ k =>
    unfold GoodLater; intro m hm μ hμ
    simp only [unfoldLater]
    have h_eq : unfoldLater (Later.next (World.restrict entry hj)) m hm μ =
        entry.unfold m (by omega) μ := by
      show (World.restrictStep (World.restrict entry hj)).unfold m hm μ = _
      rw [D_unfold_restrictStep, D_unfold_restrict]
    simp only [h_eq]
    exact hρ x entry hfind m (by omega) μ hμ

theorem apply_kont_TraceGood {n : Nat} {ρ : Env (D n)} {x : Var} (entry : D n) (hρ : GoodEnv ρ) (hfind : ρ.find? x = some entry)
    {j : Nat} (hj : j ≤ n) (vh : VH j)
    (hfn : ∀ (g : World.Function (Later D) (Later D) j),
      vh.1 = .inr (.inl g) → ∀ k' (hk' : k' ≤ j) (dl : ▹ D k'),
        GoodLater k' dl → GoodLater k' (g k' (by omega) dl))
    (hcon : ∀ (K : ConTag) (ds : List (▹ D j)),
      vh.1 = .inr (.inr (K, ds)) → ∀ (dl : ▹ D j), dl ∈ ds → GoodLater j dl)
    (hheap : ∀ a (dl : ▹ D j), Std.HashMap.get? vh.2 a = some dl → GoodLater j dl) :
    TraceGood 2 j ((match Value.F.ofRep (Later D) vh.1 with
      | .fn g => D.invis (g j (Nat.le_refl j) (Later.next (World.restrict entry)))
      | _ => D.stuck).unfold j (Nat.le_refl j) vh.2) := by
        unfold Value.F.ofRep
        rcases vh with ⟨v, μ⟩
        rcases v with (_ | (g | ⟨K, ds⟩))
        · -- stuck case
          simp; exact (GoodD_stuck j (Nat.le_refl j) μ hheap).2
        · -- fn case
          show TraceGood 2 j ((D.invis (g j (Nat.le_refl j) (Later.next (World.restrict entry (hm := hj))))).unfold j (Nat.le_refl j) μ)
          exact GoodD_invis_of_GoodLater _ (hfn g rfl j (Nat.le_refl j) _
            (GoodLater_entry_restrict hρ x entry hfind hj)) j (Nat.le_refl j) μ hheap
        · -- con case
          simp; exact (GoodD_stuck j (Nat.le_refl j) μ hheap).2

/-
D.stuck produces IsRetStuck and TraceGood k' for any k' at any good heap.
-/
theorem stuck_unfold_good (j : Nat) (μ : Heap (▹ D) j)
    (hμ : ∀ a (dl : ▹ D j), Std.HashMap.get? μ a = some dl → GoodLater j dl) :
    (NotRet j (D.stuck.unfold j (Nat.le_refl j) μ) ∨
     IsRetStuck j (D.stuck.unfold j (Nat.le_refl j) μ)) ∧
    ∀ k', TraceGood k' j (D.stuck.unfold j (Nat.le_refl j) μ) := by
  rcases j with _ | j
  · exact ⟨Or.inl trivial, fun k' => TraceGood_zero k' _⟩
  · simp only [D.stuck, D_ret_eq]
    have hrep : World.restrict (Value.F.toRep (▹ D) Value.F.stuck) (Nat.le_refl (j + 1)) =
        Sum.inl PUnit.unit := restrict_inl_unit _
    constructor
    · right; simp only [IsRetStuck, T.ret, T_uf, hrep]
    · intro k'; simp only [TraceGood, T.ret, T_uf, hrep]
      exact ⟨fun g hg => absurd hg (by simp), fun K ds hds => absurd hds (by simp), hμ⟩

/-- Fundamental lemma for .app -/
theorem fundamental_app (e₁ : Exp) (x : Var) {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (ih_e₁ : ∀ {m : Nat} (ρ' : Env (D m)), GoodEnv ρ' →
      GoodD m (eval (D := D) e₁ m (Nat.le_refl m) ρ')) :
    GoodD n (eval (D := D) (.app e₁ x) n (Nat.le_refl n) ρ) := by
  simp only [eval.eq_3]
  cases hfind : ρ.find? x with
  | none => exact GoodD_stuck
  | some entry =>
    -- Unfold Domain.apply' to D.bind
    show GoodD n (D.step .app1 (Later.next
      (D.bind (World.restrict (eval (D := D) e₁ n (Nat.le_refl n) ρ))
        (fun j hj v => match v with
          | .fn g => D.invis (g j (Nat.le_refl j) (Later.next (World.restrict entry)))
          | _ => D.stuck))))
    apply GoodD_step_of_TraceGood
    -- World.restrict with le_refl is identity
    have h_restr : World.restrict (eval (D := D) e₁ n (Nat.le_refl n) ρ) = eval (D := D) e₁ n (Nat.le_refl n) ρ := by
      rw [World.restrict.eq_1, dif_pos rfl]; simp
    rw [h_restr]
    apply D_bind_TraceGood _ _ (ih_e₁ ρ hρ)
    · exact fun j hj vh hfn hcon hheap =>
        apply_kont_TraceGood entry hρ hfind hj vh hfn hcon hheap
    · -- hkont_stuck: at stuck values, the apply kont produces D.stuck
      intro j hj μ' hμ'
      -- Value.F.ofRep _ (Sum.inl PUnit.unit) = .stuck, match reduces to D.stuck
      show (NotRet j (D.stuck.unfold j _ μ') ∨ IsRetStuck j (D.stuck.unfold j _ μ')) ∧
           ∀ k', TraceGood k' j (D.stuck.unfold j _ μ')
      exact stuck_unfold_good j μ' hμ'

/-- Later.sequence at succ level is the identity. -/
theorem Later_sequence_succ {k : Nat} (ds : List (D k)) :
    @Later.sequence D _ (k+1) ds = ds := by
  induction ds with
  | nil =>
    dsimp [Later.sequence, List.foldr, Later.next]
    rfl
  | cons d ds ih =>
    dsimp only [Later.sequence, List.foldr, Function.comp, Later.map, Later.ap] at ih ⊢
    rw [ih]

/-- If Value.F.ofRep gives .con K ds, then the input was Sum.inr (Sum.inr (K, ds)) -/
theorem Value_F_ofRep_con_inv {F : Nat → Type} [World F] {n : Nat}
    {v : Value.F.Rep F n} {K : ConTag} {ds : List (F n)}
    (h : Value.F.ofRep F v = Value.F.con K ds) :
    v = Sum.inr (Sum.inr (K, ds)) := by
  rcases v with (u | (_ | ⟨K', ds'⟩))
  · cases u; simp [Value.F.ofRep] at h
  · simp [Value.F.ofRep] at h
  · simp [Value.F.ofRep] at h; rcases h with ⟨rfl, rfl⟩; rfl

/-
Fundamental lemma for .case'
-/
theorem fundamental_case (eₛ : Exp) (alts : List Alt) {n : Nat}
    (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (ih_eₛ : ∀ {m : Nat} (ρ' : Env (D m)), GoodEnv ρ' →
      GoodD m (eval (D := D) eₛ m (Nat.le_refl m) ρ'))
    (ih_alts : ∀ alt, alt ∈ alts → ∀ {m : Nat} (ρ' : Env (D m)), GoodEnv ρ' →
      GoodD m (eval (D := D) alt.rhs m (Nat.le_refl m) ρ')) :
    GoodD n (eval (D := D) (.case' eₛ alts) n (Nat.le_refl n) ρ) := by
  simp only [eval.eq_5]
  -- Goal: GoodD n (Domain.step' .case1 (Domain.select' (eval eₛ) alts_map))
  -- Domain.step' .case1 X = D.step .case1 (Later.next X) definitionally
  apply GoodD_step_of_TraceGood
  -- Goal: ∀ m hm μ, GoodHeap m μ → TraceGood 2 m ((Domain.select' ...).unfold m hm μ)
  -- Domain.select' for ByNeed = D.bind (dv↓) select_kont
  have h_restr : World.restrict (eval (D := D) eₛ n (Nat.le_refl n) ρ) = eval (D := D) eₛ n (Nat.le_refl n) ρ := by
    rw [World.restrict.eq_1, dif_pos rfl]; simp
  intro m hm μ hμ
  simp only [Domain.select', Domain.select, h_restr]
  apply D_bind_TraceGood _ _ (ih_eₛ ρ hρ) _ _ m hm μ hμ
  · intro j hj vh hfn hcon hheap
    -- The goal has nested matches. Use split to case-split.
    split
    next K ds heq =>
      -- heq : Value.F.ofRep (Later D) vh.fst = Value.F.con K ds
      -- Split on List.find? result
      split
      next _ f hfind =>
        -- found matching alt: D.invis (Later.hmap j ... (Later.sequence j ds))
        apply GoodD_invis_of_GoodLater _ _ j (Nat.le_refl j) vh.2 hheap;
        cases j <;> simp_all +decide [ Later_sequence_succ ];
        · exact GoodLater_zero _;
        · obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := hfind;
          rw [ ← ha₃ ];
          apply GoodLater_of_step;
          apply ih_alts a (by
          exact List.mem_of_find?_eq_some ha₁);
          apply GoodEnv_bindMany;
          · exact GoodEnv_world_restrict ρ hρ _;
          · intro d hd m hm μ hμ;
            have := hcon K ds ( Value_F_ofRep_con_inv heq ) d hd;
            exact GoodLater_to_GoodEnv_cond d this m hm μ hμ
      next hfind =>
        -- no matching alt: D.stuck
        exact (GoodD_stuck j (Nat.le_refl j) vh.2 (by simpa using hheap)).2
    next => exact (GoodD_stuck j (Nat.le_refl j) vh.2 (by simpa using hheap)).2
  · -- hkont_stuck for select: at stuck, the select kont produces D.stuck
    intro j hj μ' hμ'
    show (NotRet j (D.stuck.unfold j _ μ') ∨ IsRetStuck j (D.stuck.unfold j _ μ')) ∧
         ∀ k', TraceGood k' j (D.stuck.unfold j _ μ')
    exact stuck_unfold_good j μ' hμ'

/-! ## Heap-invariant versions for the let case -/

/-- GoodD relative to a heap invariant Inv. -/
noncomputable def GoodD_Inv (Inv : ∀ m, Heap (▹ D) m → Prop) (n : Nat) (d : D n) : Prop :=
  ∀ m (hm : m ≤ n) μ, GoodHeap m μ → Inv m μ →
    StartsVisible m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)

/-- GoodEnv relative to a heap invariant Inv. -/
noncomputable def GoodEnv_Inv (Inv : ∀ m, Heap (▹ D) m → Prop) {n : Nat} (ρ : Env (D n)) : Prop :=
  ∀ x d, ρ.find? x = some d →
    ∀ m (hm : m ≤ n) μ, GoodHeap m μ → Inv m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)

theorem GoodD_to_Inv {Inv : ∀ m, Heap (▹ D) m → Prop} {n : Nat} {d : D n}
    (hd : GoodD n d) : GoodD_Inv Inv n d := fun m hm μ hμ _ => hd m hm μ hμ

theorem GoodEnv_to_Inv {Inv : ∀ m, Heap (▹ D) m → Prop} {n : Nat} {ρ : Env (D n)}
    (hρ : GoodEnv ρ) : GoodEnv_Inv Inv ρ := fun x d hfind m hm μ hμ _ => hρ x d hfind m hm μ hμ

theorem GoodEnv_Inv_to_GoodD_Inv {Inv : ∀ m, Heap (▹ D) m → Prop} {n : Nat}
    {ρ : Env (D n)} (hρ : GoodEnv_Inv Inv ρ) (x : Var) (d : D n)
    (hfind : ρ.find? x = some d) : GoodD_Inv Inv n d := fun m hm μ hμ hInv =>
  ⟨StartsWithStep_imp_StartsVisible (hρ x d hfind m hm μ hμ hInv).1,
   (hρ x d hfind m hm μ hμ hInv).2⟩

theorem GoodEnv_Inv_world_restrict {Inv : ∀ m, Heap (▹ D) m → Prop}
    {n m : Nat} (ρ : Heap D n) (hρ : GoodEnv_Inv Inv ρ) (hm : m ≤ n) :
    GoodEnv_Inv Inv (Functor.map (World.restrict (hm := hm)) ρ) := by
  intro x d hd k hk μ hμ hInv
  have hfind : Env.find? ((fun x => World.restrict x hm) <$> ρ) x =
      Option.map (fun x => World.restrict x hm) (Env.find? ρ x) := by
    show Std.HashMap.get? (Functor.map _ ρ) x = _
    exact AddrMap_get?_map _ _ _
  rw [hfind] at hd
  cases hget : Env.find? ρ x with
  | none => simp [hget] at hd
  | some d' =>
    simp [hget] at hd; subst hd
    simp only [D_unfold_restrict]
    exact hρ x d' hget k (Nat.le_trans hk hm) μ hμ hInv

theorem GoodEnv_Inv_bind {Inv : ∀ m, Heap (▹ D) m → Prop} {n : Nat}
    (ρ : Env (D n)) (hρ : GoodEnv_Inv Inv ρ)
    (x : Var) (d : D n)
    (hd : ∀ m (hm : m ≤ n) μ, GoodHeap m μ → Inv m μ →
      StartsWithStep m (d.unfold m hm μ) ∧ TraceGood 2 m (d.unfold m hm μ)) :
    GoodEnv_Inv Inv (ρ.bind x d) := by
  intro y d' hfind k hk μ hμ hInv
  simp only [Env.bind, Env.find?, Std.HashMap.get?_eq_getElem?] at hfind
  rw [Std.HashMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind; exact hd k hk μ hμ hInv
  · exact hρ y d' (by rwa [Env.find?, Std.HashMap.get?_eq_getElem?]) k hk μ hμ hInv


/-- The fetch-based entry for the let-bound variable satisfies GoodEnv conditions.
    At heaps with address a: step → invis → invis → d_at_a (good from GoodHeap).
    At heaps without a: step → invis → ret(stuck) (OK with IsRetStuck relaxation). -/
theorem fetch_entry_good (x : Var) (a : Addr) {n : Nat} :
    ∀ m (hm : m ≤ n) (μ : Heap (▹ D) m), GoodHeap m μ →
      StartsWithStep m ((D.step (.look x) (Later.next (D.invis (fetch a)))).unfold m hm μ) ∧
      TraceGood 2 m ((D.step (.look x) (Later.next (D.invis (fetch a)))).unfold m hm μ) := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨trivial, TraceGood_zero _ _⟩
  · simp only [D_step_eq]
    constructor
    · unfold StartsWithStep; simp [T.step, T_uf]
    · unfold TraceGood; simp [T.step, T_uf]
      -- Goal: TraceGood 2 m of the inner (D.invis (fetch a) unfolded)
      rw [restrict_later_next]
      show TraceGood 2 m ((World.restrict (D.invis (fetch a)) (by omega)).unfold m (Nat.le_refl m) (World.restrict μ (by omega)))
      rw [D_unfold_restrict]
      -- TraceGood 2 m of D.invis (fetch a) at some heap
      -- Need to unfold D.invis and fetch and case-split
      have hμ' := GoodHeap_restrict μ hμ (m := m) (by omega)
      -- At level m, D.invis wraps fetch a
      rcases m with _ | k
      · exact TraceGood_zero _ _
      · -- D.invis (fetch a) at level k+1 at heap μ''
        simp only [D_invis_eq]
        unfold TraceGood; simp only [T_uf]
        -- Reduce Later.hmap (k+1) f x = f k _ x
        unfold fetch
        rw [restrict_later_next]
        dsimp only [Later.hmap]
        -- Now the goal has (World.restrict (D.fold body) _).unfold k _ heap'
        rw [D_unfold_restrict]
        simp only [D_fold_unfold]
        -- Now case split on Std.HashMap.get? heap' a
        have hμ_k : GoodHeap k (World.restrict (World.restrict μ _) _) :=
          GoodHeap_restrict _ hμ' (m := k) (by omega)
        rcases hget : Std.HashMap.get? (World.restrict (World.restrict μ _) _) a with _ | dl
        · -- none case: T.ret (stuck, heap_k)
          rcases k with _ | j
          · exact ⟨Or.inl trivial, TraceGood_zero 1 _⟩
          · constructor
            · right; unfold IsRetStuck; simp [T.ret, T_uf, Value.F.toRep]
            · unfold TraceGood; simp [T.ret, T_uf]
              exact ⟨fun g hg => absurd hg (by simp [Value.F.toRep]),
                     fun K ds hds => absurd hds (by simp [Value.F.toRep]),
                     fun a' dl' h' => hμ_k a' dl' h'⟩
        · -- some dl case: T.fold (.invis (Later.hmap k ... dl))
          have hdl := hμ_k a dl hget
          rcases k with _ | j
          · exact ⟨Or.inl trivial, TraceGood_zero 1 _⟩
          · -- T.fold (.invis (dl.unfold j _ heap')) at level j+1
            constructor
            · left; unfold NotRet; simp [T_uf]
            · unfold TraceGood; simp [T_uf]
              -- Need (NotRet ∨ IsRetStuck) ∧ TraceGood 0 of dl.unfold j _ heap'
              have h_heap_j := GoodHeap_restrict _ hμ_k (m := j) (by omega)
              unfold GoodLater at hdl
              have ⟨h_sws, h_tg2⟩ := hdl j (Nat.le_refl j) _ h_heap_j
              exact ⟨Or.inl (StartsWithStep_imp_NotRet h_sws),
                     TraceGood_0_of_StartsWithStep j _ h_sws h_tg2⟩

/-
StartsWithStep is preserved by T.bind when inner starts visibly and kont starts with step at ret.
-/
theorem StartsWithStep_bind_of_visible {n : Nat} (t : T VH n)
    (kont : World.Function VH (T VH) n)
    (hv : StartsVisible n t)
    (hk : ∀ j (hj : j ≤ n) (vh : VH j), StartsWithStep j (kont j hj vh)) :
    StartsWithStep n (T.bind t kont) := by
  cases n with
  | zero => trivial
  | succ n =>
    unfold T.bind
    cases h : t.unfold <;> simp_all +decide [StartsWithStep]
    · exact hk _ (Nat.le_refl _) _
    · unfold StartsVisible at hv; simp [h] at hv

@[simp] private theorem Value_F_toRep_ofRep {F : Nat → Type} [World F] {n : Nat}
    (v : Value.F.Rep F n) : Value.F.toRep F (Value.F.ofRep F v) = v := by
  rcases v with (u | (g | ⟨K, ds⟩)) <;> first | (cases u; rfl) | rfl

private theorem toRep_restrictStep_ofRep {n : Nat} (v : Value.F.Rep (Later D) (n + 1)) :
    Value.F.toRep _ (World.restrictStep (Value.F.ofRep (Later D) v)) =
    World.restrictStep v := by
  rcases v with (⟨⟩ | g | ⟨K, ds⟩) <;> rfl

private theorem toRep_restrict_ofRep {n m : Nat}
    (v : Value.F.Rep (Later D) n) (hm : m ≤ n) :
    Value.F.toRep _ (World.restrict (Value.F.ofRep (Later D) v) hm) = World.restrict v hm := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hm; simp [World.restrict.eq_1, Value_F_toRep_ofRep]
  | succ n ih =>
    rw [World.restrict.eq_1]; split
    · next h => subst h; simp [Value_F_toRep_ofRep, World.restrict.eq_1]
    · next h =>
      have h_rs : World.restrictStep (Value.F.ofRep (Later D) v) =
          Value.F.ofRep _ (World.restrictStep v) := by
        rcases v with (⟨⟩ | g | ⟨K, ds⟩) <;> rfl
      show Value.F.toRep _ (World.restrict (World.restrictStep (Value.F.ofRep _ v)) _) = _
      rw [h_rs, ih]
      rw [World.restrict, World.restrict];
      grind +suggestions

/-
Helper: fn condition is preserved under restriction
-/
private theorem fn_cond_restrict {n : Nat}
    (v : Value.F.Rep (Later D) (n + 2))
    (hfn : ∀ (g : World.Function (Later D) (Later D) (n + 2)),
      v = Sum.inr (Sum.inl g) →
      ∀ k' (hk' : k' ≤ n + 2) (dl : Later D k'), GoodLater k' dl → GoodLater k' (g k' hk' dl)) :
    ∀ (g : World.Function (Later D) (Later D) (n + 1)),
      World.restrict v (Nat.le_succ (n + 1)) = Sum.inr (Sum.inl g) →
      ∀ k' (hk' : k' ≤ n) (dl : Later D (k' + 1)),
        GoodLater (k' + 1) dl → GoodLater (k' + 1) (g (k' + 1) (by omega) dl) := by
  intro g hg
  rcases v with (_ | _ | _ | v) <;> simp +arith +decide [World.restrict] at hg ⊢
  · simp_all +decide [World.restrictStep]; grind
  · cases hg
  · cases hg

/-
Helper: con condition is preserved under restriction
-/
private theorem con_cond_restrict {n : Nat}
    (v : Value.F.Rep (Later D) (n + 2))
    (hcon : ∀ (K : ConTag) (ds : List (Later D (n + 2))),
      v = Sum.inr (Sum.inr (K, ds)) →
      ∀ (dl : Later D (n + 2)), dl ∈ ds → GoodLater (n + 2) dl) :
    ∀ (K : ConTag) (ds : List (Later D (n + 1))),
      World.restrict v (Nat.le_succ (n + 1)) = Sum.inr (Sum.inr (K, ds)) →
      ∀ (dl : Later D (n + 1)), dl ∈ ds → GoodLater (n + 1) dl := by
  intro K ds hds dl hdl
  rcases v with (u | (g | ⟨K', ds'⟩))
  · cases u; simp [World.restrict.eq_1] at hds
  · rw [restrict_fn_rep] at hds; exact absurd hds (by intro h; cases h)
  · rw [restrict_con_rep] at hds
    have ⟨hK, hds_eq⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hds))
    subst hK; subst hds_eq
    have ⟨x, hx_mem, hx_eq⟩ := mem_restrict_list ds' dl _ hdl
    rw [hx_eq]; exact GoodLater_restrict _ (hcon K' ds' rfl x hx_mem) _ _

/-
Helper: D.ret with good value conditions produces StartsVisible and TraceGood
-/
private theorem D_ret_good_at_level {n : Nat}
    (v : Value.F (▹ D) (n + 1))
    (hfn : ∀ (g : World.Function (Later D) (Later D) (n + 1)),
      Value.F.toRep _ v = Sum.inr (Sum.inl g) →
      ∀ k' (hk' : k' ≤ n) (dl : Later D (k' + 1)),
        GoodLater (k' + 1) dl → GoodLater (k' + 1) (g (k' + 1) (by omega) dl))
    (hcon : ∀ (K : ConTag) (ds : List (Later D (n + 1))),
      Value.F.toRep _ v = Sum.inr (Sum.inr (K, ds)) →
      ∀ (dl : Later D (n + 1)), dl ∈ ds → GoodLater (n + 1) dl)
    (k : Nat) (hk : k ≤ n) (μ : Heap (▹ D) k) (hμ : GoodHeap k μ) :
    StartsVisible k ((D.ret v).unfold k (by omega) μ) ∧
    TraceGood 2 k ((D.ret v).unfold k (by omega) μ) := by
  simp only [D_ret_eq]
  cases k with
  | zero => exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  | succ k' =>
    constructor
    · unfold StartsVisible; simp [T.ret, T_uf]
    · unfold TraceGood; simp [T.ret, T_uf]
      refine ⟨?_, ?_, hμ⟩
      · -- fn condition on restricted value
        intro g hg k'' hk'' dl hdl
        have hv := Value.F.toRep _ v
        rcases hv : Value.F.toRep ( Later D ) v with ( _ | _ | _ );
        · simp_all +decide [ Value.F.toRep ];
          exact absurd hg ( by erw [ restrict_inl_unit ] ; simp +decide );
        · rw [ hv ] at hg;
          rw [ restrict_fn_rep ] at hg;
          cases hg;
          rw [restrict_Function_apply];
          exact hfn _ hv _ ( by omega ) _ hdl;
        · rw [ hv ] at hg; simp_all +decide;
          exact absurd hg ( by erw [ restrict_con_rep ] ; exact by rintro ⟨ ⟩ )
      · -- con condition on restricted value
        intro K' ds' hds dl hdl
        rcases v with (⟨⟩ | ⟨g⟩ | ⟨K, ds⟩)
        · simp [Value.F.toRep] at hds; rw [restrict_inl_unit] at hds; cases hds
        · simp [Value.F.toRep] at hds; rw [restrict_fn_rep] at hds; cases hds
        · simp [Value.F.toRep] at hds ⊢
          rw [restrict_con_rep] at hds
          have ⟨hK, hds_eq⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hds))
          subst hK; subst hds_eq
          have ⟨x, hx_mem, hx_eq⟩ := mem_restrict_list ds dl _ hdl
          rw [hx_eq]
          exact GoodLater_restrict _ (hcon K ds rfl x hx_mem) _ _

/-
T.ret with a double-restricted value satisfies StartsVisible ∧ TraceGood 2.
-/
private theorem ret_restrict_good {n : Nat}
    (v : Value.F.Rep (Later D) (n + 2))
    (hfn : ∀ (g : World.Function (Later D) (Later D) (n + 2)),
      v = Sum.inr (Sum.inl g) →
      ∀ (k' : Nat) (hk' : k' ≤ n + 2) (dl : Later D k'), GoodLater k' dl → GoodLater k' (g k' hk' dl))
    (hcon : ∀ (K : ConTag) (ds : List (Later D (n + 2))),
      v = Sum.inr (Sum.inr (K, ds)) → ∀ (dl : Later D (n + 2)), dl ∈ ds → GoodLater (n + 2) dl)
    (k₀ : Nat) (hk₀ : k₀ ≤ n + 1) (μ₀ : Heap (Later D) k₀) (hμ₀ : GoodHeap k₀ μ₀) :
    StartsVisible k₀ (T.ret (World.restrict (World.restrict v (Nat.le_refl (n + 2))) (by omega), μ₀)) ∧
    TraceGood 2 k₀ (T.ret (World.restrict (World.restrict v (Nat.le_refl (n + 2))) (by omega), μ₀)) := by
  have hrestr : World.restrict v (Nat.le_refl (n + 2)) = v := by
    rw [World.restrict.eq_1]; simp
  rw [hrestr]
  cases k₀ with
  | zero => exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
  | succ k₀' =>
    constructor
    · unfold StartsVisible; simp [T.ret, T_uf]
    · unfold TraceGood; simp only [T.ret, T_uf]
      refine ⟨?_, ?_, hμ₀⟩
      · -- fn condition: case split on v
        intro g hg k' hk' dl hdl
        rcases v with (u | gv | ⟨K, ds⟩)
        · cases u; rw [restrict_inl_unit] at hg; nomatch hg
        · rw [restrict_fn_rep] at hg; cases hg
          rw [restrict_Function_apply]
          exact hfn gv rfl _ (by omega) _ hdl
        · rw [restrict_con_rep] at hg; nomatch hg
      · -- con condition: case split on v
        intro K ds hds dl hdl
        rcases v with (u | gv | ⟨K', ds'⟩)
        · cases u; rw [restrict_inl_unit] at hds; nomatch hds
        · rw [restrict_fn_rep] at hds; nomatch hds
        · rw [restrict_con_rep] at hds
          have ⟨hK, hds_eq⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hds))
          subst hK; subst hds_eq
          have ⟨x, hx_mem, hx_eq⟩ := mem_restrict_list ds' dl _ hdl
          rw [hx_eq]; exact GoodLater_restrict _ (hcon K' ds' rfl x hx_mem) _ _

theorem GoodLater_memo : ∀ (a : Addr) {m : Nat} (d : ▹ D (m + 1)),
    (∀ k (hk : k ≤ m) μ, GoodHeap k μ →
      StartsVisible k (unfoldLater d k hk μ) ∧ TraceGood 2 k (unfoldLater d k hk μ)) →
    GoodLater (m + 1) (D.memo a d) := by
  intro a m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro d hd
  unfold GoodLater
  intro k hk μ hμ
  -- Unfold D.memo using equation lemma
  show StartsWithStep k (unfoldLater (D.memo a d) k hk μ) ∧
       TraceGood 2 k (unfoldLater (D.memo a d) k hk μ)
  simp only [unfoldLater]
  rw [D.memo.eq_1 a d]
  simp only [Later.hmap, D_bind_eq, Value_F_toRep_ofRep]
  have hd_vis := (hd k hk μ hμ).1
  have hd_tg := (hd k hk μ hμ).2
  constructor
  · -- StartsWithStep of T.bind
    apply StartsWithStep_bind_of_visible
    · exact hd_vis
    · intro j hj vh
      obtain ⟨v, μ'⟩ := vh
      cases j <;> simp [StartsWithStep, D_step_eq, T_uf, T.step]
  · -- TraceGood 2 of T.bind
    apply T_bind_TraceGood 2 (Nat.le_refl 2) _ _ hd_tg
    · intro h; omega
    · -- hkont: TraceGood 2 at good values
      intro j hj vh hfn hcon hheap
      obtain ⟨v, μ'⟩ := vh
      dsimp only [] at hfn hcon hheap ⊢
      cases j with
      | zero => exact TraceGood_zero _ _
      | succ j =>
        simp only [D_step_eq, T.step]
        unfold TraceGood; simp only [T_uf]
        rw [restrict_later_next]
        show TraceGood 2 j ((World.restrict (D.fold _) _).unfold j (Nat.le_refl j) (World.restrict μ' _))
        rw [D_unfold_restrict]
        simp only [D_fold_unfold]
        cases j with
        | zero => exact TraceGood_zero 2 _
        | succ j' =>
          unfold TraceGood; simp only [T.ret, T_uf]
          refine ⟨?_, ?_, ?_⟩
          ·
            exact fun g a k hk dl a_1 => fn_cond_restrict v hfn g a k hk dl a_1
          · exact con_cond_restrict v hcon
          · -- heap condition: insert (restrict μ') a (restrict memo)
            intro a' dl' h_get
            rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
            split at h_get
            · -- a' = a: dl' = restrict memo
              cases h_get
              apply GoodLater_restrict
              -- GoodLater (j'+1+1) (D.memo a (Later.next (D.ret ...)))
              -- Apply IH at j' < m
              apply ih (j' + 1) (by omega)
              intro k₀ hk₀ μ₀ hμ₀
              simp only [unfoldLater, Later.next]
              rw [D_unfold_restrictStep]
              simp only [D_ret_eq, toRep_restrict_ofRep]
              -- Now: T.ret (World.restrict (World.restrict v _) _, μ₀)
              exact ret_restrict_good v hfn hcon k₀ hk₀ μ₀ hμ₀
            · -- a' ≠ a: dl' from restrict μ'
              have h_get' : Std.HashMap.get? (World.restrict μ' (by omega)) a' = some dl' := by
                rwa [Std.HashMap.get?_eq_getElem?]
              exact GoodHeap_restrict μ' hheap (by omega) a' dl' h_get'
    · -- hkont_stuck: at stuck values
      intro j hj vh hvh hheap
      obtain ⟨v, μ'⟩ := vh
      dsimp only [] at hvh hheap ⊢
      subst hvh
      cases j with
      | zero => exact ⟨Or.inl trivial, fun k' => TraceGood_zero k' _⟩
      | succ j =>
        simp only [D_step_eq, T.step]
        constructor
        · left; unfold NotRet; simp [T_uf]
        · intro k'
          -- T.step .update (...) at level j+1
          -- TraceGood k' (j+1) of step = TraceGood 2 j of inner
          unfold TraceGood; simp only [T_uf]
          rw [restrict_later_next]
          show TraceGood 2 j ((World.restrict (D.fold _) _).unfold j (Nat.le_refl j) (World.restrict μ' _))
          rw [D_unfold_restrict]
          simp only [D_fold_unfold]
          cases j with
          | zero => exact TraceGood_zero 2 _
          | succ j' =>
            unfold TraceGood; simp only [T.ret, T_uf]
            refine ⟨?_, ?_, ?_⟩
            · -- fn condition: vacuous for stuck
              intro g hg; rw [restrict_inl_unit] at hg; cases hg
            · -- con condition: vacuous for stuck
              intro K ds hds; rw [restrict_inl_unit] at hds; cases hds
            · -- heap condition
              intro a' dl' h_get
              rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
              split at h_get
              · cases h_get; apply GoodLater_restrict
                apply ih (j' + 1) (by omega)
                intro k₀ hk₀ μ₀ hμ₀
                simp only [unfoldLater, Later.next]
                rw [D_unfold_restrictStep]
                simp only [D_ret_eq, toRep_restrict_ofRep]
                cases k₀ with
                | zero => exact ⟨StartsVisible_zero _, TraceGood_zero _ _⟩
                | succ k₀' =>
                  constructor
                  · unfold StartsVisible; simp [T.ret, T_uf]
                  · unfold TraceGood; simp only [T.ret, T_uf]
                    refine ⟨fun g hg => ?_, fun K ds hds => ?_, hμ₀⟩
                    · rw [restrict_inl_unit, restrict_inl_unit] at hg; nomatch hg
                    · rw [restrict_inl_unit, restrict_inl_unit] at hds; nomatch hds
              · have h_get' : Std.HashMap.get? (World.restrict μ' (by omega)) a' = some dl' := by
                  rwa [Std.HashMap.get?_eq_getElem?]
                exact GoodHeap_restrict μ' hheap (by omega) a' dl' h_get'

-- stuck_memo_TraceGood

/-- Fundamental lemma for .let' -/
theorem fundamental_let (x : Var) (e₁ e₂ : Exp) {n : Nat}
    (ρ : Env (D n)) (hρ : GoodEnv ρ)
    (ih_e₁ : ∀ {m : Nat} (ρ' : Env (D m)), GoodEnv ρ' →
      GoodD m (eval (D := D) e₁ m (Nat.le_refl m) ρ'))
    (ih_e₂ : ∀ {m : Nat} (ρ' : Env (D m)), GoodEnv ρ' →
      GoodD m (eval (D := D) e₂ m (Nat.le_refl m) ρ')) :
    GoodD n (eval (D := D) (.let' x e₁ e₂) n (Nat.le_refl n) ρ) := by
  simp only [eval.eq_6]
  intro m hm μ hμ
  simp only [Domain.bind', Domain.bind, D_fold_unfold]
  -- The goal is StartsVisible ∧ TraceGood of body.unfold at the extended heap
  -- Let ext_env := the extended env, a := μ.nextFree
  -- The env: (World.restrict ρ _).bind x (Domain.step' (.look x) (D.invis (fetch a)))
  -- The heap: Heap.set μ a (D.memo a (Later.next (eval e₁ m _ ext_env)))
  -- 1. GoodEnv of extended env
  have h_env_base := GoodEnv_world_restrict ρ hρ hm
  have h_env := GoodEnv_bind _ h_env_base x _ (fetch_entry_good x μ.nextFree)
  -- 2. GoodD of rhs: eval e₁ in the extended GoodEnv
  have h_rhs := ih_e₁ _ h_env
  -- The body: D.step .let1 (Later.next (eval e₂ m _ (Env.bind (World.restrict ρ hm) x (D.step ...))))
  -- The heap: Heap.set μ a (D.memo a (Later.next (eval e₁ m _ ext_env)))
  -- 3. GoodLater of memo thunk
  have h_memo : GoodLater m (D.memo μ.nextFree
      (Later.next (eval (D := D) e₁ m (Nat.le_refl m)
        (Env.bind (World.restrict (F := Heap D) ρ hm) x
          (D.step (.look x) (Later.next (D.invis (fetch μ.nextFree)))))))) := by
    cases m with
    | zero => exact GoodLater_zero _
    | succ k' =>
      apply GoodLater_memo
      intro k hk μ' hμ'
      simp only [unfoldLater, Later.next]
      rw [D_unfold_restrictStep]
      exact h_rhs k (by omega) μ' hμ'
  -- 4. GoodHeap of extended heap
  have h_heap := GoodHeap_set μ hμ μ.nextFree _ h_memo
  -- 5. GoodD of body
  have h_body := GoodD_step_of_TraceGood .let1
    (eval (D := D) e₂ m (Nat.le_refl m)
      (Env.bind (World.restrict (F := Heap D) ρ hm) x
        (D.step (.look x) (Later.next (D.invis (fetch μ.nextFree))))))
    (fun m' hm' μ'' hμ'' => (ih_e₂ _ h_env m' hm' μ'' hμ'').2)
  -- 6. Apply at extended heap
  exact h_body m (Nat.le_refl m) _ h_heap

/-- **Fundamental Lemma**: if the environment is good, then `eval e` produces a good `D`.
    By structural induction on `e` (mutual with `Alt`), using the closure properties. -/
theorem fundamental_lemma (e : Exp) {n : Nat} (ρ : Env (D n)) (hρ : GoodEnv ρ) :
    GoodD n (eval (D := D) e n (Nat.le_refl n) ρ) := by
  match e with
  | .ref x => exact fundamental_ref x ρ hρ
  | .conapp K xs => exact fundamental_conapp K xs ρ hρ
  | .lam x body =>
    simp only [eval.eq_2, Domain.fn', Domain.step']
    apply GoodD_fn
    intro m hm dl hdl
    cases m with
    | zero => exact GoodLater_zero _
    | succ k =>
      simp only [Later.hmap]
      apply GoodLater_of_step
      apply fundamental_lemma body
      apply GoodEnv_bind _ (GoodEnv_world_restrict ρ hρ _) x dl
      exact GoodLater_to_GoodEnv_cond dl hdl
  | .app e₁ x =>
    exact fundamental_app e₁ x ρ hρ (fun ρ' hρ' => fundamental_lemma e₁ ρ' hρ')
  | .case' eₛ alts =>
    exact fundamental_case eₛ alts ρ hρ
      (fun ρ' hρ' => fundamental_lemma eₛ ρ' hρ')
      (fun alt _halt {_m} ρ' hρ' => fundamental_lemma alt.rhs ρ' hρ')
  | .let' x e₁ e₂ =>
    exact fundamental_let x e₁ e₂ ρ hρ
      (fun ρ' hρ' => fundamental_lemma e₁ ρ' hρ')
      (fun ρ' hρ' => fundamental_lemma e₂ ρ' hρ')
termination_by sizeOf e
decreasing_by
  all_goals simp_wf; first | omega | skip
  · have := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have : sizeOf alt.rhs < sizeOf alt := by cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega

/-! ## Main theorems -/

private theorem emptyHeap_good (n : Nat) : GoodHeap n (∅ : Heap (▹ D) n) :=
  fun _ _ h => absurd h (by rw [HashMap_get?_empty]; simp)

private theorem emptyEnv_good (n : Nat) : GoodEnv (Env.empty : Env (D n)) := by
  intro x d h; rw [show Env.find? Env.empty x = none from HashMap_get?_empty x] at h; cases h

/-- **Main Theorem**: every trace produced by `evalByNeed` has at most 2 consecutive
    invisible steps (no triple `T.invis`). -/
theorem evalByNeed_noTripleInvis (n : Nat) (e : Exp) :
    NoTripleInvis n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) :=
  TraceGood_implies_NCI 2 n _
    (fundamental_lemma e Env.empty (emptyEnv_good n) n (Nat.le_refl n) ∅ (emptyHeap_good n)).2

/-- The trace of `evalByNeed n e` starts visibly. -/
theorem evalByNeed_startsVisible (n : Nat) (e : Exp) :
    StartsVisible n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) :=
  (fundamental_lemma e Env.empty (emptyEnv_good n) n (Nat.le_refl n) ∅ (emptyHeap_good n)).1

end ByNeed
