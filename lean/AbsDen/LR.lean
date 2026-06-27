import AbsDen.Semantics
import AbsDen.Trace

/-! ## `IsLookShape` — the look-step value shape -/

/-- The look-step value shape as a `Pred D` at any level: holds iff
    `d = Domain.step' (.look x) d'` for some `x : Var` and witness `d'`. -/
noncomputable def IsLookShape {D : Nat → Type} [Domain D] {n : Nat} :
    World.Pred D n :=
  World.Pred.ofClosed
    (holds := fun {m} d => ∃ (x : Var) (d' : D _), d = Domain.step' (.look x) d')
    (closed := fun {m} d ⟨x, d', hd⟩ =>
      ⟨x, World.restrictStep d', by rw [hd]; exact (Domain.natural_step (.look x) d').symm⟩)

@[simp] theorem IsLookShape_holds {D : Nat → Type} [Domain D] {n : Nat} (d : D n) :
    (IsLookShape (D := D) (n := n)).holds d ↔
    ∃ (x : Var) (d' : D n), d = Domain.step' (.look x) d' := Iff.rfl

/-! ## `IsLookup` — `P` plus look-step shape -/

/-- The "look-step-wrapped P-value" sub-presheaf on `D`: pointwise conjunction
    of `P` and `IsLookShape`. -/
noncomputable def IsLookup {D : Nat → Type} [Domain D] {n : Nat} (P : World.Pred D n) :
    World.Pred D n := World.Pred.And P IsLookShape

@[simp] theorem IsLookup_holds {D : Nat → Type} [Domain D] {n : Nat}
    (P : World.Pred D n) (d : D n) :
    (IsLookup P).holds d ↔
    P.holds d ∧ ∃ (x : Var) (d' : D n), d = Domain.step' (.look x) d' := by
  show (P.And IsLookShape).holds d ↔ _
  rw [World.Pred.And_holds, IsLookShape_holds]

/-! ## `Parametric`: per-case closure conditions on `Value.F` -/

namespace Parametric

/-- A function `f : D → D` is `Parametric P`-good iff it maps `IsLookup P`
    inputs to `P` outputs, at every sub-level. -/
def Fn {D : Nat → Type} [Domain D] (P : ∀ {n}, World.Pred D n) {n : Nat}
    (f : world(D → D) n) : Prop :=
  ∀ (m : Nat) (hm : m ≤ n) (d : D m),
    (IsLookup P).holds d → P.holds (f m hm d)

/-- A list of fields `ds : List (D n)` is `Parametric P`-good iff every entry
    is `IsLookup P`. -/
def Con {D : Nat → Type} [Domain D] (P : ∀ {n}, World.Pred D n) {n : Nat}
    (ds : List (D n)) : Prop :=
  ∀ d, d ∈ ds → (IsLookup P).holds d

end Parametric

/-!
# Logical relations on semantic domains

A `LR D` packages two level-indexed sub-presheaves on a semantic domain `D`:

- `P : ∀ {n}, World.Pred D n` — the *defining* predicate. Holds for
  `D`-values whose unfoldings are well-behaved.
- `IsThunk : ∀ {n}, World.Pred D n` — heap-stored thunks; the predicate that
  `bind_closed`'s `rhs`/`body` receive on their input.
-/

/-- A unary logical relation on the semantic domain `D`. -/
structure LR (D : Nat → Type) [Domain D] where
  /-- Computation-side sub-presheaf of `D`. -/
  P : ∀ {n : Nat}, World.Pred D n

  /-- Naturality of the `P` family: the level-`n+1` view's underlying truth
      values at level `m ≤ n+1` agree with the level-`n` view's underlying
      truth values at level `m ≤ n`. -/
  P_natural : ∀ {n m : Nat} (hm : m ≤ n) (x : D m),
    (P (n := n+1)).val m (Nat.le_succ_of_le hm) x = (P (n := n)).val m hm x

  /-- Thunk-shape predicate: values that body/rhs in `bind_closed` receive as
      input. For ByName this is just `IsLookup`-shape; for ByNeed it captures
      heap-fetched thunks (`D.invis (fetch a)`-style). -/
  IsThunk : ∀ {n : Nat}, World.Pred D n

  /-- Naturality of the `IsThunk` family. -/
  IsThunk_natural : ∀ {n m : Nat} (hm : m ≤ n) (x : D m),
    (IsThunk (n := n+1)).val m (Nat.le_succ_of_le hm) x
      = (IsThunk (n := n)).val m hm x

  /-- Coherence: wrapping a thunk with `step' (.look x)` yields a `P`-good
      value. -/
  IsThunk_to_P : ∀ {n : Nat} (x : Var) (d : D n),
    IsThunk.holds d → P.holds (Domain.step' (.look x) d)

  /-- `Domain.stuck` is a `P`. -/
  stuck : ∀ {n : Nat}, P.holds (Domain.stuck (D := D) (n := n))

  /-- Closure of `P` under `Domain.step'`. -/
  step : ∀ {n : Nat} (ev : Event) (d : D n),
    P.holds d → P.holds (Domain.step' ev d)

  /-- `Domain.fn'` closure: `f` is `Parametric.Fn P`-good. -/
  fn : ∀ {n : Nat} (f : world(D → D) n),
    Parametric.Fn (@P) f → P.holds (Domain.fn' f)

  /-- `Domain.con'` closure: the fields list is `Parametric.Con P`-good. -/
  con : ∀ {n : Nat} (K : ConTag) (ds : List (D n)),
    Parametric.Con (@P) ds → P.holds (Domain.con' K ds)

  /-- Closure for the `.app1`-wrapped application produced by `eval (.app …)`. -/
  app_closed : ∀ {n : Nat} (dv da : D n),
    P.holds dv → (IsLookup P).holds da →
    P.holds (Domain.step' .app1 (Domain.apply' dv da))

  /-- Closure for the `.case1`-wrapped case discrimination produced by
      `eval (.case' …)`. Each alt branch maps a `Parametric.Con P`-good list
      to a `P`-good result. -/
  case_closed : ∀ {n : Nat} (dv : D n)
      (alts : List (ConTag × world(List D → D) n)),
    P.holds dv →
    (∀ (K : ConTag) (f : world(List D → D) n), (K, f) ∈ alts →
      ∀ (m : Nat) (hm : m ≤ n) (ds : List (D m)),
        Parametric.Con (@P) ds → P.holds (f m hm ds)) →
    P.holds (Domain.step' .case1 (Domain.select' dv alts))

  /-- `Domain.bind'` closure: both `rhs` and `body` produce `P`-good output
      given `IsThunk`-good input. -/
  bind_closed : ∀ {n : Nat} (rhs body : World.Function D D n),
    (∀ (m : Nat) (hm : m ≤ n) (d : D m),
      IsThunk.holds d → P.holds (rhs m hm d)) →
    (∀ (m : Nat) (hm : m ≤ n) (d : D m),
      IsThunk.holds d → P.holds (body m hm d)) →
    P.holds (Domain.step' .let1 (Domain.bind' rhs body))

namespace LR

variable {D : Nat → Type} [Domain D]

/-! ## Derived coherences -/

/-- Forcing a `IsLookup` produces a `P`: with `Pred.And`, `P d` is already
    the left conjunct of `(IsLookup P).holds d`, so this is just projection. -/
theorem IsLookup_to_P {n : Nat} {P : World.Pred D n}
    (d : D n) (h : (IsLookup P).holds d) : P.holds d := by
  rw [IsLookup_holds] at h; exact h.1

/-- `step' (.look v)`-wrapping a `P`-value yields a `IsLookup`. -/
theorem look_to_Lookup (lr : LR D) {n : Nat} (v : Var) (d : D n)
    (h : lr.P.holds d) : (IsLookup lr.P).holds (Domain.step' (.look v) d) := by
  rw [IsLookup_holds]
  exact ⟨lr.step (.look v) d h, v, d, rfl⟩

/-! ## HashMap-level helpers (private)

    Used to lift `Functor.map`-style restriction on `Env D` to a get?-level
    equation. -/

theorem foldl_insert_map_getElem? {V W : Type} (f : V → W)
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

theorem HashMap_rebuild_getElem? {V : Type} (m : Std.HashMap Nat V) (a : Nat) :
    (m.toList.foldl (fun (acc : Std.HashMap Nat V) (p : Nat × V) => acc.insert p.1 p.2) ∅)[a]? =
    m[a]? := by
  rw [foldl_insert_eq_insertMany, Std.HashMap.getElem?_insertMany_list,
      Std.HashMap.getElem?_empty, Option.or_none, findSomeRev?_toList_eq_getElem?]

private theorem env_find?_map {V W : Type} (f : V → W) (ρ : Env V) (x : Var) :
    Env.find? (Functor.map f ρ : Env W) x = Option.map f (Env.find? ρ x) := by
  simp only [Env.find?, Std.HashMap.get?_eq_getElem?]
  show (Std.HashMap.fold (fun (acc : Std.HashMap Nat W) k v => acc.insert k (f v)) ∅ ρ)[x]? = _
  rw [Std.HashMap.fold_eq_foldl_toList, foldl_insert_map_getElem?]
  · congr 1; exact HashMap_rebuild_getElem? ρ x
  · intro b; simp

/-! ## Env-level closure -/

/-- An environment is *good* when every entry is `IsLookup` at the env's level. -/
def env (lr : LR D) {n : Nat} (ρ : Env (D n)) : Prop :=
  ∀ x d, ρ.find? x = some d → (IsLookup lr.P).holds d

/-- The empty env is good. -/
theorem env_empty (lr : LR D) {n : Nat} :
    lr.env (Env.empty : Env (D n)) := by
  intro x d h
  have hnone : (∅ : Std.HashMap Var (D n)).get? x = none := by
    simp [Std.HashMap.get?_eq_getElem?]
  rw [show Env.empty.find? x = (∅ : Std.HashMap Var (D n)).get? x from rfl, hnone] at h
  cases h

/-- Single-step closure for `IsLookup`. -/
theorem IsLookup_closed (lr : LR D) {n : Nat} (d : D (n+1))
    (hd : (IsLookup lr.P).holds d) :
    (IsLookup lr.P).holds (World.restrictStep (F := D) d) := by
  rw [IsLookup_holds] at hd
  rw [IsLookup_holds]
  obtain ⟨hPx, x, d', hd_eq⟩ := hd
  refine ⟨?_, x, World.restrictStep d', ?_⟩
  · -- lr.P at level n holds at restrictStep d, derived from the level-(n+1) view via
    -- intra-Pred closure plus the family's naturality.
    have h : (lr.P (n := n+1)).val n (Nat.le_succ n) (World.restrictStep d) :=
      (lr.P (n := n+1)).property n (Nat.le_refl _) d hPx
    show (lr.P (n := n)).val n (Nat.le_refl _) (World.restrictStep d)
    rw [← lr.P_natural (Nat.le_refl n) (World.restrictStep d)]
    exact h
  · rw [hd_eq]; exact (Domain.natural_step (.look x) d').symm

/-- Good envs are preserved by single-step restriction. -/
theorem env_restrictStep (lr : LR D) {n : Nat} (ρ : Env (D (n+1)))
    (hρ : lr.env ρ) :
    lr.env (World.restrictStep (F := World.Comp Env D) ρ) := by
  intro x d hd
  have hmap : Env.find? (Functor.map (World.restrictStep (F := D)) ρ) x =
      Option.map World.restrictStep (Env.find? ρ x) :=
    env_find?_map _ ρ x
  rw [show World.restrictStep (F := World.Comp Env D) ρ =
        Functor.map (World.restrictStep (F := D)) ρ from rfl, hmap] at hd
  cases hget : Env.find? ρ x with
  | none => rw [hget] at hd; exact absurd hd (by simp [Option.map])
  | some d' =>
    rw [hget] at hd; simp [Option.map] at hd; subst hd
    exact lr.IsLookup_closed d' (hρ x d' hget)

/-- Good envs are preserved by `World.restrict`. -/
theorem env_world_restrict (lr : LR D) {n m : Nat} (ρ : Env (D n))
    (hρ : lr.env ρ) (hm : m ≤ n) :
    lr.env (World.restrict (F := World.Comp Env D) ρ hm) := by
  rw [World.restrict.eq_1]
  split
  · next heq => subst heq; exact hρ
  · next hne =>
    match n with
    | 0 => exact absurd (Nat.le_zero.mp hm) hne
    | _ + 1 =>
      exact env_world_restrict lr _ (env_restrictStep lr ρ hρ) _
  termination_by n

/-- Binding a `IsLookup`-value extends a good env. -/
theorem env_bind (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (x : Var) (d : D n) (hd : (IsLookup lr.P).holds d) :
    lr.env (ρ.bind x d) := by
  intro y d' hfind
  simp only [Env.bind, Env.find?, Std.HashMap.get?_eq_getElem?] at hfind
  rw [Std.HashMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind; exact hd
  · exact hρ y d' (by rwa [Env.find?, Std.HashMap.get?_eq_getElem?])

/-- Binding many `IsLookup`-values extends a good env. -/
theorem env_bindMany (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (xs : List Var) (ds : List (D n)) (hds : Parametric.Con lr.P ds) :
    lr.env (ρ.bindMany xs ds) := by
  unfold Env.bindMany
  induction xs generalizing ρ ds with
  | nil => simp [List.zip]; exact hρ
  | cons x xs ih => cases ds with
    | nil => simp [List.zip]; exact hρ
    | cons d ds =>
      simp [List.zip]
      apply ih (Std.HashMap.insert ρ x d)
      · have hd : (IsLookup lr.P).holds d := by
          rw [IsLookup_holds]; exact hds d (.head _)
        exact env_bind lr ρ hρ x d hd
      · intro d' hd'; exact hds d' (.tail _ hd')

/-- `pmapList` results from a good env are pointwise `IsLookup`. -/
theorem pmapList_good (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (xs : List Var) (ds : List (D n)) (hds : ρ.pmapList xs = some ds) :
    Parametric.Con lr.P ds := by
  have h_exists_x : ∀ d ∈ ds, ∃ x ∈ xs, ρ.find? x = some d := by
    induction xs generalizing ds <;> simp_all +decide [Env.pmapList]
    cases h : ρ.find? ‹_› <;> simp_all +decide [Option.bind_eq_some_iff]; grind
  intro d hd
  have hLookup := hρ _ _ (h_exists_x d hd |> Classical.choose_spec |> And.right)
  rw [IsLookup_holds] at hLookup
  exact hLookup

/-! ## Fundamental lemma -/

/-- **Fundamental Lemma.** If `ρ` is good, then `eval e ρ` satisfies `lr.P`. -/
theorem fundamental (lr : LR D) :
    ∀ (e : Exp) {n : Nat} (ρ : Env (D n)), lr.env ρ →
      lr.P.holds (eval (D := D) e n (Nat.le_refl n) ρ)
  | .ref x, n, ρ, hρ => by
    simp only [eval]
    cases h : ρ.find? x with
    | none => exact lr.stuck
    | some d => exact IsLookup_to_P d (hρ x d h)
  | .conapp K xs, n, ρ, hρ => by
    simp only [eval]
    cases h : ρ.pmapList xs with
    | none => exact lr.stuck
    | some ds => exact lr.con K ds (pmapList_good lr ρ hρ xs ds h)
  | .lam x body, n, ρ, hρ => by
    simp only [eval]
    apply lr.fn
    intro m hm d hLookup
    apply lr.step
    apply fundamental lr body
    apply env_bind lr _ _ x d hLookup
    exact env_world_restrict lr ρ hρ hm
  | .app e₁ x, n, ρ, hρ => by
    simp only [eval]
    cases h : ρ.find? x with
    | none => exact lr.stuck
    | some entry =>
      apply lr.app_closed
      · exact fundamental lr e₁ ρ hρ
      · exact hρ x entry h
  | .case' eₛ alts, n, ρ, hρ => by
    simp only [eval]
    apply lr.case_closed
    · exact fundamental lr eₛ ρ hρ
    · intro K f hmem m hm ds hds
      obtain ⟨alt, halt_mem, halt_eq⟩ := List.mem_map.mp hmem
      cases halt_eq
      apply lr.step
      apply fundamental lr alt.rhs
      apply env_bindMany lr _ _ alt.vars ds hds
      exact env_world_restrict lr ρ hρ hm
  | .let' x e₁ e₂, n, ρ, hρ => by
    simp only [eval]
    apply lr.bind_closed
    · intro m hm dx hThunk
      apply fundamental lr e₁
      apply env_bind lr _ _ x _
      · rw [IsLookup_holds]
        exact ⟨lr.IsThunk_to_P x dx hThunk, x, dx, rfl⟩
      · exact env_world_restrict lr ρ hρ hm
    · intro m hm dx hThunk
      apply fundamental lr e₂
      apply env_bind lr _ _ x _
      · rw [IsLookup_holds]
        exact ⟨lr.IsThunk_to_P x dx hThunk, x, dx, rfl⟩
      · exact env_world_restrict lr ρ hρ hm
termination_by e _ _ _ => sizeOf e
decreasing_by
  all_goals simp_wf; first | omega | skip
  · have := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have : sizeOf alt.rhs < sizeOf alt := by cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega

/-! ## Smart constructors -/

/-- The trivial logical relation: `P` always true. -/
def trivial : LR D where
  P := World.Pred.ofClosed (fun _ => True) (fun _ _ => True.intro)
  P_natural := fun _ _ => rfl
  IsThunk := World.Pred.ofClosed (fun _ => True) (fun _ _ => True.intro)
  IsThunk_natural := fun _ _ => rfl
  IsThunk_to_P := fun _ _ _ => True.intro
  stuck := True.intro
  step := fun _ _ _ => True.intro
  fn := fun _ _ => True.intro
  con := fun _ _ _ => True.intro
  app_closed := fun _ _ _ _ => True.intro
  case_closed := fun _ _ _ _ => True.intro
  bind_closed := fun _ _ _ _ => True.intro

end LR
