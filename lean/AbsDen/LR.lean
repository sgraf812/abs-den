import AbsDen.Semantics

/-!
# Logical relations on semantic domains

A `LR D` packages two step-indexed sub-presheaves on a semantic domain `D`:

- `Comp : World.Pred D` — the *computation* side. Holds for `D`-values whose
  unfoldings are well-behaved.
- `Thunk : World.Pred (Later D)` — the *thunk* side. Holds for `Later D`-values
  that represent heap-allocated thunks: their first unfolding step is visible
  and forces to a `Comp`.

Coherences `Thunk_to_Comp` and `step_to_Thunk` mediate between the two. The
fundamental lemma `LR.fundamental` is a structural induction over `Exp` using
only these fields.
-/

/-- A unary logical relation on the semantic domain `D`. -/
structure LR (D : Nat → Type) [Domain D] where
  /-- Computation-side sub-presheaf of `D`. -/
  Comp : World.Pred D
  /-- Thunk-side sub-presheaf of `Later D`. -/
  Thunk : World.Pred (Later D)

  /-- Forcing a `Thunk` produces a `Comp`. -/
  Thunk_to_Comp : ∀ {n : Nat} (d : D n),
    Thunk.holds (n := n+1) d → Comp.holds d
  /-- Step-wrapping a `Comp`-value yields a `Thunk`. -/
  step_to_Thunk : ∀ {n : Nat} (ev : Event) (d : D n),
    Comp.holds d → Thunk.holds (n := n+1) (Domain.step' ev d : D n)

  /-- `Domain.stuck` is a `Comp`. -/
  stuck : ∀ {n : Nat}, Comp.holds (Domain.stuck (D := D) (n := n))

  /-- Closure of `Comp` under `Domain.step'`. -/
  step : ∀ {n : Nat} (ev : Event) (d : D n),
    Comp.holds d → Comp.holds (Domain.step' ev d)

  /-- `Domain.fn'` closure: the function maps `Thunk`s to `Thunk`s. -/
  fn : ∀ {n : Nat} (f : world(D → D) n),
    (∀ (m : Nat) (hm : m ≤ n) (dl : Later D m),
      Thunk.holds dl →
      Thunk.holds (Later.hmap m (fun k _hk => f k (by omega)) dl)) →
    Comp.holds (Domain.fn' f)

  /-- `Domain.con'` closure: each field is a `Thunk`. -/
  con : ∀ {n : Nat} (K : ConTag) (ds : List (D n)),
    (∀ d, d ∈ ds → Thunk.holds (n := n+1) d) →
    Comp.holds (Domain.con' K ds)

  /-- Closure for the `.app1`-wrapped application produced by `eval (.app …)`. -/
  app_closed : ∀ {n : Nat} (dv da : D n),
    Comp.holds dv → Thunk.holds (n := n+1) da →
    Comp.holds (Domain.step' .app1 (Domain.apply' dv da))

  /-- Closure for the `.case1`-wrapped case discrimination produced by
      `eval (.case' …)`. -/
  case_closed : ∀ {n : Nat} (dv : D n)
      (alts : List (ConTag × world(List D → D) n)),
    Comp.holds dv →
    (∀ (K : ConTag) (f : world(List D → D) n), (K, f) ∈ alts →
      ∀ (m : Nat) (hm : m ≤ n) (ds : List (D m)),
        (∀ d, d ∈ ds → Thunk.holds (n := m+1) d) →
        Thunk.holds (n := m+1) (f m hm ds : D m)) →
    Comp.holds (Domain.step' .case1 (Domain.select' dv alts))

  /-- `Domain.bind'` closure, parameterized by the wrapping event. -/
  bind_closed : ∀ {n : Nat} (ev : Event) (rhs body : World.Function D D n),
    (∀ (m : Nat) (hm : m ≤ n) (dx : D m),
      Thunk.holds (n := m+1) (Domain.step' ev dx : D m) →
      Comp.holds (rhs m hm dx)) →
    (∀ (m : Nat) (hm : m ≤ n) (dx : D m),
      Thunk.holds (n := m+1) (Domain.step' ev dx : D m) →
      Comp.holds (body m hm dx)) →
    Comp.holds (Domain.bind' rhs body)

namespace LR

variable {D : Nat → Type} [Domain D]

/-! ## HashMap-level helpers (private)

    Used to lift `Functor.map`-style restriction on `Env D` to a get?-level
    equation. -/

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

private theorem env_find?_map {V W : Type} (f : V → W) (ρ : Env V) (x : Var) :
    Env.find? (Functor.map f ρ : Env W) x = Option.map f (Env.find? ρ x) := by
  simp only [Env.find?, Std.HashMap.get?_eq_getElem?]
  show (Std.HashMap.fold (fun (acc : Std.HashMap Nat W) k v => acc.insert k (f v)) ∅ ρ)[x]? = _
  rw [Std.HashMap.fold_eq_foldl_toList, foldl_insert_map_getElem?]
  · congr 1; exact HashMap_rebuild_getElem? ρ x
  · intro b; simp

/-! ## Env-level closure -/

/-- An environment is *good* when every entry, viewed at one index up,
    satisfies `lr.Thunk`. -/
def env (lr : LR D) {n : Nat} (ρ : Env (D n)) : Prop :=
  ∀ x d, ρ.find? x = some d → lr.Thunk.holds (n := n+1) d

/-- The empty env is good. -/
theorem env_empty (lr : LR D) {n : Nat} :
    lr.env (Env.empty : Env (D n)) := by
  intro x d h
  have hnone : (∅ : Std.HashMap Var (D n)).get? x = none := by
    simp [Std.HashMap.get?_eq_getElem?]
  rw [show Env.empty.find? x = (∅ : Std.HashMap Var (D n)).get? x from rfl, hnone] at h
  cases h

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
    exact lr.Thunk.closed d' (hρ x d' hget)

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

/-- Binding a `Thunk`-value extends a good env. -/
theorem env_bind (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (x : Var) (d : D n) (hd : lr.Thunk.holds (n := n+1) d) :
    lr.env (ρ.bind x d) := by
  intro y d' hfind
  simp only [Env.bind, Env.find?, Std.HashMap.get?_eq_getElem?] at hfind
  rw [Std.HashMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind; exact hd
  · exact hρ y d' (by rwa [Env.find?, Std.HashMap.get?_eq_getElem?])

/-- Binding many `Thunk`-values extends a good env. -/
theorem env_bindMany (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (xs : List Var) (ds : List (D n)) (hds : ∀ d, d ∈ ds → lr.Thunk.holds (n := n+1) d) :
    lr.env (ρ.bindMany xs ds) := by
  unfold Env.bindMany
  induction xs generalizing ρ ds with
  | nil => simp [List.zip]; exact hρ
  | cons x xs ih => cases ds with
    | nil => simp [List.zip]; exact hρ
    | cons d ds =>
      simp [List.zip]
      apply ih (Std.HashMap.insert ρ x d)
      · exact env_bind lr ρ hρ x d (hds d (.head _))
      · intro d' hd'; exact hds d' (.tail _ hd')

/-- `pmapList` results from a good env are pointwise `Thunk`. -/
theorem pmapList_good (lr : LR D) {n : Nat} (ρ : Env (D n)) (hρ : lr.env ρ)
    (xs : List Var) (ds : List (D n)) (hds : ρ.pmapList xs = some ds) :
    ∀ d, d ∈ ds → lr.Thunk.holds (n := n+1) d := by
  have h_exists_x : ∀ d ∈ ds, ∃ x ∈ xs, ρ.find? x = some d := by
    induction xs generalizing ds <;> simp_all +decide [Env.pmapList]
    cases h : ρ.find? ‹_› <;> simp_all +decide [Option.bind_eq_some_iff]; grind
  exact fun d hd => hρ _ _ (h_exists_x d hd |> Classical.choose_spec |> And.right)

/-! ## Fundamental lemma -/

/-- **Fundamental Lemma.** If `ρ` is good, then `eval e ρ` satisfies `lr.Comp`.
    Structural induction on `e` using only the closure laws and coherences
    packaged in `lr`. -/
theorem fundamental (lr : LR D) :
    ∀ (e : Exp) {n : Nat} (ρ : Env (D n)), lr.env ρ →
      lr.Comp.holds (eval (D := D) e n (Nat.le_refl n) ρ)
  | .ref x, n, ρ, hρ => by
    simp only [eval]
    cases h : ρ.find? x with
    | none => exact lr.stuck
    | some d => exact lr.Thunk_to_Comp d (hρ x d h)
  | .conapp K xs, n, ρ, hρ => by
    simp only [eval]
    cases h : ρ.pmapList xs with
    | none => exact lr.stuck
    | some ds => exact lr.con K ds (pmapList_good lr ρ hρ xs ds h)
  | .lam x body, n, ρ, hρ => by
    simp only [eval]
    apply lr.fn
    intro m hm dl hThunk
    match m, dl, hThunk with
    | 0, _, hThunk => exact hThunk
    | k+1, dl, hThunk =>
      simp only [Later.hmap]
      apply lr.step_to_Thunk
      apply fundamental lr body
      apply env_bind lr _ _ x dl hThunk
      exact env_world_restrict lr ρ hρ (by omega)
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
      apply lr.step_to_Thunk
      apply fundamental lr alt.rhs
      apply env_bindMany lr _ _ alt.vars ds hds
      exact env_world_restrict lr ρ hρ hm
  | .let' x e₁ e₂, n, ρ, hρ => by
    simp only [eval]
    apply lr.bind_closed (.look x)
    · intro m hm dx hThunk
      apply fundamental lr e₁
      apply env_bind lr _ _ x _ hThunk
      exact env_world_restrict lr ρ hρ hm
    · intro m hm dx hThunk
      apply lr.step
      apply fundamental lr e₂
      apply env_bind lr _ _ x _ hThunk
      exact env_world_restrict lr ρ hρ hm
termination_by e _ _ _ => sizeOf e
decreasing_by
  all_goals simp_wf; first | omega | skip
  · have := List.sizeOf_lt_of_mem ‹alt ∈ alts›
    have : sizeOf alt.rhs < sizeOf alt := by cases alt; simp [Alt.mk.sizeOf_spec]; omega
    omega

/-! ## Smart constructors -/

/-- The trivial logical relation: both predicates always true. -/
def trivial : LR D where
  Comp := World.Pred.ofClosed (fun _ => True) (fun _ _ => True.intro)
  Thunk := World.Pred.ofClosed (fun _ => True) (fun _ _ => True.intro)
  Thunk_to_Comp := fun _ _ => by simp
  step_to_Thunk := fun _ _ _ => by simp
  stuck := by simp
  step := fun _ _ _ => by simp
  fn := fun _ _ => by simp
  con := fun _ _ _ => by simp
  app_closed := fun _ _ _ _ => by simp
  case_closed := fun _ _ _ _ => by simp
  bind_closed := fun _ _ _ _ _ => by simp

end LR
