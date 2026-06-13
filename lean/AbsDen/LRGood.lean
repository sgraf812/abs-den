import AbsDen.LR
import AbsDen.NoConsecInvis

/-!
# `LR.good` for the by-need domain

Instantiates `LR D` for `ByNeed.D` with `P := GoodD`, `Lookup := GoodLater`. The
main theorems `evalByNeed_noTripleInvis` and `evalByNeed_startsVisible` are
derived as direct consequences of `LR.fundamental good`.
-/

namespace ByNeed

/-! ## Closure lemmas -/

/-- `GoodD` is preserved by `World.restrictStep`. -/
private theorem GoodD_restrictStep {n : Nat} (d : D (n+1))
    (hd : GoodD (n+1) d) : GoodD n (World.restrictStep d) := by
  intro k hk μ hμ
  rw [D_unfold_restrictStep]
  exact hd k (Nat.le_trans hk (Nat.le_succ _)) μ hμ

/-- `World.restrict ∘ Later.next` collapses to `World.restrict` at one index lower. -/
private theorem restrict_later_next' {n : Nat} (d : D n) (k : Nat) (hk : k + 1 ≤ n) :
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

/-- `D.fold` is a left inverse of `World.Fix.unfold`. -/
private theorem D_fold_unfold_id {n : Nat} (d : D n) :
    D.fold (World.Fix.unfold d) = d := by
  show World.Fix.fold (World.Fix.unfold d) = d
  unfold World.Fix.fold World.Fix.unfold
  simp

/-- Extensionality for `D`: two `D` values that agree at every unfolding are
    equal. -/
private theorem D_ext {n : Nat} (a b : D n)
    (h : ∀ (m : Nat) (hm : m ≤ n) (μ : Heap (▹ D) m), D.unfold a m hm μ = D.unfold b m hm μ) :
    a = b := by
  rw [← D_fold_unfold_id a, ← D_fold_unfold_id b]
  congr 1
  funext m hm μ
  exact h m hm μ

/-- `Domain.step' ev` is a natural transformation: it commutes with
    `restrictStep`. -/
theorem Natural_step_ByNeed (ev : Event) :
    Natural (fun {n : Nat} (d : D n) => Domain.step' ev d) := by
  intro n d
  show D.step ev (Later.next (World.restrictStep d)) =
       World.restrictStep (D.step ev (Later.next d))
  apply D_ext
  intro m hm μ
  rw [D_unfold_restrictStep]
  rw [D_step_eq, D_step_eq]
  congr 2
  cases m with
  | zero => rfl
  | succ k =>
    show @World.restrict (Later D) _ n _ (Later.next (World.restrictStep d)) _ =
         @World.restrict (Later D) _ (n+1) _ (Later.next d) _
    rw [restrict_later_next' (World.restrictStep d) k (by omega),
        restrict_later_next' d k (by omega)]
    exact (World.restrict_succ d (by omega : k ≤ n)).symm

/-- A step-wrapped `D.invis (fetch a)` satisfies the env-entry condition for
    any event. -/
private theorem step_invis_fetch_good (ev : Event) (a : Addr) {n : Nat} :
    ∀ m (hm : m ≤ n) (μ : Heap (▹ D) m), GoodHeap m μ →
      StartsWithStep m ((D.step ev (Later.next (D.invis (fetch a)))).unfold m hm μ) ∧
      TraceGood 2 m ((D.step ev (Later.next (D.invis (fetch a)))).unfold m hm μ) := by
  intro m hm μ hμ
  rcases m with _ | m
  · exact ⟨trivial, TraceGood_zero _ _⟩
  · simp only [D_step_eq]
    constructor
    · unfold StartsWithStep; simp [T.step, T_uf]
    · unfold TraceGood; simp [T.step, T_uf]
      rw [restrict_later_next']
      show TraceGood 2 m ((World.restrict (D.invis (fetch a)) (by omega)).unfold m (Nat.le_refl m) (World.restrict μ (by omega)))
      rw [D_unfold_restrict]
      have hμ' := GoodHeap_restrict μ hμ (m := m) (by omega)
      rcases m with _ | k
      · exact TraceGood_zero _ _
      · simp only [D_invis_eq]
        unfold TraceGood; simp only [T_uf]
        unfold fetch
        rw [restrict_later_next']
        dsimp only [Later.hmap]
        rw [D_unfold_restrict]
        simp only [D_fold_unfold]
        have hμ_k : GoodHeap k (World.restrict (World.restrict μ _) _) :=
          GoodHeap_restrict _ hμ' (m := k) (by omega)
        rcases hget : Std.HashMap.get? (World.restrict (World.restrict μ _) _) a with _ | dl
        · rcases k with _ | j
          · exact ⟨Or.inl trivial, TraceGood_zero 1 _⟩
          · constructor
            · right; unfold IsRetStuck; simp [T.ret, T_uf, Value.F.toRep]
            · unfold TraceGood; simp [T.ret, T_uf]
              exact ⟨fun g hg => absurd hg (by simp [Value.F.toRep]),
                     fun K ds hds => absurd hds (by simp [Value.F.toRep]),
                     fun a' dl' h' => hμ_k a' dl' h'⟩
        · have hdl := hμ_k a dl hget
          rcases k with _ | j
          · exact ⟨Or.inl trivial, TraceGood_zero 1 _⟩
          · constructor
            · left; unfold NotRet; simp [T_uf]
            · unfold TraceGood; simp [T_uf]
              have h_heap_j := GoodHeap_restrict _ hμ_k (m := j) (by omega)
              unfold GoodLater at hdl
              have ⟨h_sws, h_tg2⟩ := hdl j (Nat.le_refl j) _ h_heap_j
              exact ⟨Or.inl (StartsWithStep_imp_NotRet h_sws),
                     TraceGood_0_of_StartsWithStep j _ h_sws h_tg2⟩

/-- Packaged form of `step_invis_fetch_good` as a `GoodLater`. -/
private theorem Thunk_step_invis_fetch (ev : Event) (a : Addr) {n : Nat} :
    GoodLater (n+1) (D.step ev (Later.next (D.invis (fetch (n := n) a))) : D n) := by
  unfold GoodLater
  intro m hm μ hμ
  simp only [unfoldLater]
  exact step_invis_fetch_good ev a m hm μ hμ

/-- `GoodD` is preserved by `Domain.step'`. -/
private theorem GoodD_step (n : Nat) (ev : Event) (d : D n) (hd : GoodD n d) :
    GoodD n (Domain.step' ev d) :=
  GoodD_of_GoodLater _ (GoodLater_of_step ev d hd)

/-- `GoodLater (n+1) entry` implies the env-entry condition after restriction. -/
private theorem GoodLater_restrict_next {n j : Nat} (entry : D n)
    (hgl : GoodLater (n+1) entry) (hj : j ≤ n) :
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
    unfold GoodLater at hgl
    exact hgl m (by omega) μ hμ

/-- `GoodLater (n+1) d` implies `GoodLater n (Later.next d)`. -/
private theorem GoodLater_next_of_GoodLater_succ {n : Nat} (d : D n)
    (hd : GoodLater (n+1) d) : GoodLater n (Later.next d) := by
  cases n with
  | zero => exact GoodLater_zero _
  | succ k =>
    unfold GoodLater; intro m hm μ hμ
    simp only [unfoldLater]
    show StartsWithStep m ((World.restrictStep d).unfold m hm μ) ∧
         TraceGood 2 m ((World.restrictStep d).unfold m hm μ)
    rw [D_unfold_restrictStep]
    unfold GoodLater at hd
    exact hd m (by omega) μ hμ

/-- `apply`-kont continuation is `TraceGood` given a `GoodLater` env entry. -/
private theorem apply_kont_TraceGood_GL {n : Nat} (entry : D n)
    (hgl : GoodLater (n+1) entry)
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
  · simp; exact (GoodD_stuck j (Nat.le_refl j) μ hheap).2
  · show TraceGood 2 j ((D.invis (g j (Nat.le_refl j) (Later.next (World.restrict entry (hm := hj))))).unfold j (Nat.le_refl j) μ)
    exact GoodD_invis_of_GoodLater _ (hfn g rfl j (Nat.le_refl j) _
      (GoodLater_restrict_next entry hgl hj)) j (Nat.le_refl j) μ hheap
  · simp; exact (GoodD_stuck j (Nat.le_refl j) μ hheap).2

/-! ## `LR.good` -/

private noncomputable def goodP : World.Pred D :=
  World.Pred.ofClosed (fun {n} d => GoodD n d) GoodD_restrictStep

private noncomputable def goodLookup : World.Pred (Later D) :=
  World.Pred.ofClosed (fun {n} dl => GoodLater n dl) GoodLater_restrictStep

private theorem goodComp_holds {n : Nat} (d : D n) : goodP.holds d ↔ GoodD n d :=
  World.Pred.ofClosed_holds _ _ d

private theorem goodLookup_holds {n : Nat} (dl : Later D n) :
    goodLookup.holds dl ↔ GoodLater n dl :=
  World.Pred.ofClosed_holds _ _ dl

private theorem goodLookup_holds_succ {n : Nat} (d : D n) :
    goodLookup.holds (n := n+1) d ↔ GoodLater (n+1) d :=
  goodLookup_holds (n := n+1) d

/-- The logical relation `(GoodD, GoodLater)` packaged as an `LR ByNeed.D`. -/
noncomputable def good : LR D where
  P := goodP
  Lookup := goodLookup
  Lookup_to_P := by
    intro n d h
    rw [goodLookup_holds] at h
    rw [goodComp_holds]
    exact GoodD_of_GoodLater d h
  step_to_Lookup := by
    intro n ev d h
    rw [goodComp_holds] at h
    rw [goodLookup_holds]
    exact GoodLater_of_step ev d h
  stuck := by intro n; rw [goodComp_holds]; exact GoodD_stuck
  step := by
    intro n ev d hd
    rw [goodComp_holds] at hd
    rw [goodComp_holds]
    exact GoodD_step _ ev d hd
  fn := by
    intro n f hLookup
    rw [goodComp_holds]
    apply GoodD_fn
    intro m hm dl hgl
    have := hLookup m hm dl ((goodLookup_holds dl).mpr hgl)
    exact (goodLookup_holds _).mp this
  con := by
    intro n K ds hds
    rw [goodComp_holds]
    apply GoodD_con K ds
    intro d hd
    have hgl : GoodLater (n+1) d := (goodLookup_holds_succ d).mp (hds d hd)
    exact GoodLater_next_of_GoodLater_succ d hgl
  app_closed := by
    intro n dv da hdv hLookup_da
    rw [goodComp_holds] at hdv
    rw [goodComp_holds]
    have hLookup_da : GoodLater (n+1) da := (goodLookup_holds_succ da).mp hLookup_da
    show GoodD n (D.step .app1 (Later.next
      (D.bind (World.restrict dv) (fun j _hj v =>
        match v with
        | .fn g => D.invis (g j (Nat.le_refl j) (Later.next (World.restrict da)))
        | _ => D.stuck))))
    apply GoodD_step_of_TraceGood
    have h_restr : World.restrict dv = dv := by
      rw [World.restrict.eq_1, dif_pos rfl]; simp
    rw [h_restr]
    apply D_bind_TraceGood _ _ hdv
    · intro j hj vh hfn hcon hheap
      exact apply_kont_TraceGood_GL da hLookup_da hj vh hfn hcon hheap
    · intro j hj μ' hμ'
      exact stuck_unfold_good j μ' hμ'
  case_closed := by
    intro n dv alts hdv halts
    rw [goodComp_holds] at hdv
    rw [goodComp_holds]
    show GoodD n (D.step .case1 (Later.next (Domain.select' dv alts)))
    apply GoodD_step_of_TraceGood
    have h_restr : World.restrict dv = dv := by
      rw [World.restrict.eq_1, dif_pos rfl]; simp
    intro m hm μ hμ
    simp only [Domain.select', Domain.select, h_restr]
    apply D_bind_TraceGood _ _ hdv _ _ m hm μ hμ
    · intro j hj vh hfn hcon hheap
      split
      next K ds heq =>
        split
        next _ f hfind =>
          apply GoodD_invis_of_GoodLater _ _ j (Nat.le_refl j) vh.2 hheap
          have hmem : (_, f) ∈ alts := List.mem_of_find?_eq_some hfind
          cases j
          · exact GoodLater_zero _
          · simp only [Later.hmap, Later_sequence_succ]
            apply (goodLookup_holds _).mp
            apply halts _ f hmem _ _ ds
            intro d hd
            exact (goodLookup_holds_succ d).mpr
              (hcon K ds (Value_F_ofRep_con_inv heq) d hd)
        next hfind =>
          exact (GoodD_stuck j (Nat.le_refl j) vh.2 (by simpa using hheap)).2
      next =>
        exact (GoodD_stuck j (Nat.le_refl j) vh.2 (by simpa using hheap)).2
    · intro j hj μ' hμ'
      show (NotRet j (D.stuck.unfold j _ μ') ∨ IsRetStuck j (D.stuck.unfold j _ μ')) ∧
           ∀ k', TraceGood k' j (D.stuck.unfold j _ μ')
      exact stuck_unfold_good j μ' hμ'
  bind_closed := by
    intro n ev rhs body hrhs hbody
    rw [goodComp_holds]
    intro m hm μ hμ
    simp only [Domain.bind', Domain.bind, D_fold_unfold]
    have hLookup_fetch : GoodLater (m+1)
        ((Domain.step' ev (D.invis (fetch μ.nextFree)) : D m) : Later D (m+1)) :=
      Thunk_step_invis_fetch ev μ.nextFree
    have hLookup_fetch' := (goodLookup_holds _).mpr hLookup_fetch
    have h_rhs := hrhs m hm (D.invis (fetch μ.nextFree)) hLookup_fetch'
    have h_body := hbody m hm (D.invis (fetch μ.nextFree)) hLookup_fetch'
    rw [goodComp_holds] at h_rhs h_body
    have h_memo : GoodLater m (D.memo μ.nextFree
        (Later.next (rhs m hm (D.invis (fetch μ.nextFree))))) := by
      cases m with
      | zero => exact GoodLater_zero _
      | succ k' =>
        apply GoodLater_memo
        intro k hk μ' hμ'
        simp only [unfoldLater, Later.next]
        rw [D_unfold_restrictStep]
        exact h_rhs k (by omega) μ' hμ'
    have h_heap := GoodHeap_set μ hμ μ.nextFree _ h_memo
    exact h_body m (Nat.le_refl m) _ h_heap

/-! ## Main theorems -/

private theorem HashMap_get?_empty' {α β : Type} [BEq α] [Hashable α]
    (a : α) : Std.HashMap.get? (∅ : Std.HashMap α β) a = none := by
  simp only [Std.HashMap.get?]; have : (∅ : Std.HashMap α β).inner = ∅ := rfl; rw [this]
  simp [Std.DHashMap.Const.get?, Std.DHashMap.Internal.Raw₀.Const.get?]

private theorem emptyHeap_good (n : Nat) : GoodHeap n (∅ : Heap (▹ D) n) :=
  fun _ _ h => absurd h (by rw [HashMap_get?_empty']; simp)

private theorem emptyEnv_good (n : Nat) : good.env (Env.empty : Env (D n)) :=
  good.env_empty

/-- Every trace produced by `evalByNeed` has at most 2 consecutive invisible
    steps. -/
theorem evalByNeed_noTripleInvis (n : Nat) (e : Exp) :
    NoTripleInvis n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) := by
  have : GoodD n (eval (D := D) e n (Nat.le_refl n) Env.empty) :=
    (goodComp_holds _).mp (LR.fundamental good e Env.empty (emptyEnv_good n))
  exact TraceGood_implies_NCI 2 n _
    (this n (Nat.le_refl n) ∅ (emptyHeap_good n)).2

/-- The trace of `evalByNeed n e` starts visibly. -/
theorem evalByNeed_startsVisible (n : Nat) (e : Exp) :
    StartsVisible n ((evalByNeed n e).unfold n (Nat.le_refl n) ∅) := by
  have : GoodD n (eval (D := D) e n (Nat.le_refl n) Env.empty) :=
    (goodComp_holds _).mp (LR.fundamental good e Env.empty (emptyEnv_good n))
  exact (this n (Nat.le_refl n) ∅ (emptyHeap_good n)).1

end ByNeed
