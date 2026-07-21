import AbsDen.Soundness
import AbsDen.ParametricLR

/-! # Usage analysis satisfies the abstraction laws

The order theory of the bounded usage domain's operations: every operation is
monotone, `step` commutes past `apply` and `select` up to `⊑`, `stuck` is the
least element, `bind` keeps the `ByNeed-Bind` promise by Kleene ascent, and
`update` steps are invisible. The summary laws `Beta-App` and `Beta-Sel`
remain open; they hold only for the closures `eval` produces under distinct
binders, which the logical relation does not yet communicate. -/

namespace AbsDen

/-! ## Pointwise `U` facts -/

theorem U.u0_le (u : U) : (U.u0 ⊑ u) = true := by cases u <;> decide

theorem U.add_zero (u : U) : u + U.u0 = u := by cases u <;> rfl

theorem U.zero_add (u : U) : U.u0 + u = u := by cases u <;> rfl

theorem U.mul_zero (u : U) : u * U.u0 = U.u0 := by cases u <;> rfl
theorem U.zero_mul (u : U) : U.u0 * u = U.u0 := rfl

theorem U.add_assoc (a b c : U) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem U.add_mono {a a' b b' : U} (ha : (a ⊑ a') = true) (hb : (b ⊑ b') = true) :
    (a + b ⊑ a' + b') = true := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> revert ha hb <;> decide

theorem U.mul_mono {a a' b b' : U} (ha : (a ⊑ a') = true) (hb : (b ⊑ b') = true) :
    (a * b ⊑ a' * b') = true := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> revert ha hb <;> decide

theorem U.le_add_left (a b : U) : (b ⊑ a + b) = true := by
  cases a <;> cases b <;> decide

/-! ## Readings of the `Uses` operations -/

theorem Uses.get_emp (x : Var) : Uses.emp !? x = U.u0 := by
  rw [Uses.get_eq]
  show ((∅ : Std.HashMap Var U)[x]?).getD _ = _
  simp

theorem Uses.get_add (φ₁ φ₂ : Uses) (x : Var) :
    (φ₁ + φ₂) !? x = φ₁ !? x + φ₂ !? x := by
  show (Uses.merge U.add φ₁ φ₂) !? x = _
  rw [Uses.get_eq, Uses.get_eq, Uses.get_eq, Uses.getElem?_merge]
  cases φ₂[x]? with
  | none =>
    cases φ₁[x]? with
    | none => simp [U.add_zero]
    | some u₁ => simp [U.add_zero]
  | some u₂ =>
    cases φ₁[x]? with
    | none => simp [mstep, U.zero_add]
    | some u₁ => simp only [mstep, Option.getD_some]; rfl

theorem Uses.get_smul (u : U) (φ : Uses) (x : Var) : (u * φ) !? x = u * (φ !? x) := by
  show Uses.smul u φ !? x = _
  unfold Uses.smul
  by_cases hu : (u == U.u0) = true
  · rw [if_pos hu, U.beq_iff_eq.mp hu, Uses.get_emp]
    rfl
  · rw [if_neg hu]
    rw [Uses.get_eq, Uses.get_eq]
    show ((φ.toMap.map fun _ v => u * v)[x]?).getD _ = _
    rw [Std.HashMap.getElem?_map]
    cases φ.toMap[x]? with
    | none => simp [U.mul_zero]
    | some v => simp

theorem Uses.get_singenv_self (x : Var) (u : U) : Uses.singenv x u !? x = u := by
  simp only [Uses.singenv]
  by_cases hu : (u == U.u0) = true
  · rw [if_pos hu, U.beq_iff_eq.mp hu, Uses.get_emp]
  · rw [if_neg hu, Uses.get_eq]
    show (((∅ : Std.HashMap Var U).insert x u)[x]?).getD U.u0 = u
    rw [Std.HashMap.getElem?_insert_self]
    rfl

/-- Distinct variables compare `false` under the value-wise `BEq`. -/
theorem Var.beq_eq_false {x y : Var} (h : y ≠ x) : ¬(y == x) = true :=
  fun hbeq => h (Subtype.ext (by simpa using hbeq))

theorem Uses.get_singenv_ne {x y : Var} (u : U) (h : y ≠ x) :
    Uses.singenv y u !? x = U.u0 := by
  simp only [Uses.singenv]
  by_cases hu : (u == U.u0) = true
  · rw [if_pos hu, Uses.get_emp]
  · rw [if_neg hu, Uses.get_eq]
    show (((∅ : Std.HashMap Var U).insert y u)[x]?).getD U.u0 = U.u0
    rw [Std.HashMap.getElem?_insert, if_neg (Var.beq_eq_false h)]
    simp

theorem Uses.get_ext_self (φ : Uses) (x : Var) (u : U) : Uses.ext φ x u !? x = u := by
  simp only [Uses.ext]
  by_cases hu : (u == U.u0) = true
  · rw [if_pos hu, U.beq_iff_eq.mp hu, Uses.get_eq]
    show ((φ.toMap.erase x)[x]?).getD U.u0 = U.u0
    rw [Std.HashMap.getElem?_erase_self]
    rfl
  · rw [if_neg hu, Uses.get_eq]
    show ((φ.toMap.insert x u)[x]?).getD U.u0 = u
    rw [Std.HashMap.getElem?_insert_self]
    rfl

theorem Uses.get_ext_ne (φ : Uses) {x y : Var} (u : U) (h : y ≠ x) :
    Uses.ext φ y u !? x = φ !? x := by
  simp only [Uses.ext]
  by_cases hu : (u == U.u0) = true
  · rw [if_pos hu, Uses.get_eq, Uses.get_eq]
    show ((φ.toMap.erase y)[x]?).getD U.u0 = (φ[x]?).getD U.u0
    rw [Std.HashMap.getElem?_erase, if_neg (Var.beq_eq_false h)]
    rfl
  · rw [if_neg hu, Uses.get_eq, Uses.get_eq]
    show ((φ.toMap.insert y u)[x]?).getD U.u0 = (φ[x]?).getD U.u0
    rw [Std.HashMap.getElem?_insert, if_neg (Var.beq_eq_false h)]
    rfl

theorem Uses.le_refl (φ : Uses) : (φ ⊑ φ) = true :=
  (Uses.le_iff_get φ φ).mpr fun _ => U.le_refl _

theorem Uses.add_mono {φ₁ φ₁' φ₂ φ₂' : Uses} (h₁ : (φ₁ ⊑ φ₁') = true)
    (h₂ : (φ₂ ⊑ φ₂') = true) : (φ₁ + φ₂ ⊑ φ₁' + φ₂') = true := by
  rw [Uses.le_iff_get] at h₁ h₂ ⊢
  intro x
  rw [Uses.get_add, Uses.get_add]
  exact U.add_mono (h₁ x) (h₂ x)

theorem Uses.smul_mono {u u' : U} {φ φ' : Uses} (hu : (u ⊑ u') = true)
    (hφ : (φ ⊑ φ') = true) : (u * φ ⊑ u' * φ') = true := by
  rw [Uses.le_iff_get] at hφ ⊢
  intro x
  rw [Uses.get_smul, Uses.get_smul]
  exact U.mul_mono hu (hφ x)

/-! ## Summary views: `peel`, `tailSup`, `widen` -/

theorem UValue.le_refl (v : UValue) : (v ⊑ v) = true :=
  (UValue.le_iff_At v v).mpr fun _ => U.le_refl _

theorem UValue.peel_fst_At (v : UValue) : (peel v).1 = v.At 0 := by cases v <;> rfl

theorem UValue.peel_snd_At (v : UValue) (i : Nat) : (peel v).2.At i = v.At (i + 1) := by
  cases v <;> rfl

theorem UValue.peel_fst_mono {v w : UValue} (h : (v ⊑ w) = true) :
    ((peel v).1 ⊑ (peel w).1) = true := by
  rw [UValue.peel_fst_At, UValue.peel_fst_At]
  exact (UValue.le_iff_At v w).mp h 0

theorem UValue.peel_snd_mono {v w : UValue} (h : (v ⊑ w) = true) :
    ((peel v).2 ⊑ (peel w).2) = true := by
  rw [UValue.le_iff_At]
  intro i
  rw [UValue.peel_snd_At, UValue.peel_snd_At]
  exact (UValue.le_iff_At v w).mp h (i + 1)

theorem UValue.at_le_tailSup (v : UValue) (i : Nat) : (v.At i ⊑ v.tailSup) = true := by
  induction v generalizing i with
  | rep u => exact U.le_refl u
  | cons u w ih =>
    cases i with
    | zero =>
      show (u ⊑ u ⊔ w.tailSup) = true
      cases u <;> cases w.tailSup <;> decide
    | succ i =>
      show (w.At i ⊑ u ⊔ w.tailSup) = true
      refine U.le_trans (ih i) ?_
      cases u <;> cases w.tailSup <;> decide

theorem UValue.tailSup_le {v : UValue} {b : U} (h : ∀ i, (v.At i ⊑ b) = true) :
    (v.tailSup ⊑ b) = true := by
  induction v with
  | rep u => exact h 0
  | cons u w ih =>
    show (u ⊔ w.tailSup ⊑ b) = true
    rw [U.join_le_iff]
    exact ⟨h 0, ih fun i => h (i + 1)⟩

/-- Drop the first `k` positions of a summary. -/
def UValue.dropTail : Nat → UValue → UValue
  | 0, v => v
  | k + 1, v => dropTail k (peel v).2

theorem UValue.dropTail_At (k : Nat) (v : UValue) (i : Nat) :
    (v.dropTail k).At i = v.At (k + i) := by
  induction k generalizing v i with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    show ((peel v).2.dropTail k).At i = _
    rw [ih, UValue.peel_snd_At]
    congr 1
    omega

theorem UValue.At_widen (k : Nat) (v : UValue) (i : Nat) :
    (v.widen k).At i = if i < k then v.At i else (v.dropTail k).tailSup := by
  induction k generalizing v i with
  | zero =>
    show (UValue.rep v.tailSup).At i = _
    simp [UValue.dropTail]
  | succ k ih =>
    cases v with
    | rep u =>
      show (UValue.rep u).At i = _
      have hdrop : ∀ j, (UValue.rep u).dropTail j = UValue.rep u := by
        intro j
        induction j with
        | zero => rfl
        | succ j ihj => exact ihj
      rw [hdrop]
      simp [UValue.At_rep, UValue.tailSup]
    | cons u w =>
      cases i with
      | zero => simp [UValue.widen]
      | succ i =>
        show (w.widen k).At i = _
        rw [ih]
        show _ = if i + 1 < k + 1 then w.At i else ((UValue.cons u w).dropTail (k + 1)).tailSup
        have : (UValue.cons u w).dropTail (k + 1) = w.dropTail k := rfl
        rw [this]
        congr 1
        simp [Nat.succ_lt_succ_iff]

theorem UValue.le_widen (k : Nat) (v : UValue) : (v ⊑ v.widen k) = true := by
  rw [UValue.le_iff_At]
  intro i
  rw [UValue.At_widen]
  by_cases hik : i < k
  · rw [if_pos hik]; exact U.le_refl _
  · rw [if_neg hik]
    have : v.At i = (v.dropTail k).At (i - k) := by
      rw [UValue.dropTail_At]; congr 1; omega
    rw [this]
    exact UValue.at_le_tailSup _ _

theorem UValue.widen_mono {v w : UValue} (h : (v ⊑ w) = true) (k : Nat) :
    (v.widen k ⊑ w.widen k) = true := by
  have hpt := (UValue.le_iff_At v w).mp h
  rw [UValue.le_iff_At]
  intro i
  rw [UValue.At_widen, UValue.At_widen]
  by_cases hik : i < k
  · rw [if_pos hik, if_pos hik]; exact hpt i
  · rw [if_neg hik, if_neg hik]
    refine UValue.tailSup_le fun j => ?_
    rw [UValue.dropTail_At]
    refine U.le_trans (hpt (k + j)) ?_
    rw [show w.At (k + j) = (w.dropTail k).At j from (UValue.dropTail_At k w j).symm]
    exact UValue.at_le_tailSup _ _

theorem UValue.widen_of_length_le {v : UValue} {k : Nat} (h : v.length ≤ k) :
    v.widen k = v := by
  induction k generalizing v with
  | zero =>
    cases v with
    | rep u => rfl
    | cons u w => simp [UValue.length] at h
  | succ k ih =>
    cases v with
    | rep u => rfl
    | cons u w =>
      show UValue.cons u (w.widen k) = _
      rw [ih (Nat.le_of_succ_le_succ h)]

theorem UValue.widen_widen_le (k : Nat) (v : UValue) :
    ((v.widen k).widen k ⊑ v.widen k) = true := by
  rw [UValue.widen_of_length_le (UValue.widen_length k v)]
  exact UValue.le_refl _

/-! ## The trace order, componentwise -/

theorem UD.le_iff (a b : UD) :
    (a ⊑ b) = true ↔ (a.uses ⊑ b.uses) = true ∧ (a.val ⊑ b.val) = true := by
  show ((a.uses ⊔ b.uses == b.uses) && (a.val ⊔ b.val == b.val)) = true ↔ _
  rw [Bool.and_eq_true]; rfl

theorem UD.le_refl (d : UD) : (d ⊑ d) = true :=
  (UD.le_iff d d).mpr ⟨Uses.le_refl d.uses, UValue.le_refl d.val⟩

theorem UD.apply_def (d a : UD) :
    UD.apply d a = ⟨d.uses + (peel d.val).1 * a.uses, (peel d.val).2⟩ := by
  obtain ⟨φ₁, v₁⟩ := d
  obtain ⟨φ₂, v₂⟩ := a
  rcases h : peel v₁ with ⟨u, w⟩
  simp [UD.apply, h]

theorem UD.select_def (d : UD) (fs : List (ConTag × Nat × (List UD → UD))) :
    UD.select d fs =
      ⟨d.uses + (lub (fs.map (fun kf : ConTag × Nat × (List UD → UD) =>
          kf.2.2 (UD.select.fieldProxies kf.2.1)))).uses,
       (lub (fs.map (fun kf : ConTag × Nat × (List UD → UD) =>
          kf.2.2 (UD.select.fieldProxies kf.2.1)))).val⟩ := by
  obtain ⟨φ, v⟩ := d
  show UT.bind ⟨φ, v⟩ (fun _ => lub (fs.map fun kf => kf.2.2 (UD.select.fieldProxies kf.2.1))) = _
  rcases h : lub (fs.map fun kf => kf.2.2 (UD.select.fieldProxies kf.2.1)) with ⟨φL, vL⟩
  simp [UT.bind, h]

theorem UD.step_look (y : Var) (d : UD) :
    UD.step (.look y) d = ⟨Uses.singenv y .u1 + d.uses, d.val⟩ := by
  obtain ⟨φ, v⟩ := d; rfl

theorem UD.step_mono (ev : Event) {a b : UD} (h : (a ⊑ b) = true) :
    (UD.step ev a ⊑ UD.step ev b) = true := by
  cases ev
  case look y =>
    rw [UD.step_look, UD.step_look, UD.le_iff]
    rw [UD.le_iff] at h
    exact ⟨Uses.add_mono (Uses.le_refl _) h.1, h.2⟩
  all_goals exact h

theorem UD.le_step (ev : Event) (d : UD) : (d ⊑ UD.step ev d) = true := by
  cases ev
  case look y =>
    rw [UD.step_look, UD.le_iff]
    refine ⟨?_, UValue.le_refl _⟩
    rw [Uses.le_iff_get]
    intro x
    rw [Uses.get_add]
    exact U.le_add_left _ _
  all_goals exact UD.le_refl d

theorem UD.apply_mono {d d' a a' : UD} (h₁ : (d ⊑ d') = true) (h₂ : (a ⊑ a') = true) :
    (UD.apply d a ⊑ UD.apply d' a') = true := by
  rw [UD.apply_def, UD.apply_def, UD.le_iff]
  rw [UD.le_iff] at h₁ h₂
  exact ⟨Uses.add_mono h₁.1 (Uses.smul_mono (UValue.peel_fst_mono h₁.2) h₂.1),
         UValue.peel_snd_mono h₁.2⟩

theorem UD.select_mono (fs : List (ConTag × Nat × (List UD → UD))) {d d' : UD}
    (h : (d ⊑ d') = true) : (UD.select d fs ⊑ UD.select d' fs) = true := by
  rw [UD.select_def, UD.select_def, UD.le_iff]
  rw [UD.le_iff] at h
  exact ⟨Uses.add_mono h.1 (Uses.le_refl _), UValue.le_refl _⟩

theorem Uses.add_assoc_le (a b c : Uses) : (a + (b + c) ⊑ (a + b) + c) = true := by
  rw [Uses.le_iff_get]
  intro x
  rw [Uses.get_add, Uses.get_add, Uses.get_add, Uses.get_add, U.add_assoc]
  exact U.le_refl _

/-! ## Order bridges between `UD` and `UDk` -/

theorem UDk.embed_mono {k : Nat} {a b : UDk k} (h : (a ⊑ b) = true) :
    (a.embed ⊑ b.embed) = true := by
  rw [UDk.le_iff] at h
  rw [UD.le_iff]
  exact ⟨h.1, h.2⟩

theorem UDk.wrap_le_wrap {k : Nat} {z₁ z₂ : UD} (h : (z₁ ⊑ z₂) = true) :
    (UDk.wrap (k := k) z₁ ⊑ UDk.wrap z₂) = true := by
  rw [UD.le_iff] at h
  rw [UDk.le_iff]
  exact ⟨h.1, UValue.widen_mono h.2 k⟩

theorem UDk.wrap_embed {k : Nat} (d : UDk k) : UDk.wrap d.embed = d := by
  obtain ⟨φ, v, hv⟩ := d
  exact congrArg (UT.mk φ) (Subtype.ext (UValue.widen_of_length_le hv))

/-- The bounded step is monotone. -/
theorem UDk.step_mono {k : Nat} (ev : Event) {a b : UDk k} (h : a ⊑ b) :
    AbstractDomain.step (D := UDk k) ev a ⊑ AbstractDomain.step (D := UDk k) ev b :=
  UDk.wrap_le_wrap (UD.step_mono ev (UDk.embed_mono h))

/-- A look charges one use of its variable on top of the tail's usage. -/
theorem UDk.step_look_uses {k : Nat} (y : Var) (d : UDk k) :
    (AbstractDomain.step (D := UDk k) (.look y) d).uses = Uses.singenv y .u1 + d.uses := by
  show (UD.step (.look y) d.embed).uses = _
  rw [UD.step_look]
  rfl

/-- Any step other than a look at `x` leaves the usage of `x` unchanged. -/
theorem UDk.step_uses_get_ne {k : Nat} {x : Var} {ev : Event} (hev : ev ≠ .look x)
    (d : UDk k) :
    (AbstractDomain.step (D := UDk k) ev d).uses !? x = d.uses !? x := by
  cases ev with
  | look y =>
    rw [UDk.step_look_uses, Uses.get_add,
      Uses.get_singenv_ne _ (fun h => hev (by rw [h]))]
    show U.add .u0 _ = _
    rfl
  | update => rfl
  | app1 => rfl
  | app2 => rfl
  | case1 => rfl
  | case2 => rfl
  | let1 => rfl

/-! ## Pointwise usage readings of `apply` and `fn`

A single variable's usage after a combinator, read off directly. Applying a
summary adds its head times the argument's usage; the head of a `fn` is the
binder's own reading in the body, so an unused binder annihilates the
argument. -/

/-- Applying a summary adds the summary's head, times the argument's usage. -/
theorem UDk.apply_uses_get {k : Nat} (f a : UDk k) (x : Var) :
    (AbstractDomain.apply (D := UDk k) f a).uses !? x
      = f.uses !? x + (peel f.val.val).1 * (a.uses !? x) := by
  show (UD.apply f.embed a.embed).uses !? x = _
  rw [UD.apply_def, Uses.get_add, Uses.get_smul]
  rfl

/-- A summary hides its binder, so its usage away from the binder is the
    body's. -/
theorem UDk.fn_uses_get_ne {k : Nat} (y : Var) (f : UDk k → UDk k) {x : Var}
    (hxy : x ≠ y) :
    (AbstractDomain.fn (D := UDk k) y f).uses !? x
      = (f (UDk.wrap (UD.fn.proxy y))).uses !? x := by
  show (Uses.ext (f (UDk.wrap (UD.fn.proxy y))).uses y U.u0) !? x = _
  rw [Uses.get_ext_ne _ _ (Ne.symm hxy)]

/-- The head of a summary is the binder's own reading in the body. -/
theorem UDk.fn_head {k : Nat} (hk : 0 < k) (y : Var) (f : UDk k → UDk k) :
    (peel (AbstractDomain.fn (D := UDk k) y f).val.val).1
      = (f (UDk.wrap (UD.fn.proxy y))).uses !? y := by
  rw [UValue.peel_fst_At]
  show (UValue.widen k (UValue.cons ((f (UDk.wrap (UD.fn.proxy y))).uses !? y)
    (f (UDk.wrap (UD.fn.proxy y))).val.val)).At 0 = _
  rw [UValue.At_widen, if_pos hk]
  rfl

/-- The proxy for a binder reads zero away from the binder. -/
theorem UDk.proxy_uses_get_ne {k : Nat} {y x : Var} (hxy : x ≠ y) :
    (UDk.wrap (k := k) (UD.fn.proxy y)).uses !? x = U.u0 :=
  Uses.get_singenv_ne _ (Ne.symm hxy)

theorem UDk.stuck_le {k : Nat} (d : UDk k) :
    ((AbstractDomain.stuck : UDk k) ⊑ d) = true := by
  rw [UDk.le_iff]
  constructor
  · show (Uses.emp ⊑ d.uses) = true
    rw [Uses.le_iff_get]
    intro x
    rw [Uses.get_emp]
    exact U.u0_le _
  · show ((UValue.rep U.u0).widen k ⊑ d.val.val) = true
    rw [UValue.widen_of_length_le (Nat.zero_le k)]
    rw [UValue.le_iff_At]
    intro i
    exact U.u0_le _

/-- Widening the function's summary between two bounded operations only
    weakens `apply`, uniformly in a usage prefix `φe`. -/
theorem UDk.wrap_apply_le {k : Nat} (φe : Uses) (d a : UD) :
    (UDk.wrap (k := k) ⟨φe + (UD.apply d a).uses, (UD.apply d a).val.widen k⟩
      ⊑ UDk.wrap (UD.apply ⟨φe + d.uses, d.val.widen k⟩ a)) = true := by
  rw [UD.apply_def d a, UD.apply_def ⟨φe + d.uses, d.val.widen k⟩ a, UDk.le_iff]
  constructor
  · show (φe + (d.uses + (peel d.val).1 * a.uses)
        ⊑ (φe + d.uses) + (peel (d.val.widen k)).1 * a.uses) = true
    refine le_iff_le.mp (Std.IsPreorder.le_trans _ _ _
      (le_iff_le.mpr (Uses.add_mono (Uses.le_refl φe) (Uses.add_mono (Uses.le_refl d.uses)
        (Uses.smul_mono (UValue.peel_fst_mono (UValue.le_widen k d.val)) (Uses.le_refl a.uses)))))
      (le_iff_le.mpr (Uses.add_assoc_le _ _ _)))
  · show (((peel d.val).2.widen k).widen k ⊑ ((peel (d.val.widen k)).2).widen k) = true
    rw [UValue.widen_of_length_le (UValue.widen_length k _)]
    exact UValue.widen_mono (UValue.peel_snd_mono (UValue.le_widen k d.val)) k

/-- The prefix-free variant of `UDk.wrap_apply_le`. -/
theorem UDk.wrap_apply_le' {k : Nat} (d a : UD) :
    (UDk.wrap (k := k) ⟨(UD.apply d a).uses, (UD.apply d a).val.widen k⟩
      ⊑ UDk.wrap (UD.apply ⟨d.uses, d.val.widen k⟩ a)) = true := by
  rw [UD.apply_def d a, UD.apply_def ⟨d.uses, d.val.widen k⟩ a, UDk.le_iff]
  constructor
  · show (d.uses + (peel d.val).1 * a.uses
        ⊑ d.uses + (peel (d.val.widen k)).1 * a.uses) = true
    exact Uses.add_mono (Uses.le_refl _)
      (Uses.smul_mono (UValue.peel_fst_mono (UValue.le_widen k d.val)) (Uses.le_refl _))
  · show (((peel d.val).2.widen k).widen k ⊑ ((peel (d.val.widen k)).2).widen k) = true
    rw [UValue.widen_of_length_le (UValue.widen_length k _)]
    exact UValue.widen_mono (UValue.peel_snd_mono (UValue.le_widen k d.val)) k

/-- `step` commutes past a widened `select`, uniformly in a usage prefix. -/
theorem UDk.wrap_select_le {k : Nat} (φe : Uses) (d : UD)
    (fs : List (ConTag × Nat × (List UD → UD))) :
    (UDk.wrap (k := k) ⟨φe + (UD.select d fs).uses, (UD.select d fs).val.widen k⟩
      ⊑ UDk.wrap (UD.select ⟨φe + d.uses, d.val.widen k⟩ fs)) = true := by
  rw [UD.select_def d fs, UD.select_def ⟨φe + d.uses, d.val.widen k⟩ fs, UDk.le_iff]
  exact ⟨Uses.add_assoc_le _ _ _, UValue.widen_widen_le k _⟩

/-- The prefix-free variant of `UDk.wrap_select_le`, an order-equality. -/
theorem UDk.wrap_select_le' {k : Nat} (d : UD)
    (fs : List (ConTag × Nat × (List UD → UD))) :
    (UDk.wrap (k := k) ⟨(UD.select d fs).uses, (UD.select d fs).val.widen k⟩
      ⊑ UDk.wrap (UD.select ⟨d.uses, d.val.widen k⟩ fs)) = true := by
  rw [UD.select_def d fs, UD.select_def ⟨d.uses, d.val.widen k⟩ fs, UDk.le_iff]
  exact ⟨Uses.le_refl _, UValue.widen_widen_le k _⟩

/-! ## Freshness reads as a `u0` column

The concrete content of `Fresh` at the bounded usage domain: a fresh variable's
reading is `u0`. Instantiate the impredicative quantifier at the `x`-column
reading and check every operation's closure clause. -/

theorem UD.get_foldl_apply_eq_zero {x : Var} :
    ∀ (ds : List UD) (acc : UD), acc.uses !? x = U.u0 →
      (∀ τ ∈ ds, τ.uses !? x = U.u0) → (ds.foldl UD.apply acc).uses !? x = U.u0
  | [], _, hacc, _ => hacc
  | τ :: ds, acc, hacc, hds => by
    refine UD.get_foldl_apply_eq_zero ds (UD.apply acc τ) ?_
      (fun τ' hτ' => hds τ' (List.mem_cons_of_mem _ hτ'))
    rw [UD.apply_def]
    show (acc.uses + (peel acc.val).1 * τ.uses) !? x = U.u0
    rw [Uses.get_add, Uses.get_smul, hacc, hds τ (List.mem_cons_self ..), U.mul_zero]
    rfl

theorem UD.get_lub_eq_zero {x : Var} :
    ∀ {l : List UD}, (∀ τ ∈ l, τ.uses !? x = U.u0) → (lub l).uses !? x = U.u0
  | [], _ => Uses.get_emp x
  | τ :: l, h => by
    show (τ.uses ⊔ (lub l).uses) !? x = U.u0
    rw [show τ.uses ⊔ (lub l).uses = Uses.merge U.join τ.uses (lub l).uses from rfl,
      Uses.get_join, h τ (List.mem_cons_self ..),
      UD.get_lub_eq_zero (fun τ' hτ' => h τ' (List.mem_cons_of_mem _ hτ'))]
    rfl

/-- A variable absent from both sides is absent from their join. -/
theorem UDk.get_sup_eq_zero {k : Nat} {x : Var} {a b : UDk k}
    (ha : a.uses !? x = U.u0) (hb : b.uses !? x = U.u0) :
    (a ⊔ b).uses !? x = U.u0 := by
  show (Uses.merge U.join a.uses b.uses) !? x = U.u0
  rw [Uses.get_join, ha, hb]
  rfl

/-- The `x`-column reading `u0` is closed under every combinator that does not
    look up `x`. -/
theorem UDk.freshClosed_get_eq_zero (k : Nat) (x : Var) :
    FreshClosed (D := Discrete (UDk k)) x (fun d => d.uses !? x = U.u0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Uses.get_emp x
  · intro ev d hev hd
    cases ev
    case look y =>
      have hyx : y ≠ x := fun hxy => hev (hxy ▸ rfl)
      show (Uses.singenv y .u1 + d.embed.uses) !? x = U.u0
      rw [Uses.get_add, Uses.get_singenv_ne _ hyx]
      show U.u0 + d.uses !? x = U.u0
      rw [hd]
      rfl
    all_goals exact hd
  · intro d a hd ha
    show (UD.apply d.embed a.embed).uses !? x = U.u0
    rw [UD.apply_def]
    show (d.embed.uses + (peel d.embed.val).1 * a.embed.uses) !? x = U.u0
    rw [Uses.get_add, Uses.get_smul]
    show d.uses !? x + _ * (a.uses !? x) = U.u0
    rw [hd, ha, U.mul_zero]
    rfl
  · intro K ds hds
    show (UD.con K (ds.map UDk.embed)).uses !? x = U.u0
    refine UD.get_foldl_apply_eq_zero _ _ (Uses.get_emp x) fun τ hτ => ?_
    obtain ⟨τ', hτ', rfl⟩ := List.mem_map.mp hτ
    exact hds τ' hτ'
  · intro d alts hd halts
    show (UD.select d.embed ((alts.map (fun p => (p.1, p.2.1, p.2.2.f))).map
      (fun p => (p.1, p.2.1, fun ds => (p.2.2 (ds.map UDk.wrap)).embed)))).uses !? x = U.u0
    rw [UD.select_def]
    show (d.embed.uses + _) !? x = U.u0
    rw [Uses.get_add]
    show d.uses !? x + _ = U.u0
    rw [hd, UD.get_lub_eq_zero, U.add_zero]
    intro τ hτ
    rw [List.map_map, List.map_map] at hτ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
    show (p.2.2 ((UD.select.fieldProxies p.2.1).map UDk.wrap)).uses !? x = U.u0
    refine halts p hp _ fun τ' hτ' => ?_
    obtain ⟨τ'', hτ'', rfl⟩ := List.mem_map.mp hτ'
    rw [List.eq_of_mem_replicate hτ'']
    exact Uses.get_emp x
  · intro y f hf
    by_cases hyx : y = x
    · subst hyx
      show Uses.ext (f (UDk.wrap (UD.fn.proxy y))).embed.uses y U.u0 !? y = U.u0
      exact Uses.get_ext_self _ _ _
    · show Uses.ext (f (UDk.wrap (UD.fn.proxy y))).embed.uses y U.u0 !? x = U.u0
      rw [Uses.get_ext_ne _ _ hyx]
      exact hf (UDk.wrap (UD.fn.proxy y)) (Uses.get_singenv_ne _ hyx)
  · intro rhs body hrhs hbody
    exact hbody _ (kleeneFix_pred (a := UDk k) (P := fun d => d.uses !? x = U.u0)
      (fun d => rhs d) (Uses.get_emp x)
      (fun _ _ ha hb => UDk.get_sup_eq_zero ha hb) hrhs)

/-- The reading of a fresh variable is `u0`. -/
theorem UDk.get_eq_zero_of_fresh {k : Nat} {x : Var} {d : UDk k}
    (h : Fresh (D := Discrete (UDk k)) x d) : d.uses !? x = U.u0 :=
  h _ (UDk.freshClosed_get_eq_zero k x)

/-! ## Abstract substitution

The paper's substitution operation on usage environments: retarget the
`x`-column at the argument usage `φa`, scaled by how often `x` is read. Its
order theory is pointwise; each reading obligation is a closed `U` fact
decided by enumeration. -/

theorem U.subst_add_pt (a b c d e u : U) :
    (a + b * e) + u * (c + d * e) ⊑ (a + u * c) + (b + u * d) * e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases u <;> decide

theorem U.subst_add_col (b d e u : U) :
    b * e + u * (d * e) ⊑ (b + u * d) * e := by
  cases b <;> cases d <;> cases e <;> cases u <;> decide

theorem U.subst_join_pt (a b c d e : U) :
    (a + b * e) ⊔ (c + d * e) ⊑ (a ⊔ c) + (b ⊔ d) * e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem U.subst_join_col (b d e : U) :
    (b * e) ⊔ (d * e) ⊑ (b ⊔ d) * e := by
  cases b <;> cases d <;> cases e <;> decide

theorem U.subst_look_pt (s a b e : U) :
    s + (a + b * e) ⊑ (s + a) + (U.u0 + b) * e := by
  cases s <;> cases a <;> cases b <;> cases e <;> decide

theorem U.subst_look_col (b e : U) :
    U.u0 + b * e ⊑ (U.u0 + b) * e := by
  cases b <;> cases e <;> decide

/-- The Lat join of usage environments reads pointwise. -/
theorem Uses.get_sup (φ ψ : Uses) (z : Var) : (φ ⊔ ψ) !? z = φ !? z ⊔ ψ !? z :=
  Uses.get_join φ ψ z

/-- Abstract substitution of the argument usage `φa` for the binder `x`. -/
def Uses.subst (φ : Uses) (x : Var) (φa : Uses) : Uses :=
  Uses.ext φ x .u0 + (φ !? x) * φa

theorem Uses.get_subst_self (φ : Uses) (x : Var) (φa : Uses) :
    φ.subst x φa !? x = (φ !? x) * (φa !? x) := by
  show (Uses.ext φ x .u0 + (φ !? x) * φa) !? x = _
  rw [Uses.get_add, Uses.get_ext_self, Uses.get_smul, U.zero_add]

theorem Uses.get_subst_ne (φ : Uses) {x z : Var} (φa : Uses) (h : z ≠ x) :
    φ.subst x φa !? z = φ !? z + (φ !? x) * (φa !? z) := by
  show (Uses.ext φ x .u0 + (φ !? x) * φa) !? z = _
  rw [Uses.get_add, Uses.get_smul, Uses.get_ext_ne _ _ (Ne.symm h)]

/-- Substitution is monotone in the substitutee. -/
theorem Uses.subst_mono {φ φ' : Uses} (x : Var) (φa : Uses)
    (h : φ ⊑ φ') : φ.subst x φa ⊑ φ'.subst x φa := by
  rw [Uses.le_iff_get] at h ⊢
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Uses.get_subst_self, Uses.get_subst_self]
    exact U.mul_mono (h z) (U.le_refl _)
  · rw [Uses.get_subst_ne _ _ hz, Uses.get_subst_ne _ _ hz]
    exact U.add_mono (h z) (U.mul_mono (h x) (U.le_refl _))

/-- A lookup of a variable other than the substituted one floats out of the
    substitution. -/
theorem Uses.singenv_add_subst_le {x y : Var} (h : y ≠ x) (φ φa : Uses) :
    Uses.singenv y .u1 + φ.subst x φa
      ⊑ (Uses.singenv y .u1 + φ).subst x φa := by
  rw [Uses.le_iff_get]
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Uses.get_add, Uses.get_subst_self, Uses.get_subst_self, Uses.get_add,
      Uses.get_singenv_ne _ h]
    exact U.subst_look_col _ _
  · rw [Uses.get_add, Uses.get_subst_ne _ _ hz, Uses.get_subst_ne _ _ hz,
      Uses.get_add, Uses.get_add, Uses.get_singenv_ne _ h]
    exact U.subst_look_pt _ _ _ _

/-- Substitution distributes over the usage of an application. -/
theorem Uses.subst_add_le (x : Var) (φa : Uses) (φ₁ φ₂ : Uses) (u : U) :
    φ₁.subst x φa + u * (φ₂.subst x φa) ⊑ (φ₁ + u * φ₂).subst x φa := by
  rw [Uses.le_iff_get]
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Uses.get_add, Uses.get_smul, Uses.get_subst_self, Uses.get_subst_self,
      Uses.get_subst_self, Uses.get_add, Uses.get_smul]
    exact U.subst_add_col _ _ _ _
  · rw [Uses.get_add, Uses.get_smul, Uses.get_subst_ne _ _ hz,
      Uses.get_subst_ne _ _ hz, Uses.get_subst_ne _ _ hz,
      Uses.get_add, Uses.get_smul, Uses.get_add, Uses.get_smul]
    exact U.subst_add_pt _ _ _ _ _ _

/-- Substitution distributes over joins. -/
theorem Uses.subst_join_le (x : Var) (φa : Uses) (φ₁ φ₂ : Uses) :
    (φ₁.subst x φa) ⊔ (φ₂.subst x φa) ⊑ (φ₁ ⊔ φ₂).subst x φa := by
  rw [Uses.le_iff_get]
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Uses.get_sup, Uses.get_subst_self, Uses.get_subst_self,
      Uses.get_subst_self, Uses.get_sup]
    exact U.subst_join_col _ _ _
  · rw [Uses.get_sup, Uses.get_subst_ne _ _ hz, Uses.get_subst_ne _ _ hz,
      Uses.get_subst_ne _ _ hz, Uses.get_sup, Uses.get_sup]
    exact U.subst_join_pt _ _ _ _ _

/-! ## Order kit for the substitution relation -/

theorem U.one_mul (u : U) : U.u1 * u = u := by cases u <;> rfl

theorem U.le_omega (u : U) : u ⊑ U.uω := by cases u <;> decide

theorem U.join_mono {a a' b b' : U} (ha : a ⊑ a') (hb : b ⊑ b') :
    a ⊔ b ⊑ a' ⊔ b' := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> revert ha hb <;> decide

theorem U.le_add_zero_mul (w e : U) : w ⊑ w + U.u0 * e := by
  cases w <;> cases e <;> decide

theorem U.subst_bind_pt (a b c d e : U) :
    (a + b * e) + (c + d * e) ⊑ (a + c) + (b + d) * e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem U.subst_bind_col (b d e : U) :
    b * e + d * e ⊑ (b + d) * e := by
  cases b <;> cases d <;> cases e <;> decide

theorem Uses.le_trans {φ₁ φ₂ φ₃ : Uses} (h₁ : φ₁ ⊑ φ₂)
    (h₂ : φ₂ ⊑ φ₃) : φ₁ ⊑ φ₃ := by
  rw [Uses.le_iff_get] at h₁ h₂ ⊢
  exact fun z => U.le_trans (h₁ z) (h₂ z)

theorem Uses.sup_mono {φ₁ φ₁' φ₂ φ₂' : Uses} (h₁ : φ₁ ⊑ φ₁')
    (h₂ : φ₂ ⊑ φ₂') : φ₁ ⊔ φ₂ ⊑ φ₁' ⊔ φ₂' := by
  rw [Uses.le_iff_get] at h₁ h₂ ⊢
  intro z
  rw [Uses.get_sup, Uses.get_sup]
  exact U.join_mono (h₁ z) (h₂ z)

/-- Substitution distributes over the usage of a sequencing. -/
theorem Uses.subst_seq_le (x : Var) (φa : Uses) (φ₁ φ₂ : Uses) :
    φ₁.subst x φa + φ₂.subst x φa ⊑ (φ₁ + φ₂).subst x φa := by
  rw [Uses.le_iff_get]
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Uses.get_add, Uses.get_subst_self, Uses.get_subst_self, Uses.get_subst_self,
      Uses.get_add]
    exact U.subst_bind_col _ _ _
  · rw [Uses.get_add, Uses.get_subst_ne _ _ hz, Uses.get_subst_ne _ _ hz,
      Uses.get_subst_ne _ _ hz, Uses.get_add, Uses.get_add]
    exact U.subst_bind_pt _ _ _ _ _

/-- Deleting a binder other than `x` commutes with substitution. -/
theorem Uses.ext_subst_le {x y : Var} (hyx : y ≠ x) (φa : Uses) {φ₁ φ₂ : Uses}
    (h : φ₁ ⊑ Uses.subst φ₂ x φa) :
    Uses.ext φ₁ y U.u0 ⊑ Uses.subst (Uses.ext φ₂ y U.u0) x φa := by
  rw [Uses.le_iff_get] at h ⊢
  intro z
  by_cases hzy : z = y
  · subst hzy
    rw [Uses.get_ext_self]
    exact U.u0_le _
  · by_cases hzx : z = x
    · subst hzx
      have hz := h z
      rw [Uses.get_subst_self] at hz
      rw [Uses.get_ext_ne _ _ hyx, Uses.get_subst_self, Uses.get_ext_ne _ _ hyx]
      exact hz
    · have hz := h z
      rw [Uses.get_subst_ne _ _ hzx] at hz
      rw [Uses.get_ext_ne _ _ (Ne.symm hzy), Uses.get_subst_ne _ _ hzx,
        Uses.get_ext_ne _ _ (Ne.symm hzy), Uses.get_ext_ne _ _ hyx]
      exact hz

/-- The reading of a binder absent from the argument survives substitution. -/
theorem Uses.subst_get_of_absent {x y : Var} (φa : Uses) (hay : φa !? y = U.u0)
    (hyx : y ≠ x) {φ₁ φ₂ : Uses} (h : φ₁ ⊑ Uses.subst φ₂ x φa) :
    φ₁ !? y ⊑ φ₂ !? y := by
  rw [Uses.le_iff_get] at h
  have hy := h y
  rw [Uses.get_subst_ne _ _ hyx, hay, U.mul_zero, U.add_zero] at hy
  exact hy

theorem UValue.le_trans {v₁ v₂ v₃ : UValue} (h₁ : v₁ ⊑ v₂)
    (h₂ : v₂ ⊑ v₃) : v₁ ⊑ v₃ := by
  rw [UValue.le_iff_At] at h₁ h₂ ⊢
  exact fun i => U.le_trans (h₁ i) (h₂ i)

theorem UValue.cons_mono {u u' : U} {v v' : UValue} (hu : u ⊑ u')
    (hv : v ⊑ v') : UValue.cons u v ⊑ UValue.cons u' v' := by
  rw [UValue.le_iff_At] at hv ⊢
  intro i
  cases i with
  | zero => exact hu
  | succ i => exact hv i

theorem UValue.join_mono {v₁ v₁' v₂ v₂' : UValue} (h₁ : v₁ ⊑ v₁')
    (h₂ : v₂ ⊑ v₂') : UValue.join v₁ v₂ ⊑ UValue.join v₁' v₂' := by
  rw [UValue.le_iff_At] at h₁ h₂ ⊢
  intro i
  rw [UValue.At_join, UValue.At_join]
  exact U.join_mono (h₁ i) (h₂ i)

theorem UValue.le_rep_omega (v : UValue) : v ⊑ UValue.rep U.uω := by
  rw [UValue.le_iff_At]
  intro i
  exact U.le_omega _

/-! ## Uses transformers and their induced relations

The common shape of the paper's `Beta` relations: the left usage is bounded
by a transformed right usage, values pointwise. A transformer names the
lookups and summarised binders its induced relation is closed at and carries
the usage algebra the combinator clauses consume; the substitution
transformer (`Beta-App`) and the budget transformer (`Beta-Sel`) instantiate
it, and `UDk.transRel` packages the induced relation as a `ParametricLR`. -/

/-- A usage transformer and the algebra its induced relation needs. -/
structure UsesTransformer where
  F : Uses → Uses
  LookOk : Var → Prop
  FnOk : Var → Prop
  fn_look : ∀ {y : Var}, FnOk y → LookOk y
  mono : ∀ {φ φ' : Uses}, φ ⊑ φ' → F φ ⊑ F φ'
  refl_of : ∀ {φ : Uses}, (∀ y, ¬ LookOk y → φ !? y = U.u0) → φ ⊑ F φ
  look : ∀ {y : Var}, LookOk y → ∀ φ : Uses,
    Uses.singenv y .u1 + F φ ⊑ F (Uses.singenv y .u1 + φ)
  add_smul : ∀ (φ₁ φ₂ : Uses) (u : U), F φ₁ + u * F φ₂ ⊑ F (φ₁ + u * φ₂)
  seq : ∀ φ₁ φ₂ : Uses, F φ₁ + F φ₂ ⊑ F (φ₁ + φ₂)
  join : ∀ φ₁ φ₂ : Uses, F φ₁ ⊔ F φ₂ ⊑ F (φ₁ ⊔ φ₂)
  ext : ∀ {y : Var}, FnOk y → ∀ {φ₁ φ₂ : Uses}, φ₁ ⊑ F φ₂ →
    Uses.ext φ₁ y U.u0 ⊑ F (Uses.ext φ₂ y U.u0)
  head : ∀ {y : Var}, FnOk y → ∀ {φ₁ φ₂ : Uses}, φ₁ ⊑ F φ₂ → φ₁ !? y ⊑ φ₂ !? y

/-- The relation a transformer induces on usage traces. -/
def UD.TransR (T : UsesTransformer) (τ₁ τ₂ : UD) : Prop :=
  τ₁.uses ⊑ T.F τ₂.uses ∧ τ₁.val ⊑ τ₂.val

/-- Substitution does not shrink an environment that does not read `x`. -/
theorem Uses.le_subst_of_get_eq_zero {x : Var} (φa : Uses) {φ : Uses}
    (hφ : φ !? x = U.u0) : φ ⊑ Uses.subst φ x φa := by
  rw [Uses.le_iff_get]
  intro z
  by_cases hz : z = x
  · subst hz
    rw [hφ]
    exact U.u0_le _
  · rw [Uses.get_subst_ne _ _ hz, hφ]
    exact U.le_add_zero_mul _ _

/-- The relation is reflexive at traces reading none of the uncovered
    lookups. -/
theorem UD.transR_refl (T : UsesTransformer) {τ : UD}
    (hφ : ∀ y, ¬ T.LookOk y → τ.uses !? y = U.u0) : UD.TransR T τ τ :=
  ⟨T.refl_of hφ, UValue.le_refl _⟩

theorem UD.transR_step (T : UsesTransformer) (ev : Event)
    (hev : ∀ y, ev = .look y → T.LookOk y) {τ₁ τ₂ : UD} (hτ : UD.TransR T τ₁ τ₂) :
    UD.TransR T (UD.step ev τ₁) (UD.step ev τ₂) := by
  cases ev
  case look y =>
    refine ⟨?_, hτ.2⟩
    show Uses.singenv y .u1 + τ₁.uses ⊑ T.F (Uses.singenv y .u1 + τ₂.uses)
    exact Uses.le_trans (Uses.add_mono (Uses.le_refl _) hτ.1) (T.look (hev y rfl) _)
  all_goals exact hτ

theorem UD.transR_apply (T : UsesTransformer) {τ₁ τ₂ σ₁ σ₂ : UD}
    (hτ : UD.TransR T τ₁ τ₂) (hσ : UD.TransR T σ₁ σ₂) :
    UD.TransR T (UD.apply τ₁ σ₁) (UD.apply τ₂ σ₂) := by
  rw [UD.TransR, UD.apply_def, UD.apply_def]
  exact ⟨Uses.le_trans
    (Uses.add_mono hτ.1 (Uses.smul_mono (UValue.peel_fst_mono hτ.2) hσ.1))
    (T.add_smul _ _ _), UValue.peel_snd_mono hτ.2⟩

theorem UD.transR_join (T : UsesTransformer) {τ₁ τ₂ σ₁ σ₂ : UD}
    (hτ : UD.TransR T τ₁ τ₂) (hσ : UD.TransR T σ₁ σ₂) :
    UD.TransR T (τ₁ ⊔ σ₁) (τ₂ ⊔ σ₂) := by
  refine ⟨?_, ?_⟩
  · show τ₁.uses ⊔ σ₁.uses ⊑ T.F (τ₂.uses ⊔ σ₂.uses)
    exact Uses.le_trans (Uses.sup_mono hτ.1 hσ.1) (T.join _ _)
  · show UValue.join τ₁.val σ₁.val ⊑ UValue.join τ₂.val σ₂.val
    exact UValue.join_mono hτ.2 hσ.2

theorem UD.transR_foldl_apply (T : UsesTransformer) {ds₁ ds₂ : List UD}
    (hds : List.Forall₂ (UD.TransR T) ds₁ ds₂) :
    ∀ {acc₁ acc₂ : UD}, UD.TransR T acc₁ acc₂ →
      UD.TransR T (ds₁.foldl UD.apply acc₁) (ds₂.foldl UD.apply acc₂) := by
  induction hds with
  | nil => exact fun hacc => hacc
  | cons hd _ ih => exact fun hacc => ih (UD.transR_apply T hacc hd)

theorem UD.transR_lub (T : UsesTransformer) {l₁ l₂ : List UD}
    (hl : List.Forall₂ (UD.TransR T) l₁ l₂) :
    UD.TransR T (lub l₁) (lub l₂) := by
  induction hl with
  | nil => exact UD.transR_refl T (fun y _ => Uses.get_emp y)
  | cons h _ ih => exact UD.transR_join T h ih

/-- The induced relation on the bounded domain, through `embed`. -/
def UDk.TransR (k : Nat) (T : UsesTransformer) (d₁ d₂ : UDk k) : Prop :=
  UD.TransR T d₁.embed d₂.embed

/-! Component readings of the bounded-domain plumbing, as rewrite rules; the
`BEq`-backed order diverges when the unifier falls back to unfolding it, so
proofs rewrite instead of relying on cross-domain reducibility. -/

theorem UDk.sup_uses {k : Nat} (a b : UDk k) : (a ⊔ b).uses = a.uses ⊔ b.uses := rfl
theorem UDk.sup_val {k : Nat} (a b : UDk k) :
    (a ⊔ b).val.val = UValue.join a.val.val b.val.val := rfl
theorem UDk.bot_uses {k : Nat} : (bottom : UDk k).uses = Uses.emp := rfl
theorem UDk.bot_val {k : Nat} : (bottom : UDk k).val.val = UValue.rep U.u0 := rfl

/-- The relation, read at the components. -/
theorem UDk.transR_iff {k : Nat} {T : UsesTransformer} {d₁ d₂ : UDk k} :
    UDk.TransR k T d₁ d₂ ↔
      d₁.uses ⊑ T.F d₂.uses ∧ d₁.val.val ⊑ d₂.val.val := Iff.rfl

theorem UDk.transR_wrap {k : Nat} {T : UsesTransformer} {τ₁ τ₂ : UD}
    (h : UD.TransR T τ₁ τ₂) :
    UDk.TransR k T (UDk.wrap τ₁) (UDk.wrap τ₂) :=
  ⟨h.1, UValue.widen_mono h.2 k⟩

/-- The relation is monotone in its right argument. -/
theorem UDk.transR_up {k : Nat} {T : UsesTransformer} {d₁ d₂ d₂' : UDk k}
    (h : UDk.TransR k T d₁ d₂) (hle : d₂ ⊑ d₂') :
    UDk.TransR k T d₁ d₂' := by
  obtain ⟨hu, hv⟩ := (UDk.le_iff d₂ d₂').mp hle
  exact ⟨Uses.le_trans h.1 (T.mono hu), UValue.le_trans h.2 hv⟩

/-- The relation holds at the bottom pair of the bounded domain. -/
theorem UDk.transR_bot {k : Nat} {T : UsesTransformer} :
    UDk.TransR k T (bottom : UDk k) bottom := by
  rw [UDk.transR_iff, UDk.bot_uses, UDk.bot_val]
  exact ⟨T.refl_of (fun y _ => Uses.get_emp y), UValue.le_refl _⟩

/-- The relation is closed under joins of the bounded domain. -/
theorem UDk.transR_join {k : Nat} {T : UsesTransformer} {a₁ b₁ a₂ b₂ : UDk k}
    (h₁ : UDk.TransR k T a₁ a₂) (h₂ : UDk.TransR k T b₁ b₂) :
    UDk.TransR k T (a₁ ⊔ b₁) (a₂ ⊔ b₂) := by
  rw [UDk.transR_iff] at h₁ h₂ ⊢
  rw [UDk.sup_uses, UDk.sup_uses, UDk.sup_val, UDk.sup_val]
  exact ⟨Uses.le_trans (Uses.sup_mono h₁.1 h₂.1) (T.join _ _),
    UValue.join_mono h₁.2 h₂.2⟩

/-- Map a pointwise implication through `Forall₂` along two functions. -/
theorem forall₂_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ} {g : β → δ} (h : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.map f) (l₂.map g)
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (forall₂_map h hs)

theorem forall₂_replicate {α : Type} {R : α → α → Prop} {a : α} (h : R a a) :
    ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n a)
  | 0 => .nil
  | n + 1 => .cons h (forall₂_replicate h n)

/-- Pair every element of a list against a constant of the matching length. -/
theorem forall₂_replicate_of_mem {α β : Type} {R : α → β → Prop} {b : β} :
    ∀ {l : List α}, (∀ a ∈ l, R a b) → List.Forall₂ R l (List.replicate l.length b)
  | [], _ => .nil
  | a :: l, h => .cons (h a (List.mem_cons_self ..))
      (forall₂_replicate_of_mem (l := l) fun a' ha' =>
        h a' (List.mem_cons_of_mem _ ha'))

/-- The `bind` of the bounded instance, unfolded. -/
theorem UDk.bind_def {k : Nat} (rhs body : UDk k → UDk k) :
    AbstractDomain.bind (D := UDk k) rhs body = body (kleeneFix rhs) := rfl

/-- The clause of the induced relation for `bind`: the two Kleene ascents are
    related step by step, right-monotonicity bridging their different
    stabilization points. -/
theorem UDk.transR_bind {k : Nat} {T : UsesTransformer}
    (rhs₁ rhs₂ body₁ body₂ : Discrete (UDk k) -n> Discrete (UDk k))
    (hrhs : ∀ d₁ d₂, UDk.TransR k T d₁ d₂ → UDk.TransR k T (rhs₁ d₁) (rhs₂ d₂))
    (hbody : ∀ d₁ d₂, UDk.TransR k T d₁ d₂ → UDk.TransR k T (body₁ d₁) (body₂ d₂)) :
    UDk.TransR k T (Domain.bind rhs₁ body₁) (Domain.bind rhs₂ body₂) := by
  show UDk.TransR k T
    (AbstractDomain.bind (D := UDk k) (fun d => rhs₁ d) (fun d => body₁ d))
    (AbstractDomain.bind (D := UDk k) (fun d => rhs₂ d) (fun d => body₂ d))
  rw [UDk.bind_def, UDk.bind_def]
  exact hbody _ _ (kleeneFix_rel (a := UDk k) (R := UDk.TransR k T)
    (fun d => rhs₁ d) (fun d => rhs₂ d)
    UDk.transR_bot
    hrhs
    (fun _ _ _ _ h₁ h₂ => UDk.transR_join h₁ h₂)
    (fun _ _ _ h hle => UDk.transR_up h hle))

/-- The conditional-reflexivity premise of `ParametricOn`, discharged: an
    element fresh at every uncovered lookup is self-related. -/
theorem UDk.transR_refl_of_fresh {k : Nat} (T : UsesTransformer) {d : UDk k}
    (hf : ∀ y, ¬ T.LookOk y → Fresh (D := Discrete (UDk k)) y d) :
    UDk.TransR k T d d :=
  UD.transR_refl T (fun y hy => UDk.get_eq_zero_of_fresh (hf y hy))

/-- The induced relation is a pure relation covered at the transformer's
    guards. -/
def UDk.transRel (k : Nat) (T : UsesTransformer) : ParametricLR (Discrete (UDk k)) where
  R := UDk.TransR k T
  LookOk := T.LookOk
  FnOk := T.FnOk
  stuck := UDk.transR_wrap (UD.transR_refl T (fun y _ => Uses.get_emp y))
  step ev d₁ d₂ hev h := UDk.transR_wrap (UD.transR_step T ev hev h)
  apply d₁ d₂ a₁ a₂ hd ha := UDk.transR_wrap (UD.transR_apply T hd ha)
  con K ds₁ ds₂ hds :=
    UDk.transR_wrap (UD.transR_foldl_apply T
      (forall₂_map (S := UD.TransR T) (f := UDk.embed) (g := UDk.embed)
        (fun _ _ h => h) hds)
      (UD.transR_refl T (fun y _ => Uses.get_emp y)))
  select d₁ d₂ alts₁ alts₂ hd halts := by
    refine UDk.transR_wrap ?_
    rw [UD.TransR, UD.select_def, UD.select_def]
    have hlub : UD.TransR T
        (lub (((alts₁.map (fun p => (p.1, p.2.1, p.2.2.f))).map
          (fun p => (p.1, p.2.1, fun ds => (p.2.2 (ds.map UDk.wrap)).embed))).map
          (fun kf => kf.2.2 (UD.select.fieldProxies kf.2.1))))
        (lub (((alts₂.map (fun p => (p.1, p.2.1, p.2.2.f))).map
          (fun p => (p.1, p.2.1, fun ds => (p.2.2 (ds.map UDk.wrap)).embed))).map
          (fun kf => kf.2.2 (UD.select.fieldProxies kf.2.1)))) := by
      refine UD.transR_lub T ?_
      rw [List.map_map, List.map_map, List.map_map, List.map_map]
      refine forall₂_map (fun p₁ p₂ hp => ?_) halts
      obtain ⟨htag, harity, hbr⟩ := hp
      show UD.TransR T
        (p₁.2.2 ((UD.select.fieldProxies p₁.2.1).map UDk.wrap)).embed
        (p₂.2.2 ((UD.select.fieldProxies p₂.2.1).map UDk.wrap)).embed
      rw [harity]
      refine hbr _ _ ?_
      show List.Forall₂ (UDk.TransR k T)
        ((List.replicate p₂.2.1 (⟨Uses.emp, .rep .uω⟩ : UD)).map UDk.wrap)
        ((List.replicate p₂.2.1 (⟨Uses.emp, .rep .uω⟩ : UD)).map UDk.wrap)
      rw [List.map_replicate]
      exact forall₂_replicate
        (UDk.transR_wrap (UD.transR_refl T (fun y _ => Uses.get_emp y))) _
    exact ⟨Uses.le_trans (Uses.add_mono hd.1 hlub.1) (T.seq _ _),
      hlub.2⟩
  fn y f₁ f₂ hy hpt := by
    have hbody := hpt (UDk.wrap (UD.fn.proxy y)) (UDk.wrap (UD.fn.proxy y))
      (UDk.transR_wrap (UD.transR_refl T (fun z hz =>
        Uses.get_singenv_ne _ (fun hzy => hz (hzy ▸ T.fn_look hy)))))
    refine UDk.transR_wrap ?_
    refine ⟨?_, ?_⟩
    · show Uses.ext (f₁ (UDk.wrap (UD.fn.proxy y))).uses y U.u0
        ⊑ T.F (Uses.ext (f₂ (UDk.wrap (UD.fn.proxy y))).uses y U.u0)
      exact T.ext hy hbody.1
    · show UValue.cons ((f₁ (UDk.wrap (UD.fn.proxy y))).uses !? y)
          (f₁ (UDk.wrap (UD.fn.proxy y))).val.val
        ⊑ UValue.cons ((f₂ (UDk.wrap (UD.fn.proxy y))).uses !? y)
          (f₂ (UDk.wrap (UD.fn.proxy y))).val.val
      exact UValue.cons_mono (T.head hy hbody.1) hbody.2
  bind := UDk.transR_bind

/-- The substitution transformer: retarget the `x`-column at the argument
    usage `φa` (paper `R_{x,a}`). Closed at every lookup other than `x` and
    at every summarised binder other than `x` absent from the argument. -/
def UsesTransformer.subst (x : Var) (φa : Uses) : UsesTransformer where
  F φ := φ.subst x φa
  LookOk y := y ≠ x
  FnOk y := y ≠ x ∧ φa !? y = U.u0
  fn_look := fun {y} hy => hy.1
  mono := fun {φ φ'} h => Uses.subst_mono x φa h
  refl_of := fun {φ} h => Uses.le_subst_of_get_eq_zero φa (h x (fun hx => hx rfl))
  look := fun {y} hy φ => Uses.singenv_add_subst_le hy φ φa
  add_smul φ₁ φ₂ u := Uses.subst_add_le x φa φ₁ φ₂ u
  seq φ₁ φ₂ := Uses.subst_seq_le x φa φ₁ φ₂
  join φ₁ φ₂ := Uses.subst_join_le x φa φ₁ φ₂
  ext := fun {y} hy {φ₁ φ₂} h => Uses.ext_subst_le hy.1 φa h
  head := fun {y} hy {φ₁ φ₂} h => Uses.subst_get_of_absent φa hy.2 hy.1 h

/-- **Beta-App** at the bounded usage domain: summarising then applying
    approximates a direct call, for `f` parametric over the relations avoiding
    the binder `x` and the summarised binders `A` absent from the argument. -/
theorem UDk.apply_fn {k : Nat} (x : Var) (f : UDk k → UDk k) (a : UDk k)
    (A L : List Var) (hxA : x ∉ A) (hxL : x ∉ L)
    (hpar : ParametricOn (D := Discrete (UDk k)) A L f)
    (hA : ∀ y ∈ A, a.uses !? y = U.u0) :
    f a ⊑ AbstractDomain.apply (AbstractDomain.fn x f) a := by
  have hbase : UDk.TransR k (UsesTransformer.subst x a.uses) a
      (UDk.wrap (UD.fn.proxy x)) := by
    refine ⟨?_, ?_⟩
    · show a.uses ⊑ Uses.subst (Uses.singenv x .u1) x a.uses
      rw [Uses.le_iff_get]
      intro z
      by_cases hz : z = x
      · subst hz
        rw [Uses.get_subst_self, Uses.get_singenv_self, U.one_mul]
        exact U.le_refl _
      · rw [Uses.get_subst_ne _ _ hz, Uses.get_singenv_ne _ (Ne.symm hz),
          Uses.get_singenv_self, U.one_mul, U.zero_add]
        exact U.le_refl _
    · show a.val.val ⊑ UValue.widen k (UValue.rep U.uω)
      rw [UValue.widen_of_length_le (Nat.zero_le k)]
      exact UValue.le_rep_omega _
  have hend : UDk.TransR k (UsesTransformer.subst x a.uses) (f a)
      (f (UDk.wrap (UD.fn.proxy x))) :=
    hpar (UDk.transRel k (UsesTransformer.subst x a.uses))
      (fun y hy => ⟨fun hxy => hxA (hxy ▸ hy), hA y hy⟩)
      (fun z hz hzx => hxL (hzx ▸ hz))
      (fun _ hf => UDk.transR_refl_of_fresh _ hf)
      a (UDk.wrap (UD.fn.proxy x)) hbase
  rw [UDk.le_iff]
  constructor
  · show (f a).uses
      ⊑ Uses.ext (f (UDk.wrap (UD.fn.proxy x))).uses x U.u0
        + (peel (UValue.widen k (UValue.cons
            ((f (UDk.wrap (UD.fn.proxy x))).uses !? x)
            (f (UDk.wrap (UD.fn.proxy x))).val.val))).1 * a.uses
    refine Uses.le_trans hend.1 (Uses.add_mono (Uses.le_refl _)
      (Uses.smul_mono ?_ (Uses.le_refl _)))
    rw [UValue.peel_fst_At]
    exact (UValue.le_iff_At _ _).mp
      (UValue.le_widen k (UValue.cons
        ((f (UDk.wrap (UD.fn.proxy x))).uses !? x)
        (f (UDk.wrap (UD.fn.proxy x))).val.val)) 0
  · show (f a).val.val
      ⊑ UValue.widen k (peel (UValue.widen k (UValue.cons
          ((f (UDk.wrap (UD.fn.proxy x))).uses !? x)
          (f (UDk.wrap (UD.fn.proxy x))).val.val))).2
    refine UValue.le_trans hend.2 ?_
    refine UValue.le_trans ?_ (UValue.le_widen k _)
    rw [UValue.le_iff_At]
    intro i
    rw [UValue.peel_snd_At]
    exact (UValue.le_iff_At _ _).mp
      (UValue.le_widen k (UValue.cons
        ((f (UDk.wrap (UD.fn.proxy x))).uses !? x)
        (f (UDk.wrap (UD.fn.proxy x))).val.val)) (i + 1)

/-! ## The budget relation and `Beta-Sel`

The relation of the `Beta-Sel` proof: the left side is bounded by the right
side plus a constant budget `Ω`, instantiated at the scrutinised constructor's
usage of its fields. There is no binder column to delete, so the relation is
closed at every lookup; a summarised binder is admissible when the budget does
not read it, and the `apply` and sequencing clauses hold when the budget
absorbs `uω`-multiples. -/

theorem U.le_add_right (a b : U) : a ⊑ a + b := by cases a <;> cases b <;> decide

theorem U.le_add_omega_mul (a b : U) : a ⊑ b + U.uω * a := by
  cases a <;> cases b <;> decide

theorem U.add_comm (a b : U) : a + b = b + a := by cases a <;> cases b <;> rfl

theorem U.omega_absorb_pt (a b : U) :
    U.uω * a ⊑ a → U.uω * (a + U.uω * b) ⊑ a + U.uω * b := by
  cases a <;> cases b <;> decide

theorem U.budget_apply_pt (b d s u : U) :
    U.uω * s ⊑ s → (b + s) + u * (d + s) ⊑ (b + u * d) + s := by
  cases b <;> cases d <;> cases s <;> cases u <;> decide

theorem U.budget_seq_pt (b d s : U) :
    U.uω * s ⊑ s → (b + s) + (d + s) ⊑ (b + d) + s := by
  cases b <;> cases d <;> cases s <;> decide

theorem U.join_add_le (b d s : U) : (b + s) ⊔ (d + s) ⊑ (b ⊔ d) + s := by
  cases b <;> cases d <;> cases s <;> decide

theorem U.le_join_left (a b : U) : a ⊑ a ⊔ b := by cases a <;> cases b <;> decide

theorem U.le_join_right (a b : U) : b ⊑ a ⊔ b := by cases a <;> cases b <;> decide

theorem Uses.le_add_right (φ ψ : Uses) : φ ⊑ φ + ψ := by
  rw [Uses.le_iff_get]
  intro z
  rw [Uses.get_add]
  exact U.le_add_right _ _

theorem Uses.add_comm_le (φ ψ : Uses) : φ + ψ ⊑ ψ + φ := by
  rw [Uses.le_iff_get]
  intro z
  rw [Uses.get_add, Uses.get_add, U.add_comm]
  exact U.le_refl _

theorem Uses.le_emp_add {φ ψ : Uses} (h : φ ⊑ ψ) : φ ⊑ Uses.emp + ψ := by
  rw [Uses.le_iff_get] at h ⊢
  intro z
  rw [Uses.get_add, Uses.get_emp, U.zero_add]
  exact h z

theorem Uses.omega_smul_add_le {φ : Uses} (hφ : U.uω * φ ⊑ φ) (ψ : Uses) :
    U.uω * (φ + U.uω * ψ) ⊑ φ + U.uω * ψ := by
  rw [Uses.le_iff_get] at hφ ⊢
  intro z
  have h := hφ z
  rw [Uses.get_smul] at h
  simp only [Uses.get_smul, Uses.get_add]
  exact U.omega_absorb_pt _ _ h

theorem Uses.budget_apply_le {Ω : Uses} (hΩ : U.uω * Ω ⊑ Ω) (φ ψ : Uses) (u : U) :
    (φ + Ω) + u * (ψ + Ω) ⊑ (φ + u * ψ) + Ω := by
  rw [Uses.le_iff_get] at hΩ ⊢
  intro z
  have h := hΩ z
  rw [Uses.get_smul] at h
  simp only [Uses.get_add, Uses.get_smul]
  exact U.budget_apply_pt _ _ _ _ h

theorem Uses.budget_seq_le {Ω : Uses} (hΩ : U.uω * Ω ⊑ Ω) (φ ψ : Uses) :
    (φ + Ω) + (ψ + Ω) ⊑ (φ + ψ) + Ω := by
  rw [Uses.le_iff_get] at hΩ ⊢
  intro z
  have h := hΩ z
  rw [Uses.get_smul] at h
  simp only [Uses.get_add]
  exact U.budget_seq_pt _ _ _ h

theorem Uses.join_add_le (φ ψ Ω : Uses) : (φ + Ω) ⊔ (ψ + Ω) ⊑ (φ ⊔ ψ) + Ω := by
  rw [Uses.le_iff_get]
  intro z
  rw [Uses.get_sup, Uses.get_add, Uses.get_add, Uses.get_add, Uses.get_sup]
  exact U.join_add_le _ _ _

theorem Uses.ext_budget_le {Ω : Uses} {y : Var} (hy : Ω !? y = U.u0)
    {φ₁ φ₂ : Uses} (h : φ₁ ⊑ φ₂ + Ω) :
    Uses.ext φ₁ y U.u0 ⊑ Uses.ext φ₂ y U.u0 + Ω := by
  rw [Uses.le_iff_get] at h ⊢
  intro z
  by_cases hz : z = y
  · subst hz
    rw [Uses.get_add, Uses.get_ext_self, Uses.get_ext_self, hy]
    exact U.u0_le _
  · rw [Uses.get_ext_ne _ _ (Ne.symm hz), Uses.get_add,
      Uses.get_ext_ne _ _ (Ne.symm hz)]
    have hh := h z
    rwa [Uses.get_add] at hh

theorem Uses.budget_get_of_absent {Ω : Uses} {y : Var} (hy : Ω !? y = U.u0)
    {φ₁ φ₂ : Uses} (h : φ₁ ⊑ φ₂ + Ω) : φ₁ !? y ⊑ φ₂ !? y := by
  have hh := (Uses.le_iff_get _ _).mp h y
  rwa [Uses.get_add, hy, U.add_zero] at hh

/-! Order kit for `lub`: a member is below the least upper bound. -/

theorem Uses.le_sup_left (φ ψ : Uses) : φ ⊑ φ ⊔ ψ := by
  rw [Uses.le_iff_get]
  intro z
  rw [Uses.get_sup]
  exact U.le_join_left _ _

theorem Uses.le_sup_right (φ ψ : Uses) : ψ ⊑ φ ⊔ ψ := by
  rw [Uses.le_iff_get]
  intro z
  rw [Uses.get_sup]
  exact U.le_join_right _ _

theorem UValue.le_join_left (v w : UValue) : v ⊑ UValue.join v w := by
  rw [UValue.le_iff_At]
  intro i
  rw [UValue.At_join]
  exact U.le_join_left _ _

theorem UValue.le_join_right (v w : UValue) : w ⊑ UValue.join v w := by
  rw [UValue.le_iff_At]
  intro i
  rw [UValue.At_join]
  exact U.le_join_right _ _

theorem UD.le_trans {a b c : UD} (h₁ : a ⊑ b) (h₂ : b ⊑ c) : a ⊑ c := by
  rw [UD.le_iff] at h₁ h₂ ⊢
  exact ⟨Uses.le_trans h₁.1 h₂.1, UValue.le_trans h₁.2 h₂.2⟩

theorem UD.le_join_left (a b : UD) : a ⊑ a ⊔ b := by
  rw [UD.le_iff]
  refine ⟨?_, ?_⟩
  · show a.uses ⊑ a.uses ⊔ b.uses
    exact Uses.le_sup_left _ _
  · show a.val ⊑ UValue.join a.val b.val
    exact UValue.le_join_left _ _

theorem UD.le_join_right (a b : UD) : b ⊑ a ⊔ b := by
  rw [UD.le_iff]
  refine ⟨?_, ?_⟩
  · show b.uses ⊑ a.uses ⊔ b.uses
    exact Uses.le_sup_right _ _
  · show b.val ⊑ UValue.join a.val b.val
    exact UValue.le_join_right _ _

theorem UD.le_lub {d : UD} : ∀ {l : List UD}, d ∈ l → d ⊑ lub l
  | [], hd => nomatch hd
  | e :: l, hd => by
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact UD.le_join_left _ _
    · exact UD.le_trans (UD.le_lub hd') (UD.le_join_right _ _)

/-! The constructor's usage: `uω` times each field, folded over the fields. -/

/-- The `con` of the bounded instance, unfolded. -/
theorem UDk.con_def {k : Nat} (K : ConTag) (ds : List (UDk k)) :
    AbstractDomain.con (D := UDk k) K ds
      = UDk.wrap (UD.con K (ds.map UDk.embed)) := rfl

/-- The `select` of the bounded instance, unfolded. -/
theorem UDk.select_def {k : Nat} (d : UDk k)
    (alts : List (ConTag × Nat × (List (UDk k) → UDk k))) :
    AbstractDomain.select (D := UDk k) d alts
      = UDk.wrap (UD.select d.embed (alts.map (fun p =>
          (p.1, p.2.1, fun ds => (p.2.2 (ds.map UDk.wrap)).embed)))) := rfl

/-- `embed` after `wrap`, at the components. -/
theorem UDk.embed_wrap {k : Nat} (τ : UD) :
    (UDk.wrap (k := k) τ).embed = ⟨τ.uses, τ.val.widen k⟩ := rfl

theorem UD.foldl_apply_rep_omega : ∀ (ds : List UD) (φ : Uses),
    ds.foldl UD.apply ⟨φ, .rep .uω⟩
      = ⟨ds.foldl (fun acc d => acc + U.uω * d.uses) φ, .rep .uω⟩
  | [], _ => rfl
  | d :: ds, φ => by
    show ds.foldl UD.apply (UD.apply ⟨φ, .rep .uω⟩ d) = _
    rw [UD.apply_def]
    exact UD.foldl_apply_rep_omega ds (φ + U.uω * d.uses)

/-- The constructor's usage, unfolded. -/
theorem UD.con_def (K : ConTag) (ds : List UD) :
    UD.con K ds = ⟨ds.foldl (fun acc d => acc + U.uω * d.uses) Uses.emp, .rep .uω⟩ :=
  UD.foldl_apply_rep_omega ds Uses.emp

/-- The seed is below the constructor-usage fold. -/
theorem UD.le_seed_foldl_omega : ∀ (ds : List UD) (φ : Uses),
    φ ⊑ ds.foldl (fun acc d => acc + U.uω * d.uses) φ
  | [], φ => Uses.le_refl φ
  | d :: ds, φ => Uses.le_trans (Uses.le_add_right φ (U.uω * d.uses))
      (UD.le_seed_foldl_omega ds (φ + U.uω * d.uses))

/-- Each field's usage is below the constructor-usage fold. -/
theorem UD.le_foldl_omega {d : UD} : ∀ {ds : List UD}, d ∈ ds → ∀ (φ : Uses),
    d.uses ⊑ ds.foldl (fun acc e => acc + U.uω * e.uses) φ
  | [], hd, _ => nomatch hd
  | e :: ds, hd, φ => by
    rcases List.mem_cons.mp hd with rfl | hd'
    · refine Uses.le_trans ?_ (UD.le_seed_foldl_omega ds (φ + U.uω * d.uses))
      rw [Uses.le_iff_get]
      intro z
      rw [Uses.get_add, Uses.get_smul]
      exact U.le_add_omega_mul _ _
    · exact UD.le_foldl_omega hd' (φ + U.uω * e.uses)

/-- The constructor-usage fold absorbs `uω`-multiples. -/
theorem UD.omega_smul_foldl_le : ∀ (ds : List UD) {φ : Uses}, U.uω * φ ⊑ φ →
    U.uω * (ds.foldl (fun acc d => acc + U.uω * d.uses) φ : Uses)
      ⊑ ds.foldl (fun acc d => acc + U.uω * d.uses) φ
  | [], _, hφ => hφ
  | _ :: ds, _, hφ => UD.omega_smul_foldl_le ds (Uses.omega_smul_add_le hφ _)

/-- A variable absent from the seed and every field is absent from the
    constructor-usage fold. -/
theorem UD.get_foldl_omega_eq_zero {y : Var} : ∀ (ds : List UD) {φ : Uses},
    φ !? y = U.u0 → (∀ d ∈ ds, d.uses !? y = U.u0) →
    ds.foldl (fun acc d => acc + U.uω * d.uses) φ !? y = U.u0
  | [], _, hφ, _ => hφ
  | d :: ds, φ, hφ, hds => by
    refine UD.get_foldl_omega_eq_zero ds ?_
      (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
    rw [Uses.get_add, Uses.get_smul, hφ, hds d (List.mem_cons_self ..), U.mul_zero]
    rfl

/-- The budget transformer: add the constructor-field budget `Ω` (the
    relation of the paper's `Beta-Sel` proof). Closed at every lookup, and
    at the summarised binders the budget does not read. -/
def UsesTransformer.budget (Ω : Uses) (hΩ : U.uω * Ω ⊑ Ω) : UsesTransformer where
  F φ := φ + Ω
  LookOk _ := True
  FnOk y := Ω !? y = U.u0
  fn_look := fun {y} _ => trivial
  mono := fun {φ φ'} h => Uses.add_mono h (Uses.le_refl _)
  refl_of := fun {φ} _ => Uses.le_add_right _ _
  look := fun {y} _ φ => Uses.add_assoc_le _ _ _
  add_smul φ₁ φ₂ u := Uses.budget_apply_le hΩ φ₁ φ₂ u
  seq φ₁ φ₂ := Uses.budget_seq_le hΩ φ₁ φ₂
  join φ₁ φ₂ := Uses.join_add_le φ₁ φ₂ Ω
  ext := fun {y} hy {φ₁ φ₂} h => Uses.ext_budget_le hy h
  head := fun {y} hy {φ₁ φ₂} h => Uses.budget_get_of_absent hy h

/-- **Beta-Sel** at the bounded usage domain: summarising the constructor and
    selecting approximates a direct branch call, for `br` parametric over the
    relations whose budget covers the summarised binders `A` absent from the
    fields. -/
theorem UDk.select_con {k : Nat} (K : ConTag) (n : Nat) (br : List (UDk k) → UDk k)
    (ds : List (UDk k)) (alts : List (ConTag × Nat × (List (UDk k) → UDk k)))
    (A L : List Var)
    (hpar : ParametricAltOn (D := Discrete (UDk k)) A L br)
    (hA : ∀ y ∈ A, ∀ d ∈ ds, d.uses !? y = U.u0)
    (hmem : (K, n, br) ∈ alts) (hlen : ds.length = n) :
    br ds ⊑ AbstractDomain.select (AbstractDomain.con K ds) alts := by
  subst hlen
  have hemp : U.uω * Uses.emp ⊑ Uses.emp := by
    rw [Uses.le_iff_get]
    intro z
    rw [Uses.get_smul, Uses.get_emp, U.mul_zero]
    exact U.le_refl _
  have hΩ := UD.omega_smul_foldl_le (ds.map UDk.embed) hemp
  have hcov := fun y (hy : y ∈ A) =>
    UD.get_foldl_omega_eq_zero (ds.map UDk.embed) (Uses.get_emp y)
      (fun τ hτ => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hτ
        exact hA y hy d hd)
  have hbase : List.Forall₂
      (UDk.TransR k (UsesTransformer.budget _ hΩ))
      ds ((UD.select.fieldProxies ds.length).map UDk.wrap) := by
    show List.Forall₂ _ ds
      ((List.replicate ds.length (⟨Uses.emp, .rep .uω⟩ : UD)).map UDk.wrap)
    rw [List.map_replicate]
    refine forall₂_replicate_of_mem (fun d hd => ⟨Uses.le_emp_add
      (UD.le_foldl_omega (List.mem_map_of_mem hd) Uses.emp), ?_⟩)
    show d.val.val ⊑ UValue.widen k (UValue.rep U.uω)
    rw [UValue.widen_of_length_le (Nat.zero_le k)]
    exact UValue.le_rep_omega _
  have hend := hpar (UDk.transRel k (UsesTransformer.budget _ hΩ)) hcov
    (fun _ _ => trivial)
    (fun _ hf => UDk.transR_refl_of_fresh _ hf)
    ds ((UD.select.fieldProxies ds.length).map UDk.wrap) hbase
  have hlubmem : (br ((UD.select.fieldProxies ds.length).map UDk.wrap)).embed
      ∈ alts.map (fun p : ConTag × Nat × (List (UDk k) → UDk k) =>
          (p.2.2 ((UD.select.fieldProxies p.2.1).map UDk.wrap)).embed) :=
    List.mem_map_of_mem hmem
  have hlub := (UD.le_iff _ _).mp (UD.le_lub hlubmem)
  rw [UDk.select_def, UDk.con_def, UDk.embed_wrap, UD.con_def, UD.select_def,
    List.map_map, UDk.le_iff]
  exact ⟨Uses.le_trans hend.1 (Uses.le_trans
      (Uses.add_mono hlub.1 (Uses.le_refl _)) (Uses.add_comm_le _ _)),
    UValue.le_trans hend.2 (UValue.le_trans hlub.2 (UValue.le_widen k _))⟩

/-! ## The laws -/

theorem usageAbstractionLaws (k : Nat) : AbstractionLaws (UDk k) where
  mono_step ev {a b} h :=
    UDk.wrap_le_wrap (UD.step_mono ev (UDk.embed_mono h))
  mono_apply {d d' a a'} h₁ h₂ :=
    UDk.wrap_le_wrap (UD.apply_mono (UDk.embed_mono h₁) (UDk.embed_mono h₂))
  mono_select {d d'} alts h :=
    UDk.wrap_le_wrap (UD.select_mono _ (UDk.embed_mono h))
  step_apply ev d a := by
    cases ev
    case look y =>
      show (UDk.wrap ⟨Uses.singenv y .u1 + (UD.apply d.embed a.embed).uses,
              (UD.apply d.embed a.embed).val.widen k⟩
          ⊑ UDk.wrap (UD.apply ⟨Uses.singenv y .u1 + d.embed.uses,
              d.embed.val.widen k⟩ a.embed)) = true
      exact UDk.wrap_apply_le _ _ _
    all_goals
      show (UDk.wrap ⟨(UD.apply d.embed a.embed).uses,
              (UD.apply d.embed a.embed).val.widen k⟩
          ⊑ UDk.wrap (UD.apply ⟨d.embed.uses, d.embed.val.widen k⟩ a.embed)) = true
    all_goals exact UDk.wrap_apply_le' _ _
  step_select ev d alts := by
    cases ev
    case look y =>
      show (UDk.wrap ⟨Uses.singenv y .u1 + (UD.select d.embed _).uses,
              (UD.select d.embed _).val.widen k⟩
          ⊑ UDk.wrap (UD.select ⟨Uses.singenv y .u1 + d.embed.uses,
              d.embed.val.widen k⟩ _)) = true
      exact UDk.wrap_select_le _ _ _
    all_goals
      show (UDk.wrap ⟨(UD.select d.embed _).uses, (UD.select d.embed _).val.widen k⟩
          ⊑ UDk.wrap (UD.select ⟨d.embed.uses, d.embed.val.widen k⟩ _)) = true
    all_goals exact UDk.wrap_select_le' _ _
  stuck_apply_stuck a := UDk.stuck_le _
  stuck_apply_con K ds a := UDk.stuck_le _
  stuck_select_stuck alts := UDk.stuck_le _
  stuck_select_fn x f alts := UDk.stuck_le _
  stuck_select_con K ds alts _ := UDk.stuck_le _
  stuck_select_arity K n br ds alts _ _ := UDk.stuck_le _
  apply_fn x f a A L hxA hxL hpar _ _ hA :=
    UDk.apply_fn x f a A L hxA hxL hpar
      (fun y hy => UDk.get_eq_zero_of_fresh (hA y hy))
  select_con K n br ds alts A L hpar hA hmem hlen :=
    UDk.select_con K n br ds alts A L hpar
      (fun y hy d hd => UDk.get_eq_zero_of_fresh (hA y hy d hd)) hmem hlen
  bind_prefix rhs := by
    rw [UDk.bind_def]
    exact kleeneFix_prefix rhs
  bind_lazy rhs body := by
    rw [UDk.bind_def, UDk.bind_def]
    exact le_iff_le.mp (Std.IsPreorder.le_refl (body (kleeneFix rhs)))
  step_inc ev d := by
    have h := UDk.wrap_le_wrap (k := k) (UD.le_step ev d.embed)
    rwa [UDk.wrap_embed] at h
  update d := by
    show UDk.wrap (UD.step .update d.embed) = d
    exact UDk.wrap_embed d

end AbsDen
