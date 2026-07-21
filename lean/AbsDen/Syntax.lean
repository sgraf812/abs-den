import Iris.Algebra.OFE

/-- Simp set that evaluates a denotation to its trace: `eval` equations, the
    domain operations' one-layer `_run` rules, and the trace monad reductions.
    `simp [eval_simp]` steps a `D.unfold (eval e ρ) μ` through the trace. -/
register_simp_attr eval_simp

/-! # Syntax shared by the trace and the interpreter

`Event`, `Var`, and `Exp` mirror `AbsDen/Syntax.lean`. `Event` carries a discrete
OFE so it can sit inside the trace functor. -/

open Iris Iris.COFE OFE

namespace AbsDen

/-- The maximal length of a variable name. -/
def Var.maxLength : Nat := 8

/-- Variable names: strings of at most `Var.maxLength` characters. The finite
    name supply gives usage environments (`UsageAnalysis`) a finite height. -/
abbrev Var := {s : String // s.length ≤ Var.maxLength}

/-- Truncate a string to a variable name. Names agreeing on their first
    `Var.maxLength` characters denote the same variable. -/
instance : Coe String Var :=
  ⟨fun s => ⟨String.ofList (s.toList.take Var.maxLength), by
    simp only [String.length_ofList]
    exact List.length_take_le ..⟩⟩

instance : Inhabited Var := ⟨⟨"", by simp [Var.maxLength]⟩⟩
instance : ToString Var := ⟨fun x => x.val⟩
instance : Repr Var := ⟨fun x n => reprPrec x.val n⟩

/-- Constructor tags. The discrete OFE (every level identifies definitionally
    with equality) lets a tag index the alternatives of `Domain.select`. -/
abbrev ConTag := Nat

instance : COFE ConTag := COFE.ofDiscrete Eq Eq_Equivalence

/-- Trace events (`AbsDen/Syntax.lean`). -/
inductive Event where
  | look : Var → Event
  | update | app1 | app2 | case1 | case2 | let1
  deriving DecidableEq, Repr, Inhabited

instance : COFE Event := COFE.ofDiscrete Eq Eq_Equivalence

/-! Expressions and case alternatives (`AbsDen/Syntax.lean`). -/
mutual
inductive Exp where
  | ref    : Var → Exp
  | lam    : Var → Exp → Exp
  | app    : Exp → Var → Exp
  | «let»  : Var → Exp → Exp → Exp
  | conapp : ConTag → List Var → Exp
  | «case» : Exp → List Alt → Exp

structure Alt where
  con : ConTag
  vars : List Var
  rhs : Exp
end

instance : Inhabited Exp := ⟨.conapp 0 []⟩

/-- An alternative's right-hand side is smaller than the alternative. -/
theorem alt_rhs_lt_self (a : Alt) : sizeOf a.rhs < sizeOf a := by
  cases a; simp [Alt.mk.sizeOf_spec]; omega

/-- An alternative's right-hand side is smaller than the `case` enclosing it
    (the termination measure for the recursions over `Exp`). Threaded through a
    `{x // x ∈ alts}` so the membership survives the term duplication that
    `ne_solve` performs on the closure under `case2`. -/
theorem alt_rhs_lt {eₛ : Exp} {alts : List Alt} (s : {x // x ∈ alts}) :
    sizeOf s.val.rhs < 1 + sizeOf eₛ + sizeOf alts := by
  have h2 := alt_rhs_lt_self s.val
  have h1 := List.sizeOf_lt_of_mem s.2
  omega

/-- All binder occurrences of an expression: every `lam` binder, `let` binder,
    and `case` field binder, in syntactic order, duplicates kept. -/
def Exp.bv : Exp → List Var
  | .ref _ => []
  | .lam x e => x :: e.bv
  | .app e _ => e.bv
  | .«let» x e₁ e₂ => x :: (e₁.bv ++ e₂.bv)
  | .conapp _ _ => []
  | .«case» eₛ alts => eₛ.bv ++ alts.attach.flatMap (fun alt => alt.1.vars ++ alt.1.rhs.bv)
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- The lambda binders of an expression, in syntactic order, duplicates kept:
    the binders summarised by `Domain.fn`. -/
def Exp.lamBV : Exp → List Var
  | .ref _ => []
  | .lam x e => x :: e.lamBV
  | .app e _ => e.lamBV
  | .«let» _ e₁ e₂ => e₁.lamBV ++ e₂.lamBV
  | .conapp _ _ => []
  | .«case» eₛ alts => eₛ.lamBV ++ alts.attach.flatMap (fun alt => alt.1.rhs.lamBV)
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- The let binders of an expression, in syntactic order, duplicates kept: the
    binders whose lookups `eval` records with `Domain.step`. -/
def Exp.letBV : Exp → List Var
  | .ref _ => []
  | .lam _ e => e.letBV
  | .app e _ => e.letBV
  | .«let» x e₁ e₂ => x :: (e₁.letBV ++ e₂.letBV)
  | .conapp _ _ => []
  | .«case» eₛ alts => eₛ.letBV ++ alts.attach.flatMap (fun alt => alt.1.rhs.letBV)
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- The free variables of an expression: every variable occurrence not captured
    by an enclosing binder, duplicates kept. -/
def Exp.fv : Exp → List Var
  | .ref x => [x]
  | .lam x e => e.fv.filter (· ≠ x)
  | .app e x => x :: e.fv
  | .«let» x e₁ e₂ => (e₁.fv ++ e₂.fv).filter (· ≠ x)
  | .conapp _ xs => xs
  | .«case» eₛ alts =>
      eₛ.fv ++ alts.attach.flatMap (fun alt => alt.1.rhs.fv.filter (· ∉ alt.1.vars))
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- The Barendregt convention: all binders are distinct from each other and
    from the free variables. Input programs to the soundness theorems satisfy
    it; the fundamental lemma consumes it as scoping side conditions. -/
def Barendregt (e : Exp) : Prop := e.bv.Nodup ∧ ∀ x ∈ e.bv, x ∉ e.fv

/-! ## The scoping discipline

`Exp.Scoped L e` relativizes the Barendregt convention to a let universe `L`:
binders are pairwise distinct, lambda binders avoid `L`, and let binders lie
within it. The fundamental lemma threads it through subterms by the inversion
lemmas; a Barendregt program is scoped under its own let binders. -/

/-- A member of one chunk of a duplicate-free flat map determines its chunk. -/
theorem nodup_flatMap_eq_of_mem {α β : Type} {f : α → List β} {y : β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
      y ∈ f a → y ∈ f b → a = b
  | c :: l, h, a, b, ha, hb, hya, hyb => by
    rw [List.flatMap_cons, List.nodup_append] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (h.2.2 y hya y (List.mem_flatMap.mpr ⟨b, hb', hyb⟩) rfl).elim
    · exact (h.2.2 y hyb y (List.mem_flatMap.mpr ⟨a, ha', hya⟩) rfl).elim
    · exact nodup_flatMap_eq_of_mem h.2.1 ha' hb' hya hyb

/-- A chunk of a duplicate-free flat map is duplicate-free. -/
theorem nodup_of_mem_flatMap {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {a : α}, a ∈ l → (f a).Nodup
  | c :: l, h, a, ha => by
    rw [List.flatMap_cons, List.nodup_append] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact nodup_of_mem_flatMap h.2.1 ha'

/-- Every lambda binder is a binder. -/
theorem Exp.lamBV_subset_bv : ∀ (e : Exp), ∀ y ∈ e.lamBV, y ∈ e.bv
  | .ref _ => by simp [Exp.lamBV]
  | .lam x e => by
    intro y hy
    simp only [Exp.lamBV, List.mem_cons] at hy
    simp only [Exp.bv, List.mem_cons]
    rcases hy with rfl | hy
    · exact .inl rfl
    · exact .inr (Exp.lamBV_subset_bv e y hy)
  | .app e _ => by
    intro y hy
    simp only [Exp.lamBV] at hy
    simp only [Exp.bv]
    exact Exp.lamBV_subset_bv e y hy
  | .«let» x e₁ e₂ => by
    intro y hy
    simp only [Exp.lamBV, List.mem_append] at hy
    simp only [Exp.bv, List.mem_cons, List.mem_append]
    rcases hy with hy | hy
    · exact .inr (.inl (Exp.lamBV_subset_bv e₁ y hy))
    · exact .inr (.inr (Exp.lamBV_subset_bv e₂ y hy))
  | .conapp _ _ => by simp [Exp.lamBV]
  | .«case» eₛ alts => by
    intro y hy
    simp only [Exp.lamBV, List.mem_append, List.mem_flatMap] at hy
    simp only [Exp.bv, List.mem_append, List.mem_flatMap]
    rcases hy with hy | ⟨alt, halt, hy⟩
    · exact .inl (Exp.lamBV_subset_bv eₛ y hy)
    · exact .inr ⟨alt, halt, .inr (Exp.lamBV_subset_bv alt.1.rhs y hy)⟩
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- Every let binder is a binder. -/
theorem Exp.letBV_subset_bv : ∀ (e : Exp), ∀ y ∈ e.letBV, y ∈ e.bv
  | .ref _ => by simp [Exp.letBV]
  | .lam x e => by
    intro y hy
    simp only [Exp.letBV] at hy
    simp only [Exp.bv, List.mem_cons]
    exact .inr (Exp.letBV_subset_bv e y hy)
  | .app e _ => by
    intro y hy
    simp only [Exp.letBV] at hy
    simp only [Exp.bv]
    exact Exp.letBV_subset_bv e y hy
  | .«let» x e₁ e₂ => by
    intro y hy
    simp only [Exp.letBV, List.mem_cons, List.mem_append] at hy
    simp only [Exp.bv, List.mem_cons, List.mem_append]
    rcases hy with rfl | hy | hy
    · exact .inl rfl
    · exact .inr (.inl (Exp.letBV_subset_bv e₁ y hy))
    · exact .inr (.inr (Exp.letBV_subset_bv e₂ y hy))
  | .conapp _ _ => by simp [Exp.letBV]
  | .«case» eₛ alts => by
    intro y hy
    simp only [Exp.letBV, List.mem_append, List.mem_flatMap] at hy
    simp only [Exp.bv, List.mem_append, List.mem_flatMap]
    rcases hy with hy | ⟨alt, halt, hy⟩
    · exact .inl (Exp.letBV_subset_bv eₛ y hy)
    · exact .inr ⟨alt, halt, .inr (Exp.letBV_subset_bv alt.1.rhs y hy)⟩
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- With pairwise distinct binders, no variable is both lambda-bound and
    let-bound. -/
theorem Exp.nodup_lam_notin_letBV : ∀ (e : Exp), e.bv.Nodup →
    ∀ y ∈ e.lamBV, y ∉ e.letBV
  | .ref _, _ => by simp [Exp.lamBV]
  | .lam x e, h => by
    simp only [Exp.bv, List.nodup_cons] at h
    intro y hy hy'
    simp only [Exp.lamBV, List.mem_cons] at hy
    simp only [Exp.letBV] at hy'
    rcases hy with rfl | hy
    · exact h.1 (Exp.letBV_subset_bv e y hy')
    · exact Exp.nodup_lam_notin_letBV e h.2 y hy hy'
  | .app e _, h => by
    simp only [Exp.bv] at h
    intro y hy hy'
    simp only [Exp.lamBV] at hy
    simp only [Exp.letBV] at hy'
    exact Exp.nodup_lam_notin_letBV e h y hy hy'
  | .«let» x e₁ e₂, h => by
    simp only [Exp.bv, List.nodup_cons, List.nodup_append] at h
    intro y hy hy'
    simp only [Exp.lamBV, List.mem_append] at hy
    simp only [Exp.letBV, List.mem_cons, List.mem_append] at hy'
    have hybv : y ∈ e₁.bv ∨ y ∈ e₂.bv :=
      hy.imp (Exp.lamBV_subset_bv e₁ y) (Exp.lamBV_subset_bv e₂ y)
    rcases hy' with rfl | hy' | hy'
    · exact h.1 (List.mem_append.mpr hybv)
    · rcases hy with hy | hy
      · exact Exp.nodup_lam_notin_letBV e₁ h.2.1 y hy hy'
      · exact h.2.2.2 y (Exp.letBV_subset_bv e₁ y hy') y (Exp.lamBV_subset_bv e₂ y hy) rfl
    · rcases hy with hy | hy
      · exact h.2.2.2 y (Exp.lamBV_subset_bv e₁ y hy) y (Exp.letBV_subset_bv e₂ y hy') rfl
      · exact Exp.nodup_lam_notin_letBV e₂ h.2.2.1 y hy hy'
  | .conapp _ _, _ => by simp [Exp.lamBV]
  | .«case» eₛ alts, h => by
    simp only [Exp.bv, List.nodup_append] at h
    intro y hy hy'
    simp only [Exp.lamBV, List.mem_append, List.mem_flatMap] at hy
    simp only [Exp.letBV, List.mem_append, List.mem_flatMap] at hy'
    rcases hy with hy | ⟨alt, halt, hy⟩ <;> rcases hy' with hy' | ⟨alt', halt', hy'⟩
    · exact Exp.nodup_lam_notin_letBV eₛ h.1 y hy hy'
    · exact h.2.2 y (Exp.lamBV_subset_bv eₛ y hy) y (List.mem_flatMap.mpr
        ⟨alt', halt', List.mem_append_right _ (Exp.letBV_subset_bv alt'.1.rhs y hy')⟩) rfl
    · exact h.2.2 y (Exp.letBV_subset_bv eₛ y hy') y (List.mem_flatMap.mpr
        ⟨alt, halt, List.mem_append_right _ (Exp.lamBV_subset_bv alt.1.rhs y hy)⟩) rfl
    · have heq : alt = alt' := nodup_flatMap_eq_of_mem h.2.1 halt halt'
        (List.mem_append_right _ (Exp.lamBV_subset_bv alt.1.rhs y hy))
        (List.mem_append_right _ (Exp.letBV_subset_bv alt'.1.rhs y hy'))
      subst heq
      have hn : (alt.1.vars ++ alt.1.rhs.bv).Nodup := nodup_of_mem_flatMap h.2.1 halt
      rw [List.nodup_append] at hn
      exact Exp.nodup_lam_notin_letBV alt.1.rhs hn.2.1 y hy hy'
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- The scoping discipline relative to the let universe `L`. -/
structure Exp.Scoped (L : List Var) (e : Exp) : Prop where
  nodup : e.bv.Nodup
  lam_notin : ∀ y ∈ e.lamBV, y ∉ L
  let_mem : ∀ y ∈ e.letBV, y ∈ L

/-- A Barendregt program is scoped under its own let binders. -/
theorem Barendregt.scoped {e : Exp} (h : Barendregt e) : e.Scoped e.letBV :=
  ⟨h.1, Exp.nodup_lam_notin_letBV e h.1, fun _ hy => hy⟩

theorem Exp.Scoped.lam_inv {L : List Var} {x : Var} {body : Exp}
    (h : Exp.Scoped L (.lam x body)) :
    body.Scoped L ∧ x ∉ body.lamBV ∧ x ∉ L := by
  have hn := h.nodup
  simp only [Exp.bv, List.nodup_cons] at hn
  have hlam : ∀ y ∈ body.lamBV, y ∉ L := fun y hy =>
    h.lam_notin y (by simp only [Exp.lamBV, List.mem_cons]; exact .inr hy)
  have hlet : ∀ y ∈ body.letBV, y ∈ L := fun y hy =>
    h.let_mem y (by simpa only [Exp.letBV] using hy)
  exact ⟨⟨hn.2, hlam, hlet⟩,
    fun hx => hn.1 (Exp.lamBV_subset_bv body x hx),
    h.lam_notin x (by simp only [Exp.lamBV]; exact List.mem_cons_self ..)⟩

theorem Exp.Scoped.app_inv {L : List Var} {e : Exp} {x : Var}
    (h : Exp.Scoped L (.app e x)) : e.Scoped L := by
  have hn := h.nodup
  simp only [Exp.bv] at hn
  exact ⟨hn,
    fun y hy => h.lam_notin y (by simpa only [Exp.lamBV] using hy),
    fun y hy => h.let_mem y (by simpa only [Exp.letBV] using hy)⟩

theorem Exp.Scoped.let_inv {L : List Var} {x : Var} {e₁ e₂ : Exp}
    (h : Exp.Scoped L (.«let» x e₁ e₂)) :
    e₁.Scoped L ∧ e₂.Scoped L ∧ x ∈ L := by
  have hn := h.nodup
  simp only [Exp.bv, List.nodup_cons, List.nodup_append] at hn
  refine ⟨⟨hn.2.1, ?_, ?_⟩, ⟨hn.2.2.1, ?_, ?_⟩, ?_⟩
  · exact fun y hy => h.lam_notin y
      (by simp only [Exp.lamBV, List.mem_append]; exact .inl hy)
  · exact fun y hy => h.let_mem y
      (by simp only [Exp.letBV, List.mem_cons, List.mem_append]; exact .inr (.inl hy))
  · exact fun y hy => h.lam_notin y
      (by simp only [Exp.lamBV, List.mem_append]; exact .inr hy)
  · exact fun y hy => h.let_mem y
      (by simp only [Exp.letBV, List.mem_cons, List.mem_append]; exact .inr (.inr hy))
  · exact h.let_mem x (by simp only [Exp.letBV]; exact List.mem_cons_self ..)

theorem Exp.Scoped.case_inv {L : List Var} {eₛ : Exp} {alts : List Alt}
    (h : Exp.Scoped L (.«case» eₛ alts)) :
    eₛ.Scoped L ∧ ∀ alt ∈ alts.attach, alt.1.rhs.Scoped L := by
  have hn := h.nodup
  simp only [Exp.bv, List.nodup_append] at hn
  refine ⟨⟨hn.1, ?_, ?_⟩, fun alt halt => ⟨?_, ?_, ?_⟩⟩
  · exact fun y hy => h.lam_notin y
      (by simp only [Exp.lamBV, List.mem_append]; exact .inl hy)
  · exact fun y hy => h.let_mem y
      (by simp only [Exp.letBV, List.mem_append]; exact .inl hy)
  · have := nodup_of_mem_flatMap hn.2.1 halt
    rw [List.nodup_append] at this
    exact this.2.1
  · exact fun y hy => h.lam_notin y
      (by simp only [Exp.lamBV, List.mem_append]
          exact .inr (List.mem_flatMap.mpr ⟨alt, halt, hy⟩))
  · exact fun y hy => h.let_mem y
      (by simp only [Exp.letBV, List.mem_append]
          exact .inr (List.mem_flatMap.mpr ⟨alt, halt, hy⟩))

end AbsDen
