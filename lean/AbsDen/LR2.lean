import AbsDen.LR
import AbsDen.ParametricLR

/-! # A binary logical relation on two semantic domains

The generalization of `AbsDen.LR` from one domain to two. Where `LR`
carries a unary predicate `P : D -n> SProp` and proves `env ρ ⊢ P (eval e ρ)`,
`LR2` carries a relation `R : D₁ -n> D₂ -n> SProp` between two domains and
proves `env ρ₁ ρ₂ ⊢ R (eval e ρ₁) (eval e ρ₂)`: the *same* syntactic program
run through two `Domain` instances yields `R`-related denotations, provided the
two environments are related pointwise. `LR` is the degenerate case where the
two domains coincide and `R` ignores its second argument.

The relation is indexed by the let universe `L` of the program under scrutiny.
Every `D₂`-side value the relation stores is fresh outside `L`, and the
value-introducing fields receive the parametricity and freshness of the
`D₂`-side closures they summarise, established from the scoping discipline
`Exp.Scoped L` and the freshness of the environment entries.

The fundamental lemma is one structural recursion over the expression,
discharging each `eval` clause by the corresponding closure field of the
relation. The relation-specific content, the paper's abstraction laws, lives in
those fields and is supplied per instance. -/

open Iris Iris.BI Iris.BI.BigAndL Iris.COFE OFE

namespace AbsDen

variable {SProp : Type} [Sbi SProp]
variable {D₁ D₂ : Type} [OFE D₁] [Domain D₁] [OFE D₂] [Domain D₂]

/-! ## Relating options and look-shaped values -/

namespace LR2

/-- Relate two options in lockstep: both absent, or both present and related. -/
def OptRel {A B : Type} (Rel : A → B → SProp) : Option A → Option B → SProp
  | none, none => iprop(True)
  | some a, some b => Rel a b
  | none, some _ => iprop(False)
  | some _, none => iprop(False)

@[simp] theorem OptRel_none_none {A B} (Rel : A → B → SProp) :
    OptRel Rel (none : Option A) (none : Option B) = iprop(True) := rfl
@[simp] theorem OptRel_some_some {A B} (Rel : A → B → SProp) (a : A) (b : B) :
    OptRel Rel (some a) (some b) = Rel a b := rfl
@[simp] theorem OptRel_none_some {A B} (Rel : A → B → SProp) (b : B) :
    OptRel Rel (none : Option A) (some b) = iprop(False) := rfl
@[simp] theorem OptRel_some_none {A B} (Rel : A → B → SProp) (a : A) :
    OptRel Rel (some a) (none : Option B) = iprop(False) := rfl

end LR2

/-- Two values related by `R`, each look-shaped, the `D₂` side fresh outside
    the let universe `L`. Mirrors `IsLookup`; look-shape is what a
    `let`-binding produces and the closure fields may consume. -/
def IsLookupR (L : List Var) (R : D₁ -n> D₂ -n> SProp) (a₁ : D₁) (a₂ : D₂) : SProp :=
  iprop(R a₁ a₂ ∧ IsLookShape a₁ ∧ IsLookShape a₂ ∧ ⌜∀ y, y ∉ L → Fresh y a₂⌝)

/-- Forgetting the shapes recovers the underlying relation. -/
theorem IsLookupR_to_R (L : List Var) (R : D₁ -n> D₂ -n> SProp) (a₁ : D₁) (a₂ : D₂) :
    IsLookupR L R a₁ a₂ ⊢ R a₁ a₂ := by
  simp only [IsLookupR]; exact and_elim_l

/-- The freshness a related pair carries on its abstract side. -/
theorem IsLookupR_fresh (L : List Var) (R : D₁ -n> D₂ -n> SProp) (a₁ : D₁) (a₂ : D₂) :
    IsLookupR L R a₁ a₂ ⊢ (⌜∀ y, y ∉ L → Fresh y a₂⌝ : SProp) := by
  simp only [IsLookupR]; exact and_elim_r.trans (and_elim_r.trans and_elim_r)

/-- Package boxed related look-wrappings into a boxed `IsLookupR`: the shapes
    and the freshness are emp-valid, hence intuitionistic. -/
theorem IsLookupR_look_intro_box [BIAffine SProp] {L : List Var} {X : SProp}
    {R : D₁ -n> D₂ -n> SProp} {x : Var} {a₁ : D₁} {a₂ : D₂}
    (hfresh : ∀ y, y ∉ L → Fresh y (Domain.step (.look x) a₂))
    (h : X ⊢ iprop(□ R (Domain.step (.look x) a₁) (Domain.step (.look x) a₂))) :
    X ⊢ iprop(□ IsLookupR L R (Domain.step (.look x) a₁) (Domain.step (.look x) a₂)) := by
  simp only [IsLookupR]
  refine .trans ?_ intuitionistically_and.2
  refine and_intro h (.trans ?_ intuitionistically_and.2)
  refine and_intro (LR.of_empValid_box (LR.IsLookShape_intro x a₁))
    (.trans ?_ intuitionistically_and.2)
  exact and_intro (LR.of_empValid_box (LR.IsLookShape_intro x a₂))
    (LR.of_empValid_box (pure_intro hfresh))

/-! ## Per-case closure conditions (binary) -/

namespace Parametric

/-- Related functions send related lookup inputs, received boxed, to related
    outputs. -/
def FnR (L : List Var) (R : D₁ -n> D₂ -n> SProp) (f₁ : D₁ -n> D₁) (f₂ : D₂ -n> D₂) : SProp :=
  iprop(∀ a₁ a₂, □ IsLookupR L R a₁ a₂ → R (f₁ a₁) (f₂ a₂))

/-- Field-lists related pointwise, each pair boxed: constructor fields are
    stored in the value and may be consumed any time later. -/
def ConR (L : List Var) (R : D₁ -n> D₂ -n> SProp) : List D₁ → List D₂ → SProp
  | [], [] => iprop(True)
  | a₁ :: as₁, a₂ :: as₂ => iprop(□ IsLookupR L R a₁ a₂ ∧ ConR L R as₁ as₂)
  | [], _ :: _ => iprop(False)
  | _ :: _, [] => iprop(False)

theorem ConR_nil (L : List Var) (R : D₁ -n> D₂ -n> SProp) :
    ConR L R ([] : List D₁) ([] : List D₂) = iprop(True) := rfl

theorem ConR_cons (L : List Var) (R : D₁ -n> D₂ -n> SProp) (a₁ : D₁) (as₁ : List D₁) (a₂ : D₂)
    (as₂ : List D₂) :
    ConR L R (a₁ :: as₁) (a₂ :: as₂) = iprop(□ IsLookupR L R a₁ a₂ ∧ ConR L R as₁ as₂) := rfl

/-- `ConR` is persistent: pure at mismatched shapes, boxed pairs elsewhere. -/
instance ConR_persistent (L : List Var) (R : D₁ -n> D₂ -n> SProp) :
    ∀ (ds₁ : List D₁) (ds₂ : List D₂), Persistent (ConR L R ds₁ ds₂)
  | [], [] => inferInstanceAs (Persistent iprop(⌜True⌝))
  | _ :: _, [] => inferInstanceAs (Persistent iprop(⌜False⌝))
  | [], _ :: _ => inferInstanceAs (Persistent iprop(⌜False⌝))
  | a₁ :: as₁, a₂ :: as₂ =>
    have := ConR_persistent L R as₁ as₂
    inferInstanceAs (Persistent iprop(□ IsLookupR L R a₁ a₂ ∧ ConR L R as₁ as₂))

/-- The freshness a related field-list carries on its abstract side. -/
theorem ConR_fresh (L : List Var) (R : D₁ -n> D₂ -n> SProp) :
    ∀ (ds₁ : List D₁) (ds₂ : List D₂),
      ConR L R ds₁ ds₂ ⊢ (⌜∀ d ∈ ds₂, ∀ y, y ∉ L → Fresh y d⌝ : SProp)
  | [], [] => pure_intro (fun d hd => absurd hd (List.not_mem_nil))
  | [], _ :: _ => by rw [ConR]; exact false_elim
  | _ :: _, [] => by rw [ConR]; exact false_elim
  | a₁ :: as₁, a₂ :: as₂ => by
    rw [ConR_cons]
    refine .trans (and_mono
      (intuitionistically_elim.trans (IsLookupR_fresh L R a₁ a₂))
      (ConR_fresh L R as₁ as₂)) ?_
    refine pure_and.1.trans (pure_mono ?_)
    rintro ⟨h₁, h₂⟩ d hd
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact h₁
    · exact h₂ d hd'

/-- Alternatives related: equal length, paired by position with matching tags
    and arities, each branch sending related field-lists to related results. The
    length equality makes the two tag lists correspond, so a constructor absent
    from one side is absent from the other. -/
def AltsR (L : List Var) (R : D₁ -n> D₂ -n> SProp)
    (alts₁ : List (ConTag × Nat × (List D₁ -n> D₁)))
    (alts₂ : List (ConTag × Nat × (List D₂ -n> D₂))) : SProp :=
  iprop(⌜alts₁.length = alts₂.length⌝ ∧
    [∧list] p ∈ alts₁.zip alts₂,
      iprop(⌜p.1.1 = p.2.1 ∧ p.1.2.1 = p.2.2.1⌝ ∧
        ∀ ds₁ ds₂, ConR L R ds₁ ds₂ → R (p.1.2.2 ds₁) (p.2.2.2 ds₂)))

/-- The pure content of `AltsR`: the lists have equal length and pair up with
    matching tags and arities. -/
theorem AltsR_pure (L : List Var) (R : D₁ -n> D₂ -n> SProp)
    (alts₁ : List (ConTag × Nat × (List D₁ -n> D₁)))
    (alts₂ : List (ConTag × Nat × (List D₂ -n> D₂))) :
    AltsR L R alts₁ alts₂ ⊢
      (⌜alts₁.length = alts₂.length ∧
        ∀ p ∈ alts₁.zip alts₂, p.1.1 = p.2.1 ∧ p.1.2.1 = p.2.2.1⌝ : SProp) := by
  refine .trans (and_mono .rfl
    ((bigAndL_mono_of_forall fun _ _ => and_elim_l).trans bigAndL_pure_intro)) ?_
  refine pure_and.1.trans (pure_mono ?_)
  rintro ⟨hlen, hall⟩
  refine ⟨hlen, fun p hp => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k _ (List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩)

/-- Zipping two equal-length maps of a shared list pairs the images. -/
theorem zip_map_map {X A B : Type} (l : List X) (f : X → A) (g : X → B) :
    (l.map f).zip (l.map g) = l.map (fun x => (f x, g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

end Parametric

/-! ## The binary logical relation -/

/-- A binary logical relation between the semantic domains `D₁` and `D₂`,
    indexed by the let universe `L`. `R` is the defining relation; `IsThunk` is
    what `bind`'s `rhs`/`body` receive on related inputs, fresh outside
    `L` on the abstract side. Each closure field mirrors one `eval` clause,
    relating the two domains' operations; the value-introducing fields receive
    the parametricity and freshness of the `D₂`-side closures, which the
    fundamental lemma establishes from the scoping discipline.

    Hypotheses that outlive the current trace layer arrive boxed: what a value
    stores (`fn`'s clause, `bind`'s rhs clause backing the heap entry)
    and what rides along a scrutinee's trace (`apply`'s argument,
    `select`'s alternatives). At an all-persistent `SProp` such as
    `SiProp` the boxes are invisible. -/
structure LR2 (SProp : Type) (D₁ D₂ : Type) (L : List Var) [Sbi SProp]
    [OFE D₁] [Domain D₁] [OFE D₂] [Domain D₂] where
  R            : D₁ -n> D₂ -n> SProp
  IsThunk      : D₁ -n> D₂ -n> SProp
  IsThunk_to_R : ∀ (x : Var) (a₁ : D₁) (a₂ : D₂),
    IsThunk a₁ a₂ ⊢ R (Domain.step (.look x) a₁) (Domain.step (.look x) a₂)
  IsThunk_fresh : ∀ (a₁ : D₁) (a₂ : D₂),
    IsThunk a₁ a₂ ⊢ (⌜∀ y, y ∉ L → Fresh y a₂⌝ : SProp)
  stuck        : ⊢ R Domain.stuck Domain.stuck
  fn           : ∀ (x : Var) (f₁ : D₁ -n> D₁) (f₂ : D₂ -n> D₂) (A : List Var),
    x ∉ A → x ∉ L → (∀ y ∈ A, y ∉ L) →
    ParametricOn A L (fun a => Domain.step .app2 (f₂ a)) →
    FreshFn x (fun a => Domain.step .app2 (f₂ a)) →
    iprop(□ Parametric.FnR L R f₁ f₂) ⊢
      R (Domain.fn x ((Domain.step .app2).comp f₁)) (Domain.fn x ((Domain.step .app2).comp f₂))
  con          : ∀ (K : ConTag) (ds₁ : List D₁) (ds₂ : List D₂),
    Parametric.ConR L R ds₁ ds₂ ⊢ R (Domain.con K ds₁) (Domain.con K ds₂)
  apply   : ∀ (dv₁ da₁ : D₁) (dv₂ da₂ : D₂),
    iprop(R dv₁ dv₂ ∧ □ IsLookupR L R da₁ da₂) ⊢
      R (Domain.step .app1 (Domain.apply dv₁ da₁)) (Domain.step .app1 (Domain.apply dv₂ da₂))
  select  : ∀ (dv₁ : D₁) (dv₂ : D₂)
      (alts₁ : List (ConTag × Nat × (List D₁ -n> D₁)))
      (alts₂ : List (ConTag × Nat × (List D₂ -n> D₂))),
    (∀ p ∈ Parametric.stepAlts alts₂, ∃ A, (∀ y ∈ A, y ∉ L) ∧
      ParametricAltOn A L (fun ds => p.2.2 ds)) →
    iprop(R dv₁ dv₂ ∧ □ Parametric.AltsR L R alts₁ alts₂) ⊢
      R (Domain.step .case1 (Domain.select dv₁ (Parametric.stepAlts alts₁)))
        (Domain.step .case1 (Domain.select dv₂ (Parametric.stepAlts alts₂)))
  bind  : ∀ (rhs₁ body₁ : D₁ -n> D₁) (rhs₂ body₂ : D₂ -n> D₂),
    (∀ y, y ∉ L → FreshFn y (fun a => rhs₂ a)) →
    iprop((□ ∀ a₁ a₂, □ IsThunk a₁ a₂ → R (rhs₁ a₁) (rhs₂ a₂)) ∧
          (∀ a₁ a₂, □ IsThunk a₁ a₂ → R (body₁ a₁) (body₂ a₂)))
      ⊢ R (Domain.step .let1 (Domain.bind rhs₁ body₁)) (Domain.step .let1 (Domain.bind rhs₂ body₂))

namespace LR2

variable {SProp : Type} [Sbi SProp]
variable {D₁ D₂ : Type} [OFE D₁] [Domain D₁] [OFE D₂] [Domain D₂]
variable {L : List Var}

/-! ## Env-level closure -/

/-- Two environments are related when they are in lockstep at every variable and
    the bound entries are boxed `IsLookupR L lr.R`, making the whole env
    persistent. -/
def EnvOk (lr : LR2 SProp D₁ D₂ L) (ρ₁ : Env D₁) (ρ₂ : Env D₂) : SProp :=
  iprop(∀ (x : Var),
    OptRel (fun a₁ a₂ => iprop(□ IsLookupR L lr.R a₁ a₂)) (ρ₁.get x) (ρ₂.get x))

instance OptRel_persistent {A B : Type} {Rel : A → B → SProp} [∀ a b, Persistent (Rel a b)] :
    ∀ (o₁ : Option A) (o₂ : Option B), Persistent (OptRel Rel o₁ o₂)
  | none, none => inferInstanceAs (Persistent iprop(⌜True⌝))
  | some a, some b => inferInstanceAs (Persistent (Rel a b))
  | none, some _ => inferInstanceAs (Persistent iprop(⌜False⌝))
  | some _, none => inferInstanceAs (Persistent iprop(⌜False⌝))

instance envOk_persistent [BIPersistentlyForall SProp] (lr : LR2 SProp D₁ D₂ L)
    (ρ₁ : Env D₁) (ρ₂ : Env D₂) : Persistent (lr.EnvOk ρ₁ ρ₂) :=
  inferInstanceAs (Persistent (iprop(∀ (x : Var),
    OptRel (fun a₁ a₂ => iprop(□ IsLookupR L lr.R a₁ a₂)) (ρ₁.get x) (ρ₂.get x)) : SProp))

/-- Box a consequence of a related env. -/
theorem envOk_box [BIAffine SProp] [BIPersistentlyForall SProp] {lr : LR2 SProp D₁ D₂ L}
    {ρ₁ : Env D₁} {ρ₂ : Env D₂} {X : SProp} (h : lr.EnvOk ρ₁ ρ₂ ⊢ X) :
    lr.EnvOk ρ₁ ρ₂ ⊢ iprop(□ X) :=
  intuitionistic_alias.trans (intuitionistically_mono h)

/-- The empty environments are related. -/
theorem envOk_empty (lr : LR2 SProp D₁ D₂ L) : ⊢ lr.EnvOk (Env.empty : Env D₁) (Env.empty : Env D₂) := by
  simp only [EnvOk]
  refine forall_intro fun x => ?_
  simp only [Env.get, Env.empty, OptRel_none_none]
  exact true_intro

/-- A bound pair of a related env is a boxed `IsLookupR L lr.R`. -/
theorem envOk_get (lr : LR2 SProp D₁ D₂ L) {ρ₁ : Env D₁} {ρ₂ : Env D₂} {x : Var} {a₁ : D₁}
    {a₂ : D₂} (h₁ : ρ₁.get x = some a₁) (h₂ : ρ₂.get x = some a₂) :
    lr.EnvOk ρ₁ ρ₂ ⊢ iprop(□ IsLookupR L lr.R a₁ a₂) := by
  simp only [EnvOk]
  refine (forall_elim x).trans ?_
  rw [h₁, h₂, OptRel_some_some]; exact .rfl

/-- A variable present on one side only cannot occur in a related env. -/
theorem envOk_none_some (lr : LR2 SProp D₁ D₂ L) {ρ₁ : Env D₁} {ρ₂ : Env D₂} {x : Var}
    {a₂ : D₂} (h₁ : ρ₁.get x = none) (h₂ : ρ₂.get x = some a₂) {Q : SProp} :
    lr.EnvOk ρ₁ ρ₂ ⊢ Q := by
  simp only [EnvOk]
  refine (forall_elim x).trans ?_
  rw [h₁, h₂, OptRel_none_some]; exact false_elim

theorem envOk_some_none (lr : LR2 SProp D₁ D₂ L) {ρ₁ : Env D₁} {ρ₂ : Env D₂} {x : Var}
    {a₁ : D₁} (h₁ : ρ₁.get x = some a₁) (h₂ : ρ₂.get x = none) {Q : SProp} :
    lr.EnvOk ρ₁ ρ₂ ⊢ Q := by
  simp only [EnvOk]
  refine (forall_elim x).trans ?_
  rw [h₁, h₂, OptRel_some_none]; exact false_elim

/-- Binding a boxed related pair extends a related env. -/
theorem envOk_extend (lr : LR2 SProp D₁ D₂ L) (ρ₁ : Env D₁) (ρ₂ : Env D₂) (x : Var) (a₁ : D₁)
    (a₂ : D₂) :
    iprop(lr.EnvOk ρ₁ ρ₂ ∧ □ IsLookupR L lr.R a₁ a₂) ⊢ lr.EnvOk (ρ₁[x ↦ a₁]) (ρ₂[x ↦ a₂]) := by
  simp only [EnvOk]
  refine forall_intro fun y => ?_
  by_cases hyx : y = x
  · subst hyx
    rw [Env.get_extend_self, Env.get_extend_self, OptRel_some_some]
    exact and_elim_r
  · rw [Env.get_extend_ne _ _ hyx, Env.get_extend_ne _ _ hyx]
    exact and_elim_l.trans (forall_elim y)

/-- Binding a `ConR`-related pair of lists extends a related env. -/
theorem envOk_extendMany (lr : LR2 SProp D₁ D₂ L) (ρ₁ : Env D₁) (ρ₂ : Env D₂) (xs : List Var)
    (ds₁ : List D₁) (ds₂ : List D₂) :
    iprop(lr.EnvOk ρ₁ ρ₂ ∧ Parametric.ConR L lr.R ds₁ ds₂) ⊢
      lr.EnvOk ρ₁[xs ↦* ds₁] ρ₂[xs ↦* ds₂] := by
  induction xs generalizing ρ₁ ρ₂ ds₁ ds₂ with
  | nil => exact and_elim_l
  | cons x xs ih =>
    cases ds₁ with
    | nil =>
      cases ds₂ with
      | nil => exact and_elim_l
      | cons v₂ vs₂ => exact and_elim_r.trans (by rw [Parametric.ConR]; exact false_elim)
    | cons v₁ vs₁ =>
      cases ds₂ with
      | nil => exact and_elim_r.trans (by rw [Parametric.ConR]; exact false_elim)
      | cons v₂ vs₂ =>
        simp only [Env.extendMany, Parametric.ConR_cons]
        refine .trans (and_intro ?_ (and_elim_r.trans and_elim_r)) (ih (ρ₁[x ↦ v₁]) (ρ₂[x ↦ v₂]) vs₁ vs₂)
        exact (and_intro and_elim_l (and_elim_r.trans and_elim_l)).trans (lr.envOk_extend ρ₁ ρ₂ x v₁ v₂)

/-- A `getMany` from a related env is `ConR`-related, in lockstep. -/
theorem envOk_getMany (lr : LR2 SProp D₁ D₂ L) (ρ₁ : Env D₁) (ρ₂ : Env D₂) :
    (xs : List Var) →
      lr.EnvOk ρ₁ ρ₂ ⊢ OptRel (Parametric.ConR L lr.R) (ρ₁.getMany xs) (ρ₂.getMany xs)
  | [] => by
      simp only [Env.getMany, OptRel_some_some, Parametric.ConR_nil]; exact true_intro
  | x :: xs => by
      simp only [Env.getMany]
      cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x
      · exact true_intro
      · exact lr.envOk_none_some h₁ h₂
      · exact lr.envOk_some_none h₁ h₂
      · rename_i a₁ a₂
        cases hm₁ : ρ₁.getMany xs <;> cases hm₂ : ρ₂.getMany xs
        · exact true_intro
        · exact (lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [hm₁, hm₂]; exact false_elim)
        · exact (lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [hm₁, hm₂]; exact false_elim)
        · rename_i ds₁ ds₂
          exact and_intro (lr.envOk_get h₁ h₂)
            ((lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [hm₁, hm₂]; exact .rfl))

/-! ## Fundamental lemma -/

/-- **Fundamental Lemma.** Related environments send the *same* program
    through two `Domain` instances to `R`-related denotations, for a program
    scoped under the let universe `L` and an abstract environment whose
    entries are fresh outside `L`. The value-introducing fields' parametricity
    and freshness premises are supplied by `Exp.relTransport`/`predTransport`,
    the free theorem of `eval` and its diagonal, proved independently. -/
theorem fundamental [BIAffine SProp] [BIPersistentlyForall SProp] (lr : LR2 SProp D₁ D₂ L) :
    (e : Exp) → e.Scoped L → ∀ (ρ₁ : Env D₁) (ρ₂ : Env D₂), EnvFresh L ρ₂ →
      (lr.EnvOk ρ₁ ρ₂ ⊢ lr.R (eval e ρ₁) (eval e ρ₂))
  | .ref x, _, ρ₁, ρ₂, _ => by
    simp only [eval]
    cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x
    · exact LR.of_empValid lr.stuck
    · exact lr.envOk_none_some h₁ h₂
    · exact lr.envOk_some_none h₁ h₂
    · exact (lr.envOk_get h₁ h₂).trans (intuitionistically_elim.trans (IsLookupR_to_R L lr.R _ _))
  | .conapp K xs, _, ρ₁, ρ₂, _ => by
    simp only [eval, Env.getElem?_getMany]
    cases h₁ : ρ₁.getMany xs <;> cases h₂ : ρ₂.getMany xs
    · exact LR.of_empValid lr.stuck
    · exact (lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [h₁, h₂, OptRel_none_some]; exact false_elim)
    · exact (lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [h₁, h₂, OptRel_some_none]; exact false_elim)
    · rename_i ds₁ ds₂
      refine .trans ?_ (lr.con K ds₁ ds₂)
      exact (lr.envOk_getMany ρ₁ ρ₂ xs).trans (by rw [h₁, h₂, OptRel_some_some]; exact .rfl)
  | .lam x body, hsc, ρ₁, ρ₂, hρf => by
    obtain ⟨hbsc, hxA, hxL⟩ := hsc.lam_inv
    simp only [eval]
    refine .trans ?_ (lr.fn x (ofe_fun a => eval body ρ₁[x ↦ a]) (ofe_fun a => eval body ρ₂[x ↦ a])
      body.lamBV hxA hxL hbsc.lam_notin
      (ParametricOn.fn_eval (fun y hy => hy) hbsc.let_mem hρf)
      (FreshFn.fn_eval (fun hx => hxL (hbsc.let_mem x hx))
        (fun w d hget => hρf w d hget x hxL)))
    refine envOk_box ?_
    simp only [Parametric.FnR]
    refine forall_intro fun a₁ => forall_intro fun a₂ => imp_intro ?_
    refine pure_elim (∀ y, y ∉ L → Fresh y a₂)
      (and_elim_r.trans (intuitionistically_elim.trans (IsLookupR_fresh L lr.R a₁ a₂)))
      fun ha₂ => ?_
    refine .trans ?_ (fundamental lr body hbsc (ρ₁[x ↦ a₁]) (ρ₂[x ↦ a₂])
      (EnvPred.extend hρf x ha₂))
    exact lr.envOk_extend ρ₁ ρ₂ x a₁ a₂
  | .app e x, hsc, ρ₁, ρ₂, hρf => by
    simp only [eval]
    cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x
    · exact LR.of_empValid lr.stuck
    · exact lr.envOk_none_some h₁ h₂
    · exact lr.envOk_some_none h₁ h₂
    · rename_i a₁ a₂
      refine .trans ?_ (lr.apply (eval e ρ₁) a₁ (eval e ρ₂) a₂)
      exact and_intro (fundamental lr e hsc.app_inv ρ₁ ρ₂ hρf) (lr.envOk_get h₁ h₂)
  | .«case» eₛ alts, hsc, ρ₁, ρ₂, hρf => by
    obtain ⟨hssc, hbrsc⟩ := hsc.case_inv
    simp only [eval]
    have halts₁ : (alts.attach.map (fun alt =>
        (alt.1.con, alt.1.vars.length, ofe_fun ds =>
          if ds.length = alt.1.vars.length then
            Domain.step .case2 (eval alt.1.rhs ρ₁[alt.1.vars ↦* ds])
          else Domain.stuck)))
        = Parametric.stepAlts (alts.attach.map (fun alt =>
            (alt.1.con, alt.1.vars.length,
              ofe_fun ds => eval alt.1.rhs ρ₁[alt.1.vars ↦* ds]))) := by
      simp only [Parametric.stepAlts, List.map_map]; rfl
    have halts₂ : (alts.attach.map (fun alt =>
        (alt.1.con, alt.1.vars.length, ofe_fun ds =>
          if ds.length = alt.1.vars.length then
            Domain.step .case2 (eval alt.1.rhs ρ₂[alt.1.vars ↦* ds])
          else Domain.stuck)))
        = Parametric.stepAlts (alts.attach.map (fun alt =>
            (alt.1.con, alt.1.vars.length,
              ofe_fun ds => eval alt.1.rhs ρ₂[alt.1.vars ↦* ds]))) := by
      simp only [Parametric.stepAlts, List.map_map]; rfl
    rw [halts₁, halts₂]
    have hAlts : ∀ p ∈ Parametric.stepAlts (alts.attach.map (fun alt =>
        (alt.1.con, alt.1.vars.length,
          ofe_fun ds => eval alt.1.rhs ρ₂[alt.1.vars ↦* ds]))),
        ∃ A, (∀ y ∈ A, y ∉ L) ∧ ParametricAltOn A L (fun ds => p.2.2 ds) := by
      intro p hp
      simp only [Parametric.stepAlts, List.map_map, List.mem_map] at hp
      obtain ⟨alt, hmem, rfl⟩ := hp
      exact ⟨alt.1.rhs.lamBV, (hbrsc alt hmem).lam_notin,
        ParametricAltOn.case_eval (fun y hy => hy) (hbrsc alt hmem).let_mem hρf⟩
    refine .trans ?_ (lr.select (eval eₛ ρ₁) (eval eₛ ρ₂) _ _ hAlts)
    refine and_intro (fundamental lr eₛ hssc ρ₁ ρ₂ hρf) (envOk_box ?_)
    simp only [Parametric.AltsR]
    refine and_intro (pure_intro (by simp only [List.length_map])) ?_
    rw [Parametric.zip_map_map]
    refine bigAndL_intro (fun k p hget => ?_)
    rw [List.getElem?_map] at hget
    obtain ⟨alt, hmem, rfl⟩ := Option.map_eq_some_iff.mp hget
    refine and_intro (pure_intro ⟨rfl, rfl⟩) ?_
    refine forall_intro fun ds₁ => forall_intro fun ds₂ => imp_intro ?_
    refine pure_elim (∀ d ∈ ds₂, ∀ y, y ∉ L → Fresh y d)
      (and_elim_r.trans (Parametric.ConR_fresh L lr.R ds₁ ds₂)) fun hds₂ => ?_
    refine .trans ?_ (fundamental lr alt.1.rhs (hbrsc alt (List.mem_of_getElem? hmem))
      ρ₁[alt.1.vars ↦* ds₁] ρ₂[alt.1.vars ↦* ds₂]
      (EnvPred.extendMany alt.1.vars hρf hds₂))
    exact lr.envOk_extendMany ρ₁ ρ₂ alt.1.vars ds₁ ds₂
  | .«let» x e₁ e₂, hsc, ρ₁, ρ₂, hρf => by
    obtain ⟨h₁sc, h₂sc, hxL⟩ := hsc.let_inv
    simp only [eval]
    refine .trans ?_ (lr.bind _ _ _ _ (fun y hy => FreshFn.look_eval
      (fun h => hy (h ▸ hxL)) (fun hin => hy (h₁sc.let_mem y hin))
      (fun w d hget => hρf w d hget y hy)))
    refine and_intro (envOk_box ?_) ?_
    · refine forall_intro fun a₁ => forall_intro fun a₂ => imp_intro ?_
      refine pure_elim (∀ y, y ∉ L → Fresh y a₂)
        (and_elim_r.trans (intuitionistically_elim.trans (lr.IsThunk_fresh a₁ a₂)))
        fun ha₂ => ?_
      have hstep : ∀ y, y ∉ L → Fresh y (Domain.step (.look x) a₂) := fun y hy =>
        Fresh.step (.look x) (fun h => hy (Event.look.inj h ▸ hxL)) (ha₂ y hy)
      refine .trans ?_ (fundamental lr e₁ h₁sc (ρ₁[x ↦ Domain.step (.look x) a₁])
        (ρ₂[x ↦ Domain.step (.look x) a₂]) (EnvPred.extend hρf x hstep))
      refine .trans ?_ (lr.envOk_extend ρ₁ ρ₂ x (Domain.step (.look x) a₁) (Domain.step (.look x) a₂))
      exact and_intro and_elim_l (and_elim_r.trans
        (IsLookupR_look_intro_box hstep (intuitionistically_mono (lr.IsThunk_to_R x a₁ a₂))))
    · refine forall_intro fun a₁ => forall_intro fun a₂ => imp_intro ?_
      refine pure_elim (∀ y, y ∉ L → Fresh y a₂)
        (and_elim_r.trans (intuitionistically_elim.trans (lr.IsThunk_fresh a₁ a₂)))
        fun ha₂ => ?_
      have hstep : ∀ y, y ∉ L → Fresh y (Domain.step (.look x) a₂) := fun y hy =>
        Fresh.step (.look x) (fun h => hy (Event.look.inj h ▸ hxL)) (ha₂ y hy)
      refine .trans ?_ (fundamental lr e₂ h₂sc (ρ₁[x ↦ Domain.step (.look x) a₁])
        (ρ₂[x ↦ Domain.step (.look x) a₂]) (EnvPred.extend hρf x hstep))
      refine .trans ?_ (lr.envOk_extend ρ₁ ρ₂ x (Domain.step (.look x) a₁) (Domain.step (.look x) a₂))
      exact and_intro and_elim_l (and_elim_r.trans
        (IsLookupR_look_intro_box hstep (intuitionistically_mono (lr.IsThunk_to_R x a₁ a₂))))
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

end LR2

end AbsDen
