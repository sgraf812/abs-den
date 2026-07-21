import AbsDen.Semantics

/-! # The pure relational vocabulary of the domain combinators

The `Prop`-valued siblings of `LR`/`LR2`, defined over any `Domain`: they
speak only about the combinators, never about `eval`.

`FreshClosed x P` says the predicate `P` is closed under every domain
combinator that does not look up `x`; `Fresh x d` is its least solution,
impredicatively encoded, and reads "`d` admits a construction that never looks
up `x`". Occurrence of a variable is not observable in a generic domain
element (a `Domain` exposes constructors only), so the least combinator-closed
predicate is the canonical domain-agnostic rendering of "`x` cannot occur in
`d`": producers introduce `P` and apply the closure fields, consumers
instantiate `P` at the concrete fact they need. `FreshFn` is the
function-level form, quantified per predicate so that a consumer can transport
its one instantiated fact through a closure.

`ParametricLR` is the binary sibling: a relation on one domain together with a
closure clause per combinator. The `LookOk` and `FnOk` fields name the lookup
events and summarised binders the relation is closed at; a relation built
around a distinguished binder `x` (such as the substitution relation of the
usage `Beta-App` proof) is closed at every other variable only.
`ParametricOn A L f` is the free theorem of `f : D → D` relative to binder
coverage: `f` maps related elements to related elements for every pure
relation whose clauses cover the summarised binders in `A` and the lookups in
`L`.

The transport theorems `Exp.relTransport` and `Exp.predTransport` push both
notions through the interpreter: `eval e` is parametric relative to coverage
of `e`'s lambda and let binders, and preserves every closed predicate avoiding
a variable that `e` does not let-bind. Freshness transport is the diagonal
instance of parametricity transport, so it is not a separate induction. -/

open Iris Iris.COFE OFE

namespace AbsDen

variable {D : Type} [OFE D] [Domain D]

/-! ## Freshness -/

/-- `P` is closed under every domain combinator that does not look up `x`. -/
structure FreshClosed (x : Var) (P : D → Prop) : Prop where
  stuck : P Domain.stuck
  step : ∀ (ev : Event) (d : D), ev ≠ .look x → P d → P (Domain.step ev d)
  apply : ∀ d a : D, P d → P a → P (Domain.apply d a)
  con : ∀ (K : ConTag) (ds : List D), (∀ d ∈ ds, P d) → P (Domain.con K ds)
  select : ∀ (d : D) (alts : List (ConTag × Nat × (List D -n> D))), P d →
    (∀ p ∈ alts, ∀ ds : List D, (∀ d ∈ ds, P d) → P (p.2.2 ds)) →
    P (Domain.select d alts)
  fn : ∀ (y : Var) (f : D -n> D), (∀ d, P d → P (f d)) → P (Domain.fn y f)
  bind : ∀ rhs body : D -n> D, (∀ d, P d → P (rhs d)) → (∀ d, P d → P (body d)) →
    P (Domain.bind rhs body)

/-- `x` cannot occur in `d`: `d` admits a construction that never looks up
    `x`. -/
def Fresh (x : Var) (d : D) : Prop := ∀ P : D → Prop, FreshClosed x P → P d

/-- `g` transports every `FreshClosed` predicate: the function-level freshness
    of `x` for `g`. -/
def FreshFn (x : Var) (g : D → D) : Prop :=
  ∀ P : D → Prop, FreshClosed x P → ∀ d, P d → P (g d)

/-- The branch-level form of `FreshFn`, for the alternatives of `select`. -/
def FreshAlt (x : Var) (br : List D → D) : Prop :=
  ∀ P : D → Prop, FreshClosed x P → ∀ ds : List D, (∀ d ∈ ds, P d) → P (br ds)

theorem Fresh.stuck (x : Var) : Fresh x (Domain.stuck : D) :=
  fun _ hP => hP.stuck

theorem Fresh.step {x : Var} {d : D} (ev : Event) (hev : ev ≠ .look x)
    (hd : Fresh x d) : Fresh x (Domain.step ev d) :=
  fun P hP => hP.step ev d hev (hd P hP)

theorem Fresh.apply {x : Var} {d a : D} (hd : Fresh x d) (ha : Fresh x a) :
    Fresh x (Domain.apply d a) :=
  fun P hP => hP.apply d a (hd P hP) (ha P hP)

theorem Fresh.con {x : Var} (K : ConTag) {ds : List D}
    (hds : ∀ d ∈ ds, Fresh x d) : Fresh x (Domain.con K ds) :=
  fun P hP => hP.con K ds fun d hd => hds d hd P hP

theorem Fresh.select {x : Var} {d : D} {alts : List (ConTag × Nat × (List D -n> D))}
    (hd : Fresh x d) (halts : ∀ p ∈ alts, FreshAlt x ⇑p.2.2) :
    Fresh x (Domain.select d alts) :=
  fun P hP => hP.select d alts (hd P hP) fun p hp => halts p hp P hP

theorem Fresh.fn {x y : Var} {f : D -n> D} (hf : FreshFn x ⇑f) :
    Fresh x (Domain.fn y f) :=
  fun P hP => hP.fn y f (hf P hP)

theorem Fresh.bind {x : Var} {rhs body : D -n> D} (hrhs : FreshFn x ⇑rhs)
    (hbody : FreshFn x ⇑body) : Fresh x (Domain.bind rhs body) :=
  fun P hP => hP.bind rhs body (hrhs P hP) (hbody P hP)

theorem FreshFn.fresh {x : Var} {g : D → D} (hg : FreshFn x g) {d : D}
    (hd : Fresh x d) : Fresh x (g d) :=
  fun P hP => hg P hP d (hd P hP)

/-! ## Parametricity -/

/-- A pure binary logical relation on one semantic domain: a closure clause
    per combinator. `LookOk` names the lookup events and `FnOk` the summarised
    binders the relation is closed at; every other clause is unconditional. -/
structure ParametricLR (D : Type) [OFE D] [Domain D] where
  R : D → D → Prop
  LookOk : Var → Prop
  FnOk : Var → Prop
  stuck : R Domain.stuck Domain.stuck
  step : ∀ (ev : Event) (d₁ d₂ : D), (∀ y, ev = .look y → LookOk y) →
    R d₁ d₂ → R (Domain.step ev d₁) (Domain.step ev d₂)
  apply : ∀ d₁ d₂ a₁ a₂ : D, R d₁ d₂ → R a₁ a₂ →
    R (Domain.apply d₁ a₁) (Domain.apply d₂ a₂)
  con : ∀ (K : ConTag) (ds₁ ds₂ : List D), List.Forall₂ R ds₁ ds₂ →
    R (Domain.con K ds₁) (Domain.con K ds₂)
  select : ∀ (d₁ d₂ : D) (alts₁ alts₂ : List (ConTag × Nat × (List D -n> D))),
    R d₁ d₂ →
    List.Forall₂ (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2.1 = p₂.2.1 ∧
      ∀ ds₁ ds₂ : List D, List.Forall₂ R ds₁ ds₂ → R (p₁.2.2 ds₁) (p₂.2.2 ds₂))
      alts₁ alts₂ →
    R (Domain.select d₁ alts₁) (Domain.select d₂ alts₂)
  fn : ∀ (y : Var) (f₁ f₂ : D -n> D), FnOk y →
    (∀ d₁ d₂, R d₁ d₂ → R (f₁ d₁) (f₂ d₂)) → R (Domain.fn y f₁) (Domain.fn y f₂)
  bind : ∀ rhs₁ rhs₂ body₁ body₂ : D -n> D,
    (∀ d₁ d₂, R d₁ d₂ → R (rhs₁ d₁) (rhs₂ d₂)) →
    (∀ d₁ d₂, R d₁ d₂ → R (body₁ d₁) (body₂ d₂)) →
    R (Domain.bind rhs₁ body₁) (Domain.bind rhs₂ body₂)

/-- `f` maps related elements to related elements, for every pure relation
    whose clauses cover the summarised binders in `A` and the lookups in `L`
    and that is reflexive at elements fresh wherever it is not closed under
    lookup. The reflexivity premise lets a caller self-relate the fixed
    environment entries `f` closes over, from their freshness alone. -/
def ParametricOn (A L : List Var) (f : D → D) : Prop :=
  ∀ lr : ParametricLR D, (∀ y ∈ A, lr.FnOk y) → (∀ z ∈ L, lr.LookOk z) →
    (∀ d, (∀ y, ¬ lr.LookOk y → Fresh y d) → lr.R d d) →
    ∀ d₁ d₂, lr.R d₁ d₂ → lr.R (f d₁) (f d₂)

/-- The branch-level form of `ParametricOn`: a case alternative maps pointwise
    related field lists to related results, for every pure relation whose
    clauses cover the summarised binders in `A` and the lookups in `L` and
    that is reflexive at fresh elements. -/
def ParametricAltOn (A L : List Var) (br : List D → D) : Prop :=
  ∀ lr : ParametricLR D, (∀ y ∈ A, lr.FnOk y) → (∀ z ∈ L, lr.LookOk z) →
    (∀ d, (∀ y, ¬ lr.LookOk y → Fresh y d) → lr.R d d) →
    ∀ ds₁ ds₂ : List D, List.Forall₂ lr.R ds₁ ds₂ → lr.R (br ds₁) (br ds₂)

/-! ## Environment coupling -/

namespace Parametric

/-- Pointwise coupling of optional values. -/
def OptRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

end Parametric

/-- Pointwise coupling of two environments: bound in lockstep, with related
    entries. -/
def EnvRel (R : D → D → Prop) (ρ₁ ρ₂ : Env D) : Prop :=
  ∀ y : Var, Parametric.OptRel R (ρ₁.get y) (ρ₂.get y)

theorem EnvRel.extend {R : D → D → Prop} {ρ₁ ρ₂ : Env D} (h : EnvRel R ρ₁ ρ₂)
    (x : Var) {d₁ d₂ : D} (hd : R d₁ d₂) : EnvRel R ρ₁[x ↦ d₁] ρ₂[x ↦ d₂] := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    rw [Env.get_extend_self, Env.get_extend_self]
    exact hd
  · rw [Env.get_extend_ne _ _ hyx, Env.get_extend_ne _ _ hyx]
    exact h y

theorem EnvRel.extendMany {R : D → D → Prop} :
    ∀ (xs : List Var) {ρ₁ ρ₂ : Env D} {ds₁ ds₂ : List D}, EnvRel R ρ₁ ρ₂ →
      List.Forall₂ R ds₁ ds₂ → EnvRel R ρ₁[xs ↦* ds₁] ρ₂[xs ↦* ds₂]
  | [], _, _, _, _, h, _ => h
  | _ :: _, _, _, _, _, h, .nil => h
  | x :: xs, _, _, _, _, h, .cons hd hds =>
      EnvRel.extendMany xs (h.extend x hd) hds

theorem EnvRel.getMany {R : D → D → Prop} {ρ₁ ρ₂ : Env D} (h : EnvRel R ρ₁ ρ₂) :
    ∀ xs : List Var, Parametric.OptRel (List.Forall₂ R) (ρ₁.getMany xs) (ρ₂.getMany xs)
  | [] => List.Forall₂.nil
  | x :: xs => by
    have hx := h x
    have hxs := h.getMany xs
    simp only [Env.getMany]
    cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x <;> rw [h₁, h₂] at hx
    · exact trivial
    · exact hx.elim
    · exact hx.elim
    · cases hm₁ : ρ₁.getMany xs <;> cases hm₂ : ρ₂.getMany xs <;> rw [hm₁, hm₂] at hxs
      · exact trivial
      · exact hxs.elim
      · exact hxs.elim
      · exact List.Forall₂.cons hx hxs

/-- All entries of an environment satisfy `P`. -/
def EnvPred (P : D → Prop) (ρ : Env D) : Prop :=
  ∀ y d, ρ.get y = some d → P d

theorem EnvPred.empty {P : D → Prop} : EnvPred P (Env.empty : Env D) :=
  fun _ _ hget => nomatch hget

theorem EnvPred.extend {P : D → Prop} {ρ : Env D} (h : EnvPred P ρ) (x : Var)
    {d : D} (hd : P d) : EnvPred P ρ[x ↦ d] := by
  intro y d' hget
  by_cases hyx : y = x
  · subst hyx
    rw [Env.get_extend_self] at hget
    exact Option.some_inj.mp hget ▸ hd
  · rw [Env.get_extend_ne _ _ hyx] at hget
    exact h y d' hget

theorem EnvPred.extendMany {P : D → Prop} :
    ∀ (xs : List Var) {ρ : Env D} {ds : List D}, EnvPred P ρ →
      (∀ d ∈ ds, P d) → EnvPred P ρ[xs ↦* ds]
  | [], _, _, h, _ => h
  | _ :: _, _, [], h, _ => h
  | x :: xs, _, d :: ds, h, hds =>
      EnvPred.extendMany xs (h.extend x (hds d (List.mem_cons_self ..)))
        (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))

theorem EnvPred.getMany {P : D → Prop} {ρ : Env D} (h : EnvPred P ρ) :
    ∀ {xs : List Var} {ds : List D}, ρ.getMany xs = some ds → ∀ d ∈ ds, P d
  | [], _, hget, d, hd => by
    simp only [Env.getMany, Option.some_inj] at hget
    exact absurd (hget ▸ hd) (List.not_mem_nil)
  | x :: xs, _, hget, d, hd => by
    simp only [Env.getMany, Option.bind_eq_some_iff] at hget
    obtain ⟨a, ha, hget⟩ := hget
    obtain ⟨ds', hds', rfl⟩ := Option.map_eq_some_iff.mp hget
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact h x d ha
    · exact h.getMany hds' d hd'

/-- Pointwise relate two maps over the same list. -/
theorem forall₂_map_same {α β γ : Type} {S : β → γ → Prop} {f : α → β}
    {g : α → γ} : ∀ {l : List α}, (∀ a ∈ l, S (f a) (g a)) →
      List.Forall₂ S (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (List.mem_cons_self ..))
      (forall₂_map_same fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

/-- Read a left-only relation off a `Forall₂`. -/
theorem forall₂_left {α β : Type} {Q : α → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a _ => Q a) l₁ l₂ → ∀ a ∈ l₁, Q a
  | _, _, .nil => fun a ha => absurd ha List.not_mem_nil
  | _, _, .cons h hs => fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact h
      · exact forall₂_left hs a ha'

/-- Every left element of a `Forall₂` is related to some right element. -/
theorem forall₂_mem_left {α β : Type} {S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ S l₁ l₂ → ∀ a ∈ l₁, ∃ b, S a b
  | _, _, .nil => fun a ha => absurd ha List.not_mem_nil
  | _, _, .cons h hs => fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨_, h⟩
      · exact forall₂_mem_left hs a ha'

/-- A left-only predicate over a list is a diagonal `Forall₂`. -/
theorem diag_forall₂ {α : Type} {Q : α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, Q a) → List.Forall₂ (fun a _ => Q a) l l
  | [], _ => .nil
  | a :: l, h => .cons (h a (List.mem_cons_self ..))
      (diag_forall₂ (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')))

/-! ## Transport through the interpreter

The free theorem of `eval`: a pure relation whose guards cover the
expression's lambda and let binders relates the evaluations of pointwise
related environments. Its freshness sibling, that a combinator-closed
predicate avoiding a variable the expression does not let-bind holds of the
evaluation over an environment of `P`-entries, is not a separate induction:
a `FreshClosed` predicate is a `ParametricLR` on the diagonal, so freshness
transport is parametricity transport read at `fun a _ => P a`. -/

/-- The parametricity transport of `e`. -/
def Exp.RelTransport (e : Exp) : Prop :=
  ∀ {D : Type} [OFE D] [Domain D] (plr : ParametricLR D) (ρ₁ ρ₂ : Env D),
    (∀ y ∈ e.lamBV, plr.FnOk y) → (∀ z ∈ e.letBV, plr.LookOk z) →
    EnvRel plr.R ρ₁ ρ₂ → plr.R (eval e ρ₁) (eval e ρ₂)

/-- The freshness transport of `e`. -/
def Exp.PredTransport (e : Exp) : Prop :=
  ∀ {D : Type} [OFE D] [Domain D] (x : Var) (P : D → Prop),
    FreshClosed x P → x ∉ e.letBV → ∀ ρ : Env D, EnvPred P ρ → P (eval e ρ)

/-- **Parametricity transport.** One structural recursion over the
    expression, discharging each `eval` clause by the matching `ParametricLR`
    clause. The free theorem of `eval`. -/
theorem Exp.relTransport : (e : Exp) → e.RelTransport
  | .ref x => fun plr ρ₁ ρ₂ _ _ hρ => by
    simp only [eval]
    have hx := hρ x
    cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x <;> rw [h₁, h₂] at hx
    · exact plr.stuck
    · exact hx.elim
    · exact hx.elim
    · exact hx
  | .lam x body => fun plr ρ₁ ρ₂ hA hL hρ => by
    simp only [eval]
    simp only [Exp.lamBV] at hA
    simp only [Exp.letBV] at hL
    refine plr.fn x _ _ (hA x (List.mem_cons_self ..)) fun d₁ d₂ hd => ?_
    refine plr.step .app2 _ _ (fun _ h => nomatch h) ?_
    exact body.relTransport plr _ _ (fun y hy => hA y (List.mem_cons_of_mem _ hy))
      hL (hρ.extend x hd)
  | .app e x => fun plr ρ₁ ρ₂ hA hL hρ => by
    simp only [eval]
    simp only [Exp.lamBV] at hA
    simp only [Exp.letBV] at hL
    have hx := hρ x
    cases h₁ : ρ₁.get x <;> cases h₂ : ρ₂.get x <;> rw [h₁, h₂] at hx
    · exact plr.stuck
    · exact hx.elim
    · exact hx.elim
    · refine plr.step .app1 _ _ (fun _ h => nomatch h) ?_
      exact plr.apply _ _ _ _ (e.relTransport plr ρ₁ ρ₂ hA hL hρ) hx
  | .conapp K xs => fun plr ρ₁ ρ₂ _ _ hρ => by
    simp only [eval, Env.getElem?_getMany]
    have hxs := hρ.getMany xs
    cases h₁ : ρ₁.getMany xs <;> cases h₂ : ρ₂.getMany xs <;> rw [h₁, h₂] at hxs
    · exact plr.stuck
    · exact hxs.elim
    · exact hxs.elim
    · exact plr.con K _ _ hxs
  | .«case» eₛ alts => fun plr ρ₁ ρ₂ hA hL hρ => by
    simp only [eval]
    simp only [Exp.lamBV] at hA
    simp only [Exp.letBV] at hL
    refine plr.step .case1 _ _ (fun _ h => nomatch h) ?_
    refine plr.select _ _ _ _
      (eₛ.relTransport plr ρ₁ ρ₂
        (fun y hy => hA y (List.mem_append_left _ hy))
        (fun z hz => hL z (List.mem_append_left _ hz)) hρ)
      (forall₂_map_same fun alt halt => ⟨rfl, rfl, fun ds₁ ds₂ hds => ?_⟩)
    show plr.R
      (if ds₁.length = alt.1.vars.length then
        Domain.step .case2 (eval alt.1.rhs ρ₁[alt.1.vars ↦* ds₁]) else Domain.stuck)
      (if ds₂.length = alt.1.vars.length then
        Domain.step .case2 (eval alt.1.rhs ρ₂[alt.1.vars ↦* ds₂]) else Domain.stuck)
    rw [forall₂_length hds]
    by_cases hlen : ds₂.length = alt.1.vars.length
    · rw [if_pos hlen, if_pos hlen]
      refine plr.step .case2 _ _ (fun _ h => nomatch h) ?_
      refine alt.1.rhs.relTransport plr _ _
        (fun y hy => hA y (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨alt, halt, hy⟩)))
        (fun z hz => hL z (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨alt, halt, hz⟩)))
        (EnvRel.extendMany alt.1.vars hρ hds)
    · rw [if_neg hlen, if_neg hlen]
      exact plr.stuck
  | .«let» x e₁ e₂ => fun plr ρ₁ ρ₂ hA hL hρ => by
    simp only [eval]
    simp only [Exp.lamBV] at hA
    simp only [Exp.letBV] at hL
    refine plr.step .let1 _ _ (fun _ h => nomatch h) ?_
    have hlook : plr.LookOk x := hL x (List.mem_cons_self ..)
    have hext : ∀ {d₁ d₂}, plr.R d₁ d₂ →
        EnvRel plr.R ρ₁[x ↦ Domain.step (.look x) d₁] ρ₂[x ↦ Domain.step (.look x) d₂] :=
      fun hd => hρ.extend x
        (plr.step (.look x) _ _ (fun _ h => by cases Event.look.inj h; exact hlook) hd)
    refine plr.bind _ _ _ _ (fun d₁ d₂ hd => ?_) (fun d₁ d₂ hd => ?_)
    · exact e₁.relTransport plr _ _
        (fun y hy => hA y (List.mem_append_left _ hy))
        (fun z hz => hL z (List.mem_cons_of_mem _ (List.mem_append_left _ hz)))
        (hext hd)
    · exact e₂.relTransport plr _ _
        (fun y hy => hA y (List.mem_append_right _ hy))
        (fun z hz => hL z (List.mem_cons_of_mem _ (List.mem_append_right _ hz)))
        (hext hd)
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

/-- A `FreshClosed` predicate is a `ParametricLR` on the diagonal: lookups
    avoid `x`, binders are unrestricted, the second argument is ignored. -/
def FreshClosed.toParametricLR {x : Var} {P : D → Prop} (hP : FreshClosed x P) :
    ParametricLR D where
  R a _ := P a
  LookOk y := y ≠ x
  FnOk _ := True
  stuck := hP.stuck
  step ev d₁ d₂ hev h := hP.step ev d₁ (fun heq => hev x heq rfl) h
  apply d₁ d₂ a₁ a₂ hd ha := hP.apply d₁ a₁ hd ha
  con K ds₁ ds₂ hds := hP.con K ds₁ (forall₂_left hds)
  select d₁ d₂ alts₁ alts₂ hd halts :=
    hP.select d₁ alts₁ hd (fun p hp ds hds => by
      obtain ⟨_p₂, _htag, _harity, hbr⟩ := forall₂_mem_left halts p hp
      exact hbr ds ds (diag_forall₂ hds))
  fn y f₁ f₂ _ hf := hP.fn y f₁ (fun d hd => hf d d hd)
  bind rhs₁ rhs₂ body₁ body₂ hr hb :=
    hP.bind rhs₁ body₁ (fun d hd => hr d d hd) (fun d hd => hb d d hd)

/-- An `EnvPred` environment is diagonally related under the diagonal
    relation. -/
theorem envRel_diag_of_envPred {P : D → Prop} {ρ : Env D} (h : EnvPred P ρ) :
    EnvRel (fun a _ => P a) ρ ρ := by
  intro y
  cases hget : ρ.get y with
  | none => exact trivial
  | some a => exact h y a hget

/-- **Freshness transport**, as the diagonal instance of parametricity
    transport: no separate induction. -/
theorem Exp.predTransport (e : Exp) : e.PredTransport :=
  fun x P hP hxL ρ hρ => e.relTransport hP.toParametricLR ρ ρ
    (fun _ _ => trivial) (fun z hz hzx => hxL (hzx ▸ hz))
    (envRel_diag_of_envPred hρ)

/-- Freshness transport through `eval`, by dot notation on the predicate: a
    combinator-closed predicate avoiding `x` holds of the evaluation when the
    expression does not let-bind `x` and the predicate holds of every entry. -/
theorem FreshClosed.eval_pred {x : Var} {P : D → Prop}
    (hP : FreshClosed x P) (e : Exp) (ρ : Env D) (hxL : x ∉ e.letBV)
    (hρ : EnvPred P ρ) : P (eval e ρ) :=
  e.predTransport x P hP hxL ρ hρ

/-! ## Establishing the premises for `eval` closures

The shapes the fundamental lemma stores: an `eval` closure over an
environment whose entries are fresh outside the let universe `L` is
parametric relative to any coverage of its binders, and preserves the
freshness of every variable it does not let-bind. -/

/-- Every entry of `ρ` is fresh outside the let universe `L`. -/
def EnvFresh (L : List Var) (ρ : Env D) : Prop :=
  EnvPred (fun d => ∀ y, y ∉ L → Fresh y d) ρ

/-- A fresh-entry environment is diagonally self-related under any relation
    covering `L`. -/
theorem EnvRel.diag {lr : ParametricLR D} {L : List Var} {ρ : Env D}
    (covL : ∀ z ∈ L, lr.LookOk z)
    (hrefl : ∀ d, (∀ y, ¬ lr.LookOk y → Fresh y d) → lr.R d d)
    (hρ : EnvFresh L ρ) : EnvRel lr.R ρ ρ := by
  intro z
  cases hget : ρ.get z
  · exact trivial
  · exact hrefl _ (fun y hny => hρ z _ hget y (fun hyL => hny (covL y hyL)))

/-- The summarised closure of an `eval` lambda clause is parametric on any
    coverage of its body's binders. -/
theorem ParametricOn.fn_eval {A L : List Var} {x : Var} {body : Exp} {ρ : Env D}
    (hA : ∀ y ∈ body.lamBV, y ∈ A) (hL : ∀ z ∈ body.letBV, z ∈ L)
    (hρ : EnvFresh L ρ) :
    ParametricOn A L (fun a => Domain.step .app2 (eval body ρ[x ↦ a])) := by
  intro lr covA covL hrefl d₁ d₂ hd
  refine lr.step .app2 _ _ (fun _ h => nomatch h) ?_
  exact body.relTransport lr _ _ (fun y hy => covA y (hA y hy))
    (fun z hz => covL z (hL z hz))
    ((EnvRel.diag covL hrefl hρ).extend x hd)

/-- The guarded branch of an `eval` case clause is parametric on any coverage
    of its right-hand side's binders. -/
theorem ParametricAltOn.case_eval {A L : List Var} {vars : List Var}
    {rhs : Exp} {n : Nat} {ρ : Env D}
    (hA : ∀ y ∈ rhs.lamBV, y ∈ A) (hL : ∀ z ∈ rhs.letBV, z ∈ L)
    (hρ : EnvFresh L ρ) :
    ParametricAltOn A L (fun ds => if ds.length = n then
      Domain.step .case2 (eval rhs ρ[vars ↦* ds]) else Domain.stuck) := by
  intro lr covA covL hrefl ds₁ ds₂ hds
  show lr.R
    (if ds₁.length = n then Domain.step .case2 (eval rhs ρ[vars ↦* ds₁])
      else Domain.stuck)
    (if ds₂.length = n then Domain.step .case2 (eval rhs ρ[vars ↦* ds₂])
      else Domain.stuck)
  rw [forall₂_length hds]
  by_cases hlen : ds₂.length = n
  · rw [if_pos hlen, if_pos hlen]
    refine lr.step .case2 _ _ (fun _ h => nomatch h) ?_
    exact rhs.relTransport lr _ _ (fun y hy => covA y (hA y hy))
      (fun z hz => covL z (hL z hz))
      (EnvRel.extendMany vars (EnvRel.diag covL hrefl hρ) hds)
  · rw [if_neg hlen, if_neg hlen]
    exact lr.stuck

/-- The summarised closure of an `eval` lambda clause preserves the freshness
    of a variable its body does not let-bind, over `x`-fresh entries. -/
theorem FreshFn.fn_eval {x z : Var} {body : Exp} {ρ : Env D}
    (hxL : x ∉ body.letBV) (hρ : ∀ w d, ρ.get w = some d → Fresh x d) :
    FreshFn x (fun a => Domain.step .app2 (eval body ρ[z ↦ a])) :=
  fun P hP d hd => hP.step .app2 _ (fun h => nomatch h)
    (body.predTransport x P hP hxL _
      (EnvPred.extend (fun w d' hget => hρ w d' hget P hP) z hd))

/-- The look-wrapped closure of an `eval` let clause preserves the freshness
    of a variable other than its binder that its subterm does not let-bind,
    over `x`-fresh entries. -/
theorem FreshFn.look_eval {x z : Var} {e : Exp} {ρ : Env D}
    (hzx : z ≠ x) (hxL : x ∉ e.letBV)
    (hρ : ∀ w d, ρ.get w = some d → Fresh x d) :
    FreshFn x (fun a => eval e ρ[z ↦ Domain.step (.look z) a]) :=
  fun P hP d hd => e.predTransport x P hP hxL _
    (EnvPred.extend (fun w d' hget => hρ w d' hget P hP) z
      (hP.step (.look z) _ (fun h => hzx (Event.look.inj h)) hd))

end AbsDen
