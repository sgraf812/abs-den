import AbsDen.LR2
import AbsDen.Productive
import AbsDen.BoundedUsage
import AbsDen.ParametricLR

/-! # The abstraction laws (`fig:abstraction-laws`)

The laws an abstract domain `V` must satisfy for its analysis
`eval (d := Discrete V)` to soundly abstract the by-need semantics: an
`AbstractDomain` with a `Lat` order is a `Domain` over its discrete OFE (where
`-n>` is `→`), and the analysis is the generic `eval` at that instance.

Each law is an inequality or equation in the abstract domain's approximation
order `⊑`. `Mono` requires `step`, `apply`, and `select` monotone; the congruence laws
`Step-App`/`Step-Sel` push a `step` outward past `apply`/`select`; the `Stuck`
laws make application and selection of non-matching values approximate `stuck`;
`Beta-App`/`Beta-Sel` state that summarising then applying (selecting)
approximates a direct call, for parametric bodies on fresh arguments;
`Bind-Prefix` and `Bind-Lazy` state that `bind` promises its body a
pre-fixpoint of the right-hand side, and treats the body uniformly: what it
passes to the body is what it passes to the identity. The promise's freshness
is not a law: it follows generically (`Fresh.bind_id`);
`Step-Inc` and `Update` are the by-need-specific laws.

The by-need representation relation built over these laws and the soundness
theorem `thm:abstract-by-need` live in `AbsDen.NeedSound`. -/

open Iris Iris.BI Iris.COFE OFE

namespace AbsDen

/-- The promise of a recursive binding, `bind` at the identity body, is
    fresh at every binder the right-hand side preserves: the `bind` closure
    clause certifies the promise, whatever fixpoint engine computes it. -/
theorem Fresh.bind_id {V : Type} [AbstractDomain V] {x : Var} {rhs : V → V}
    (hff : FreshFn (D := Discrete V) x rhs) :
    Fresh (D := Discrete V) x (AbstractDomain.bind (D := V) rhs id) :=
  fun P hP => by
    have h := hP.bind (discreteHom rhs) (discreteHom id)
      (fun d hd => hff P hP d hd) (fun _ hd => hd)
    rwa [disc_bind] at h

/-- The abstraction laws an abstract domain `V` must satisfy for its analysis
    `eval (d := Discrete V)` to be sound. The order carries `Std.IsPreorder` and
    bounded completeness, the structure the representation relation is built over. -/
structure AbstractionLaws (V : Type) [AbstractDomain V] [Lat V]
    [Std.IsPreorder V] [ChainComplete V] : Prop where
  mono_step : ∀ (ev : Event) {a b : V},
    (a ⊑ b) = true → (AbstractDomain.step ev a ⊑ AbstractDomain.step ev b) = true
  mono_apply : ∀ {d d' a a' : V},
    (d ⊑ d') = true → (a ⊑ a') = true →
    (AbstractDomain.apply d a ⊑ AbstractDomain.apply d' a') = true
  mono_select : ∀ {d d' : V} (alts : List (ConTag × Nat × (List V → V))),
    (d ⊑ d') = true → (AbstractDomain.select d alts ⊑ AbstractDomain.select d' alts) = true
  step_apply : ∀ (ev : Event) (d a : V),
    (AbstractDomain.step ev (AbstractDomain.apply d a)
      ⊑ AbstractDomain.apply (AbstractDomain.step ev d) a) = true
  step_select : ∀ (ev : Event) (d : V) (alts : List (ConTag × Nat × (List V → V))),
    (AbstractDomain.step ev (AbstractDomain.select d alts)
      ⊑ AbstractDomain.select (AbstractDomain.step ev d) alts) = true
  stuck_apply_stuck : ∀ (a : V),
    (AbstractDomain.stuck ⊑ AbstractDomain.apply AbstractDomain.stuck a) = true
  stuck_apply_con : ∀ (K : ConTag) (ds : List V) (a : V),
    (AbstractDomain.stuck ⊑ AbstractDomain.apply (AbstractDomain.con K ds) a) = true
  stuck_select_stuck : ∀ (alts : List (ConTag × Nat × (List V → V))),
    (AbstractDomain.stuck ⊑ AbstractDomain.select AbstractDomain.stuck alts) = true
  stuck_select_fn : ∀ (x : Var) (f : V → V) (alts : List (ConTag × Nat × (List V → V))),
    (AbstractDomain.stuck ⊑ AbstractDomain.select (AbstractDomain.fn x f) alts) = true
  stuck_select_con : ∀ (K : ConTag) (ds : List V) (alts : List (ConTag × Nat × (List V → V))),
    (∀ p ∈ alts, p.1 ≠ K) →
    (AbstractDomain.stuck ⊑ AbstractDomain.select (AbstractDomain.con K ds) alts) = true
  stuck_select_arity : ∀ (K : ConTag) (n : Nat) (br : List V → V) (ds : List V)
      (alts : List (ConTag × Nat × (List V → V))),
    (K, n, br) ∈ alts → n ≠ ds.length →
    AbstractDomain.stuck ⊑ AbstractDomain.select (AbstractDomain.con K ds) alts
  apply_fn : ∀ (x : Var) (f : V → V) (a : V) (A L : List Var),
    x ∉ A → x ∉ L → ParametricOn (D := Discrete V) A L f →
    FreshFn (D := Discrete V) x f → Fresh (D := Discrete V) x a →
    (∀ y ∈ A, Fresh (D := Discrete V) y a) →
    f a ⊑ AbstractDomain.apply (AbstractDomain.fn x f) a
  select_con : ∀ (K : ConTag) (n : Nat) (br : List V → V) (ds : List V)
      (alts : List (ConTag × Nat × (List V → V))) (A L : List Var),
    ParametricAltOn (D := Discrete V) A L br →
    (∀ y ∈ A, ∀ d ∈ ds, Fresh (D := Discrete V) y d) →
    (K, n, br) ∈ alts → ds.length = n →
    br ds ⊑ AbstractDomain.select (AbstractDomain.con K ds) alts
  bind_prefix : ∀ (rhs : V → V),
    rhs (AbstractDomain.bind rhs id) ⊑ AbstractDomain.bind rhs id
  bind_lazy : ∀ (rhs body : V → V),
    body (AbstractDomain.bind rhs id) ⊑ AbstractDomain.bind rhs body
  step_inc : ∀ (ev : Event) (d : V),
    (d ⊑ AbstractDomain.step ev d) = true
  update : ∀ (d : V),
    AbstractDomain.step Event.update d = d

end AbsDen
