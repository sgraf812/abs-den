import AbsDen.NoConsecInvis

/-!
# Sketch: combinator library + use site

Two sections.

§1 (combinators) is where every `Pred.ofClosed` lives — one per combinator,
each a one-line closure proof composing inputs' `.closed`. PascalCase under
`World.Pred.*`.

§2 (use) defines predicates using **only** the §1 language. No
`Pred.ofClosed`, no manual closure proofs, no `match n with` on levels.
-/

namespace ByNeed.SketchUnified
open ByNeed NewIdea

/-! ## §1. Combinator library.

This is the only place that may say `Pred.ofClosed`. Generalizes
`Later.prop` and friends. -/

/-- Specialize `Later.elim` to constant target: extract the value, with
    `default` at level 0. Inverse of `Later.next` at `Const`. -/
def Later.elimConst {A : Type u} {n : Nat} (default : A) :
    Later (World.Const A) n → A :=
  Later.elim default id

/-- Trivially-true. Identity for `Pred.And`. -/
def World.Pred.True {F : Nat → Type} [World F] {n : Nat} : World.Pred F n :=
  World.Pred.ofClosed (fun _ => _root_.True) (fun _ _ => trivial)

/-- Never holds. Identity for `Pred.Or`. -/
def World.Pred.False {F : Nat → Type} [World F] {n : Nat} : World.Pred F n :=
  World.Pred.ofClosed (fun _ => _root_.False) (fun _ h => h)

/-- Pointwise disjunction. -/
def World.Pred.Or {F : Nat → Type} [World F] {n : Nat}
    (P Q : World.Pred F n) : World.Pred F n :=
  ⟨fun m hm x => P.val m hm x ∨ Q.val m hm x,
   fun m hm x h => h.elim
     (fun hp => .inl (P.property m hm x hp))
     (fun hq => .inr (Q.property m hm x hq))⟩

/-- Sum case-analysis: `Pred.OfSum P Q` holds on `Sum.inl a` iff `P a`, on
    `Sum.inr b` iff `Q b`. -/
def World.Pred.OfSum {A B : Nat → Type} [World A] [World B] {n : Nat}
    (P : World.Pred A n) (Q : World.Pred B n) : World.Pred (World.Sum A B) n :=
  ⟨fun m hm s => match s with | .inl a => P.val m hm a | .inr b => Q.val m hm b,
   fun m hm s h => match s, h with
     | .inl a, h => P.property m hm a h
     | .inr b, h => Q.property m hm b h⟩

/-- HOAS existential over a *constant* witness type. Binds `g : G` by name. -/
def World.Pred.ExistsConst {F : Nat → Type} [World F] {n : Nat} (G : Type)
    (P : G → World.Pred F n) : World.Pred F n :=
  ⟨fun m hm x => ∃ g : G, (P g).val m hm x,
   fun m hm x ⟨g, h⟩ => ⟨g, (P g).property m hm x h⟩⟩

/-- Image of a natural map `f : A → B` as a `Pred B`: holds at `b` iff
    `∃ a : A _, f a = b`. -/
def World.Pred.Image {A B : Nat → Type} [hA : World A] [hB : World B]
    (f : ∀ {n}, A n → B n) [hf : @Naturality A B hA hB f] {n : Nat} :
    World.Pred B n :=
  ⟨fun m _ b => ∃ a : A m, f a = b,
   fun m hm x ⟨a, h⟩ => ⟨World.restrictStep a, by
     have hnat := hf.isNatural a
     simp only [hnat, h]⟩⟩

/-- Preimage (= inverse image) of `P : Pred B` along a natural map
    `f : A → B`: holds at `a` iff `P` holds at `f a`. Set-theoretically
    `f⁻¹(P) = {a : f a ∈ P}`. Pairs with `Pred.Image` (the forward direction). -/
def World.Pred.Preimage {A B : Nat → Type} [hA : World A] [hB : World B]
    (f : ∀ {n}, A n → B n) [hf : @Naturality A B hA hB f] {n : Nat}
    (P : World.Pred B n) : World.Pred A n :=
  ⟨fun m hm a => P.val m hm (f a),
   fun m hm x h => by
     have hnat := hf.isNatural x
     have h2 := P.property m hm (f x) h
     show P.val m _ (f (World.restrictStep x))
     rw [show f (World.restrictStep x) = World.restrictStep (f x) from hnat]
     exact h2⟩

/-- Equation of two natural maps as a `Pred A`. -/
def World.Pred.EqOf {A B : Nat → Type} [hA : World A] [hB : World B]
    (f g : ∀ {n}, A n → B n)
    [hf : @Naturality A B hA hB f] [hg : @Naturality A B hA hB g] {n : Nat} :
    World.Pred A n :=
  ⟨fun m _ a => f a = g a,
   fun m hm x h => by
     have hfnat := hf.isNatural x
     have hgnat := hg.isNatural x
     show f (World.restrictStep x) = g (World.restrictStep x)
     simp only [hfnat, hgnat, h]⟩

/-- ▷ at the Pred level: extract a `Pred F n` from a `Later (Pred F) n`. At
    `n = 0` the result is `Pred.True` (▷ is vacuous); at `n = k+1` the recur
    is a `Pred F k`, used at sub-levels via `World.restrict`. Pred-level
    analogue of `Later.prop`. -/
def World.Pred.Later {F : Nat → Type} [World F] : ∀ {n : Nat},
    _root_.Later (World.Pred F) n → World.Pred F n
  | 0, _ => World.Pred.True
  | k+1, lp =>
    ⟨fun m _hm x =>
       lp.val (min m k) (Nat.min_le_right m k)
         (World.restrict x (Nat.min_le_left m k)),
     fun m hm1 x h => by
       -- Closure: `lp.val (min (m+1) k) _ (restrict x (min_le_left _ k))` for
       -- `m+1 ≤ k+1` implies the same at `m`. Both sides project to the same
       -- underlying `lp.val (min m k) _ (restrict (restrictStep x) _)`.
       sorry⟩

/-- Push `Later` from outside the `Pred` to inside the value type: turn a
    `Later (Pred F) n` into a `Pred (Later F) n`. At `n = 0` the result is
    vacuous; at `n = k+1`, the recur is `Pred F k`, and `Later F (j+1) = F j`
    for `j ≤ k`. -/
def World.Pred.AbsorbLater {F : Nat → Type} [World F] : ∀ {n : Nat},
    _root_.Later (World.Pred F) n → World.Pred (_root_.Later F) n
  | 0, _ => World.Pred.True
  | k+1, lp =>
    ⟨fun
       | 0, _, _ => _root_.True
       | j+1, hj1, x => lp.val j (Nat.le_of_succ_le_succ hj1) (x : F j),
     by
       -- Closure: trivial at m = 0; at m = j+2 uses lp's closure.
       intro m hm1 x h
       sorry⟩

/-- Function-Pred: `f : world(A → B) n` holds iff for every sub-level `k` and
    every input `a : A k` satisfying `P_A`, the output `f k _ a` satisfies
    `P_B`. The persistent-implication form (∀ sub-levels) makes closure
    automatic via the input/output Preds' own closures. -/
def World.Pred.Function {A B : Nat → Type} [World A] [World B] {n : Nat}
    (P_A : World.Pred A n) (P_B : World.Pred B n) :
    World.Pred (World.Function A B) n :=
  ⟨fun m hm f =>
     ∀ (k : Nat) (hk : k ≤ m) (a : A k),
       P_A.val k (Nat.le_trans hk hm) a →
       P_B.val k (Nat.le_trans hk hm) (f k hk a),
   by intro m hm1 f h; sorry⟩

/-- "For every value `v` projected out of the container `c`, `P` holds at
    `v`." Generic lift of a `Pred V n` to a `Pred C n` given a projection
    `proj : C m → Container (V m)` and a `Membership` instance on the
    projected container. The projection is the load-bearing parameter — pass
    `HashMap.values` for `Heap`, `id` for List-valued containers, etc. -/
def World.Pred.AllOfMem {C V : Nat → Type} [World C] [World V]
    {Container : Type → Type} [∀ V', Membership V' (Container V')] {n : Nat}
    (proj : ∀ {m}, C m → Container (V m))
    (P : World.Pred V n) : World.Pred C n :=
  ⟨fun m hm c => ∀ v : V m, v ∈ proj c → P.val m hm v,
   by intro m hm1 c h; sorry⟩

/-- Heap-goodness against a `Later (Pred D) n` recursive ref: every heap
    entry satisfies the Later-Pred lifted to a Pred on Later-values. Uses
    `Pred.AllOfMem` with `HashMap.values` as the projection. -/
noncomputable def World.Pred.ParametricHeapOf {n : Nat}
    (RecurPred : _root_.Later (World.Pred D) n) : World.Pred (Heap (▹ D)) n :=
  World.Pred.AllOfMem (proj := fun μ => μ.values) (World.Pred.AbsorbLater RecurPred)

/-- Case-on-`T.unfold` as a Pred combinator. Dispatches a `Pred (T V) n` by
    the trace's first-step shape: `.ret v` → `P_ret v`, `.step _ tl` → `P_step
    tl`, `.invis dl` → `P_invis dl`. The event in `.step` is discarded; pass
    an `ExistsConst`-quantified `P_step` if event dispatch is needed.

    The naturality (`restrictStep`-closure) of the result depends on
    `T.unfold` naturality; sorried for the sketch. -/
noncomputable def World.Pred.TraceMatch {V : Nat → Type} [World V] {n : Nat}
    (P_ret : World.Pred V n)
    (P_step : World.Pred (_root_.Later (T V)) n)
    (P_invis : World.Pred (_root_.Later (T V)) n) :
    World.Pred (T V) n :=
  ⟨fun m hm t =>
     match T.unfold t with
     | .ret v => P_ret.val m hm v
     | .step _ tl => P_step.val m hm tl
     | .invis dl => P_invis.val m hm dl,
   by
     -- Closure: needs `T.unfold` naturality (T.unfold ∘ restrictStep =
     -- restrictStep ∘ T.unfold) to lift the per-case closure proofs. Sketch
     -- sorry pending `T.unfold.naturality` (already sorried above).
     intro m hm1 x h; sorry⟩

/-! ## Naturality instances (live near `§1` extensions — these are library
    plumbing, not user-site predicates). -/

instance Domain.step'.naturality {D : Nat → Type} [Domain D] (ev : Event) :
    Naturality (fun {n : Nat} (d : D n) => Domain.step' (n := n) ev d) :=
  ⟨Domain.natural_step ev⟩

/-- `T.unfold` naturality: `T.unfold ∘ restrictStep = restrictStep ∘ T.unfold`.
    Sorried for the sketch. -/
instance T.unfold.naturality {V : Nat → Type} [World V] :
    Naturality (@T.unfold V _) := ⟨by intro n t; sorry⟩

/-- `D.unfold` viewed as a natural map from `D` into `world(Heap (▹ D) →
    T VH)`. Sorried for the sketch — proof routes through `Fix.unfold` naturality. -/
instance D.unfold.naturality :
    @Naturality D (World.Function (Heap (▹ D)) (T VH)) _ _
      (fun {n : Nat} (d : D n) => d.unfold) :=
  ⟨by intro n d; sorry⟩

/-! ## §1.5 `loeb` on `World.Pred` — sanity-check the API. -/

/-- Smoke test: `loeb` applies directly to `World.Pred D` because `Pred` is now
    a presheaf with a `World` instance. The body ignores its recursive ref, so
    the result is just `Pred.True` lifted. -/
example {N : Nat} : World.Pred D N :=
  loeb (fun _n _hn _Recur => World.Pred.True)

/-! ## §2. Use the language.

Only §1 combinators. No `.ofClosed`, no `match n with`, no `.closed`. -/

/-- `IsLookShape : Pred D` = `∃ x : Var, image of `step' (.look x)`.

    Uses the same `ExistsConst` + `Image` combinator stack as the `IsLookShape`
    in `AbsDen/LR.lean`; that one is the canonical version (used by `IsLookup`). -/
noncomputable def IsLookShape {n : Nat} : World.Pred D n :=
  World.Pred.ExistsConst Var fun x =>
    World.Pred.Image (fun {n} (d : D n) => Domain.step' (.look x) d)

/-! ## §2.5. `TraceGoodP` and `GoodP` via direct `loeb` on `World.Pred`.

`TraceGoodP` is `loeb` on `world(Nat → Pred (T VH))` so the budget reset on
`.step` and decrement on `.invis` happen inside the recursion itself (rather
than being pinned externally). The body stays in the Pred internal language:
recursive references go through `Pred.OfLater` and case dispatch on
`T.unfold` goes through `Pred.TraceMatch`. -/

/-- The body of `TraceGoodP`'s `loeb`. At each sub-level `m` and budget `S`,
    produces a `Pred (T VH) m` via `Pred.TraceMatch` — `.ret` defers to
    `RetGoodP`, `.step` resets to budget 2, `.invis` decrements (and at
    budget 0 yields `Pred.False`).

    The recursive call goes through `Pred.UnderLater (Later.ap' m (Recur↓)
    (Later.next B))`: restrict `Recur` to level `m`, evaluate at budget `B`
    (still inside `Later`), then `UnderLater` to get a `Pred (Later (T VH))`
    we can plug into `Pred.TraceMatch`'s step/invis slots.

    Codomain `world(Nat → World.Pred (T VH))` parses now that the macro
    handles presheaf-codomain applications via direct elaboration. -/
noncomputable def TraceGoodPBody (RetGoodP : ∀ {n}, World.Pred VH n) {N : Nat} :
    World.Function
      (_root_.Later world(Nat → World.Pred (T VH)))
      world(Nat → World.Pred (T VH)) N :=
  fun _n _hn Recur m hm S =>
    let S' : Nat := S
    let RecurAtBudget (B : Nat) : World.Pred (Later (T VH)) m :=
      World.Pred.AbsorbLater
        (Later.ap' m (World.restrict Recur hm) (Later.next B))
    World.Pred.TraceMatch
      (P_ret := RetGoodP)
      (P_step := RecurAtBudget 2)
      (P_invis :=
        match S' with
        | 0 => World.Pred.False
        | s + 1 => RecurAtBudget s)

/-- The trace predicate as a one-line `loeb` on the budget-indexed Pred
    family. -/
noncomputable def TraceGoodP (RetGoodP : ∀ {n}, World.Pred VH n) {N : Nat} :
    world(Nat → World.Pred (T VH)) N :=
  loeb (TraceGoodPBody RetGoodP)

/-- The body of `GoodP`'s `loeb`. `d : D m` is good if every
    `Recur`-heap-good `μ` makes `d.unfold m μ` `TraceGoodP`-good. Composed
    from `Pred.Preimage D.unfold` (D ≃ Function Heap (T VH) via unfold) +
    `Pred.Function` (function-Pred from input/output Preds) + `Pred.ParametricHeapOf`
    (heap-goodness as a Pred). -/
noncomputable def GoodPBody (S : Nat) {N : Nat} :
    World.Function (Later (World.Pred D)) (World.Pred D) N :=
  fun n _hn Recur =>
    -- Sketch: stub RetGoodP with Pred.True; real version closes over the
    -- recursive ref at budgets 1 and 2 (see NewIdea.RetGoodP).
    World.Pred.Preimage (·.unfold)
      (World.Pred.Function
        (World.Pred.ParametricHeapOf Recur)
        (TraceGoodP (RetGoodP := World.Pred.True) n (Nat.le_refl _) S))

/-- The value-level "good" predicate as a one-line `loeb` on `World.Pred D`. -/
noncomputable def GoodP (S : Nat) {N : Nat} : World.Pred D N :=
  loeb (GoodPBody S)

end ByNeed.SketchUnified
