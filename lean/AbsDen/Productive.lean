import AbsDen.ByNeed
import AbsDen.LR
import Iris.BI
import Iris.BI.SIProp
import Iris.ProofMode

/-! # The ByNeed productivity logical relation on `SiProp`

Ported from the `Productive.*` sketch in `AbsDen/SketchUnified.lean` (§2.5).
There the predicates are budget-indexed `World.Pred` families defined by `loeb`;
here the domain is the single OFE `D` and predicates are step-indexed maps
`· -n> SiProp`, so the level/naturality plumbing collapses into
non-expansiveness. The two `loeb`s become Banach `fixpoint`s over
`Gate → (· -n> SiProp)`; every trace layer is scored against a `Gate` listing
the head constructors it may open with: a visible `.step` refills the gate to
`.any`, the silent `.invis` only `.any` admits lands its tail at `.step`, and
a `.ret` passes every gate except `.step`.

The `World.Pred` combinators collapse into BI connectives and plain `match`es:
`Function`/`Preimage` to `∀`/`→`, `TraceMatch`/`ValueMatch` to a `match` on
the trace and value layers, `ParametricHeapOf` to a per-entry `∀` over the heap,
and `AbsorbLater` to `▷ (P ·.car)` (a `▷`-guarded reference at a thunk). -/

open Iris Iris.BI Iris.COFE OFE

set_option maxHeartbeats 50000

namespace AbsDen

instance : Inhabited SiProp := ⟨iprop(True)⟩

/-- What a trace returns: a value together with the resulting heap. -/
abbrev VH : Type := ValueHeapOF D D

/-! ## `SiProp` `Dist` congruence helpers

`SiProp`'s `Dist n P Q` unfolds to `∀ {m}, m ≤ n → (P.holds m ↔ Q.holds m)`; the
implicit `{m}` makes `exact`-ing a folded `≡{n}≡` term trigger implicit-lambda
introduction. Direct wrappers (applied with all-concrete arguments) sidestep it. -/

theorem reflD {n} (X : SiProp) : X ≡{n}≡ X := by apply OFE.dist_eqv.refl

theorem andD {n} {A A' B B' : SiProp} (h1 : A ≡{n}≡ A') (h2 : B ≡{n}≡ B') :
    iprop(A ∧ B) ≡{n}≡ iprop(A' ∧ B') := by
  apply and_ne.ne
  · exact h1
  · exact h2

theorem impD {n} {A A' B B' : SiProp} (h1 : A ≡{n}≡ A') (h2 : B ≡{n}≡ B') :
    iprop(A → B) ≡{n}≡ iprop(A' → B') := by
  apply imp_ne.ne
  · exact h1
  · exact h2

theorem iteD {n} {P : Prop} [Decidable P] {A A' B B' : SiProp}
    (h1 : A ≡{n}≡ A') (h2 : B ≡{n}≡ B') :
    (if P then A else B) ≡{n}≡ (if P then A' else B') := by
  split
  · exact h1
  · exact h2

/-- A `▷`-guarded reference at a thunk is non-expansive in the thunk (`▷` recovers
    the step lost by forcing `·.car`). -/
theorem later_car_ne {A : Type} [OFE A] {n} {P : A -n> SiProp} {x y : Later A}
    (h : x ≡{n}≡ y) : iprop(▷ (P x.car)) ≡{n}≡ iprop(▷ (P y.car)) := by
  apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
  intro m hm; exact P.ne.ne (h m hm)

/-- A `▷`-guarded reference at a thunk is contractive in its predicate. -/
theorem later_car_distLater {A : Type} [OFE A] {n} {P P' : A -n> SiProp}
    (h : DistLater n P P') (x : Later A) :
    iprop(▷ (P x.car)) ≡{n}≡ iprop(▷ (P' x.car)) := by
  apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
  intro m hm; exact h m hm x.car

namespace Productive

/-! ## The head gate -/

/-- Which head constructors a trace layer may open with: any layer, only a
    visible layer (a return or a visible step), or only a visible step or a
    `stuck` return. The gate governs the current segment: a visible step
    refills it to `.any`, the silent step `.any` admits lands its tail at
    `.step`, and a return passes every gate, except that `.step` passes only a
    `stuck` return (the end a machine reaches without a further transition). -/
inductive Gate
  | any
  | visible
  | step
  deriving DecidableEq

/-- `g ≤ g'`: every head `g` admits, `g'` admits. -/
protected def Gate.le : Gate → Gate → Prop
  | .step, _ => True
  | .visible, .step => False
  | .visible, _ => True
  | .any, .any => True
  | .any, _ => False

instance : LE Gate := ⟨Gate.le⟩

theorem Gate.visible_le_any : Gate.visible ≤ Gate.any := trivial

theorem Gate.le_step : ∀ {g : Gate}, g ≤ Gate.step → g = Gate.step
  | .step, _ => rfl
  | .visible, h => nomatch h
  | .any, h => nomatch h

theorem Gate.any_le : ∀ {g : Gate}, Gate.any ≤ g → g = Gate.any
  | .any, _ => rfl
  | .visible, h => nomatch h
  | .step, h => nomatch h

/-! ## Value goodness -/

/-- A value is good iff: `stuck` is good; a function is, one step later, a
    `Parametric.Fn` from lookups at the `.step` gate to results at the `.step`
    gate (a stored function's argument is look-shaped, so its gate is
    irrelevant, and the `applyCont` guard `.invis` lands the result at
    `.step`); a constructor's fields are, one step later, `Parametric.Con` at
    the full gate. `P` is the gate-indexed goodness family; the `SiProp`
    analogue of `Productive.V` (`AbsorbLater` at a `RecurAt` index). -/
def ValueOk (P : Gate → D -n> SiProp) : Value D -n> SiProp :=
  ⟨fun v => match v with
    | .stuck => iprop(True)
    | .fn g => iprop(▷ Parametric.Fn (P Gate.step) g.car)
    | .con _K ds => iprop(▷ Parametric.Con (P Gate.any) (ds.map (·.car))),
   ⟨fun {_ v v'} h => by
     cases v <;> cases v' <;> try exact False.elim h
     · apply reflD
     · apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
       intro m hm
       exact Parametric.Fn_ne (P Gate.step) (h m hm)
     · apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
       intro m hm
       exact Parametric.Con_ne (P Gate.any) (mapCar_distLater h.2 m hm)⟩⟩

theorem valueOk_distLater {n} {P P' : Gate → D -n> SiProp} (h : DistLater n P P') :
    ValueOk P ≡{n}≡ ValueOk P' := by
  intro v
  cases v with
  | stuck => apply reflD
  | fn g =>
    apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
    intro m hm
    exact Parametric.Fn_ne_pred (h m hm Gate.step) g.car
  | con K ds =>
    apply Contractive.distLater_dist (f := (BIBase.later : SiProp → SiProp))
    intro m hm
    exact Parametric.Con_ne_pred (h m hm Gate.any) (ds.map (·.car))

/-! ## Heap goodness -/

/-- Goodness of an optional stored thunk: `none` is good; a `some dl` is good iff
    `P` holds at `dl` one step later. Matching on the `Option` (not testing
    equality against a fixed thunk) keeps this non-expansive. -/
def EntryOk (P : D -n> SiProp) : Option (Later D) -n> SiProp :=
  ⟨fun o => match o with
    | none => iprop(True)
    | some dl => iprop(▷ (P dl.car)),
   ⟨fun {n o o'} h => by
     cases o <;> cases o' <;> try exact False.elim h
     · apply reflD
     · exact later_car_ne (some_dist_some.mp h)⟩⟩

theorem entryOk_distLater {n} {P P' : D -n> SiProp} (h : DistLater n P P') :
    EntryOk P ≡{n}≡ EntryOk P' := by
  intro o
  cases o with
  | none => apply reflD
  | some dl => exact later_car_distLater h dl

/-- Every stored thunk is good. The `SiProp` analogue of
    `World.Pred.ParametricHeapOf`. -/
def HeapOk (P : D -n> SiProp) : Heap D -n> SiProp :=
  ⟨fun μ => iprop(∀ a, EntryOk P (μ.car a)),
   ⟨fun {_ _ _} h => by apply forall_ne; intro a; exact (EntryOk P).ne.ne (h a)⟩⟩

theorem heapOk_distLater {n} {P P' : D -n> SiProp} (h : DistLater n P P') :
    HeapOk P ≡{n}≡ HeapOk P' := by
  intro μ; apply forall_ne; intro a; exact entryOk_distLater h (μ.car a)

/-! ## Trace goodness (guarded recursion in the gate-indexed family) -/

/-- One unfolded trace layer scored against the gate `g`: a `.ret` passes
    every gate (`.step` only with a `stuck` value), a `.step` refills the
    gate, and the `.invis` only `.any` admits lands its tail at `.step`.
    `rec` sits under `▷`. -/
def TraceOk.rawStep (Ret : VH -n> SiProp)
    (rec : Gate → Trace VH -n> SiProp) (g : Gate) :
    TraceF VH (Trace VH) (Trace VH) -n> SiProp :=
  ⟨fun x => match x with
    | .ret vμ =>
      if g = Gate.step ∧ vμ.1.isStuck = false then iprop(False) else Ret vμ
    | .step _ tl => iprop(▷ (rec Gate.any tl.car))
    | .invis tl => if g = Gate.any then iprop(▷ (rec Gate.step tl.car)) else iprop(False),
   ⟨fun {n x x'} h => by
     rcases x with vμ | ⟨e, tl⟩ | tl <;> rcases x' with vμ' | ⟨e', tl'⟩ | tl' <;>
       try exact False.elim h
     · show (if g = Gate.step ∧ vμ.1.isStuck = false then iprop(False) else Ret vμ)
         ≡{n}≡ (if g = Gate.step ∧ vμ'.1.isStuck = false then iprop(False) else Ret vμ')
       rw [ValueF.isStuck_dist (dist_fst h)]
       exact iteD (reflD _) (Ret.ne.ne h)
     · exact later_car_ne (P := rec Gate.any) h.2
     · exact iteD (later_car_ne (P := rec Gate.step) h) (reflD _)⟩⟩

/-- The body of `Productive.TraceOk`'s fixpoint (over the gate): score the
    unfolded layer. Every recursive reference sits under `▷`, so the operator
    is contractive. -/
def TraceOk.body (Ret : VH -n> SiProp) (rec : Gate → Trace VH -n> SiProp) :
    Gate → Trace VH -n> SiProp :=
  fun g => (TraceOk.rawStep Ret rec g).comp Trace.unfold

instance (Ret : VH -n> SiProp) : OFE.Contractive (TraceOk.body Ret) where
  distLater_dist {n rec rec'} H := by
    intro g t
    show TraceOk.rawStep Ret rec g (Trace.unfold t) ≡{n}≡
      TraceOk.rawStep Ret rec' g (Trace.unfold t)
    rcases Trace.unfold t with vμ | ⟨e, tl⟩ | tl
    · apply reflD
    · exact later_car_distLater (fun m hm => H m hm Gate.any) tl
    · exact iteD (later_car_distLater (fun m hm => H m hm Gate.step) tl) (reflD _)

/-- `TraceOk.body` is non-expansive in the return predicate. -/
theorem TraceOk.body_ret {n} {R R' : VH -n> SiProp} (h : R ≡{n}≡ R')
    (rec : Gate → Trace VH -n> SiProp) (g : Gate) :
    TraceOk.body R rec g ≡{n}≡ TraceOk.body R' rec g := by
  intro t
  show TraceOk.rawStep R rec g (Trace.unfold t) ≡{n}≡
    TraceOk.rawStep R' rec g (Trace.unfold t)
  rcases Trace.unfold t with vμ | ⟨e, tl⟩ | tl
  · exact iteD (reflD _) (h vμ)
  · apply reflD
  · apply reflD

/-- `TraceOk.body` at a returned value reduces to the return predicate, behind
    the gate's `.ret` check. -/
theorem TraceOk.body_ret_eq (Ret : VH -n> SiProp)
    (rec : Gate → Trace VH -n> SiProp) (g : Gate) (vμ : VH) :
    TraceOk.body Ret rec g (Trace.ret vμ) ≡
      (if g = Gate.step ∧ vμ.1.isStuck = false then iprop(False) else Ret vμ) :=
  (TraceOk.rawStep Ret rec g).ne.eqv (Trace.unfold_fold (.ret vμ))

/-- `TraceOk.body` at a visible step reduces to the full-gate tail under `▷`. -/
theorem TraceOk.body_step_eq (Ret : VH -n> SiProp)
    (rec : Gate → Trace VH -n> SiProp) (g : Gate) (ev : Event) (tl : Later (Trace VH)) :
    TraceOk.body Ret rec g (Trace.step ev tl) ≡ iprop(▷ (rec Gate.any tl.car)) :=
  (TraceOk.rawStep Ret rec g).ne.eqv (Trace.unfold_fold (.step ev tl))

/-- `TraceOk.body` at a silent step lands the tail at `.step` under `▷`, behind
    the gate's `.invis` check. -/
theorem TraceOk.body_invis_eq (Ret : VH -n> SiProp)
    (rec : Gate → Trace VH -n> SiProp) (g : Gate) (tl : Later (Trace VH)) :
    TraceOk.body Ret rec g (Trace.invis tl) ≡
      (if g = Gate.any then iprop(▷ (rec Gate.step tl.car)) else iprop(False)) :=
  (TraceOk.rawStep Ret rec g).ne.eqv (Trace.unfold_fold (.invis tl))

/-- The gate-indexed trace family; the fixpoint of `TraceOk.body`. -/
def TraceOkAt (Ret : VH -n> SiProp) : Gate → Trace VH -n> SiProp :=
  (Function.toContractiveHom (TraceOk.body Ret)).fixpoint

/-- The productive-trace predicate: the family at the full gate. -/
def TraceOk (Ret : VH -n> SiProp) : Trace VH -n> SiProp := TraceOkAt Ret Gate.any

theorem traceOkAt_unfold (Ret : VH -n> SiProp) :
    TraceOkAt Ret ≡ TraceOk.body Ret (TraceOkAt Ret) :=
  fixpoint_unfold (Function.toContractiveHom (TraceOk.body Ret))

theorem traceOkAt_ne {n} {R R' : VH -n> SiProp} (h : R ≡{n}≡ R') :
    TraceOkAt R ≡{n}≡ TraceOkAt R' :=
  OFE.ContractiveHom.fixpoint_ne.ne (fun rec g => TraceOk.body_ret h rec g)

/-- Unfold the family at a gate `g` on a trace `t`, as `⊣⊢`. -/
theorem traceOkAt_run (Ret : VH -n> SiProp) (g : Gate) (t : Trace VH) :
    TraceOkAt Ret g t ⊣⊢ TraceOk.body Ret (TraceOkAt Ret) g t :=
  equiv_iff.mp (traceOkAt_unfold Ret g t)

/-- A returned value passes every gate except `.step` and reduces to the
    return predicate. -/
theorem traceOkAt_ret (Ret : VH -n> SiProp) (g : Gate) (hg : g ≠ Gate.step) (vμ : VH) :
    TraceOkAt Ret g (Trace.ret vμ) ⊣⊢ Ret vμ := by
  refine (traceOkAt_run Ret g (Trace.ret vμ)).trans ?_
  refine ((equiv_iff (Q := (if g = Gate.step ∧ vμ.1.isStuck = false then iprop(False)
    else Ret vμ))).mp ?_).trans ?_
  · exact TraceOk.body_ret_eq Ret (TraceOkAt Ret) g vμ
  · exact .of_eq (if_neg fun h => hg h.1)

/-- A returned `stuck` value passes every gate: the trace has ended, so no
    silent step can follow. -/
theorem traceOkAt_ret_isStuck (Ret : VH -n> SiProp) (g : Gate) {vμ : VH}
    (hv : vμ.1.isStuck = true) : TraceOkAt Ret g (Trace.ret vμ) ⊣⊢ Ret vμ := by
  refine (traceOkAt_run Ret g (Trace.ret vμ)).trans ?_
  refine ((equiv_iff (Q := (if g = Gate.step ∧ vμ.1.isStuck = false then iprop(False)
    else Ret vμ))).mp ?_).trans ?_
  · exact TraceOk.body_ret_eq Ret (TraceOkAt Ret) g vμ
  · exact .of_eq (if_neg (by simp [hv]))

/-- The `.step` gate denies a returned non-`stuck` value. -/
theorem traceOkAt_ret_denied (Ret : VH -n> SiProp) {vμ : VH}
    (hv : vμ.1.isStuck = false) :
    TraceOkAt Ret Gate.step (Trace.ret vμ) ⊣⊢ (False : SiProp) := by
  refine (traceOkAt_run Ret Gate.step (Trace.ret vμ)).trans ?_
  refine ((equiv_iff (Q := (if Gate.step = Gate.step ∧ vμ.1.isStuck = false
    then iprop(False) else Ret vμ))).mp ?_).trans ?_
  · exact TraceOk.body_ret_eq Ret (TraceOkAt Ret) Gate.step vμ
  · exact .of_eq (if_pos ⟨rfl, hv⟩)

/-- A visible step passes every gate and refills it under `▷`. -/
theorem traceOkAt_step (Ret : VH -n> SiProp) (g : Gate) (ev : Event) (tl : Later (Trace VH)) :
    TraceOkAt Ret g (Trace.step ev tl) ⊣⊢ iprop(▷ (TraceOkAt Ret Gate.any tl.car)) := by
  refine (traceOkAt_run Ret g (Trace.step ev tl)).trans ?_
  exact equiv_iff.mp (TraceOk.body_step_eq Ret (TraceOkAt Ret) g ev tl)

/-- The full gate passes a silent step, landing its tail at `.step` under `▷`. -/
theorem traceOkAt_invis (Ret : VH -n> SiProp) (tl : Later (Trace VH)) :
    TraceOkAt Ret Gate.any (Trace.invis tl) ⊣⊢ iprop(▷ (TraceOkAt Ret Gate.step tl.car)) := by
  refine (traceOkAt_run Ret Gate.any (Trace.invis tl)).trans ?_
  refine ((equiv_iff (Q := (if Gate.any = Gate.any then iprop(▷ (TraceOkAt Ret Gate.step tl.car))
    else iprop(False)))).mp ?_).trans ?_
  · exact TraceOk.body_invis_eq Ret (TraceOkAt Ret) Gate.any tl
  · exact .of_eq (if_pos rfl)

/-- Every gate but `.any` denies a silent step. -/
theorem traceOkAt_invis_denied (Ret : VH -n> SiProp) (g : Gate) (hg : g ≠ Gate.any)
    (tl : Later (Trace VH)) :
    TraceOkAt Ret g (Trace.invis tl) ⊣⊢ (False : SiProp) := by
  refine (traceOkAt_run Ret g (Trace.invis tl)).trans ?_
  refine ((equiv_iff (Q := (if g = Gate.any then iprop(▷ (TraceOkAt Ret Gate.step tl.car))
    else iprop(False)))).mp ?_).trans ?_
  · exact TraceOk.body_invis_eq Ret (TraceOkAt Ret) g tl
  · exact .of_eq (if_neg hg)

/-- At the full gate, a returned value is the return predicate. -/
theorem traceOk_ret (Ret : VH -n> SiProp) (vμ : VH) :
    TraceOk Ret (Trace.ret vμ) ⊣⊢ Ret vμ :=
  traceOkAt_ret Ret Gate.any (by decide) vμ

/-- A visible step refills the gate under `▷`. -/
theorem traceOk_step (Ret : VH -n> SiProp) (ev : Event) (tl : Later (Trace VH)) :
    TraceOk Ret (Trace.step ev tl) ⊣⊢ iprop(▷ (TraceOk Ret tl.car)) :=
  traceOkAt_step Ret Gate.any ev tl

/-- A silent step lands its tail at `.step` under `▷`. -/
theorem traceOk_invis (Ret : VH -n> SiProp) (tl : Later (Trace VH)) :
    TraceOk Ret (Trace.invis tl) ⊣⊢ iprop(▷ (TraceOkAt Ret Gate.step tl.car)) :=
  traceOkAt_invis Ret tl

/-- `trace` respects trace equivalence in its scrutinee. -/
theorem traceOk_proper (Ret : VH -n> SiProp) {t t' : Trace VH} (h : t ≡ t') :
    TraceOk Ret t ⊣⊢ TraceOk Ret t' :=
  equiv_iff.mp ((TraceOk Ret).ne.eqv h)

/-- `TraceOkAt` at a fixed gate respects trace equivalence in its scrutinee. -/
theorem traceOkAt_proper (Ret : VH -n> SiProp) (g : Gate) {t t' : Trace VH} (h : t ≡ t') :
    TraceOkAt Ret g t ⊣⊢ TraceOkAt Ret g t' :=
  equiv_iff.mp ((TraceOkAt Ret g).ne.eqv h)

/-- `TraceOkAt` reduced through an unfolding equation at a `.ret` layer. -/
theorem traceOkAt_ret_of_unfold (Ret : VH -n> SiProp) (g : Gate) (hg : g ≠ Gate.step)
    {t : Trace VH} {vμ : VH} (hu : Trace.unfold t = .ret vμ) :
    TraceOkAt Ret g t ⊣⊢ Ret vμ :=
  (traceOkAt_proper Ret g (Trace.equiv_of_unfold hu).symm).trans (traceOkAt_ret Ret g hg vμ)

/-- `TraceOkAt` reduced through an unfolding equation at a `stuck` `.ret` layer. -/
theorem traceOkAt_ret_isStuck_of_unfold (Ret : VH -n> SiProp) (g : Gate)
    {t : Trace VH} {vμ : VH} (hv : vμ.1.isStuck = true)
    (hu : Trace.unfold t = .ret vμ) :
    TraceOkAt Ret g t ⊣⊢ Ret vμ :=
  (traceOkAt_proper Ret g (Trace.equiv_of_unfold hu).symm).trans
    (traceOkAt_ret_isStuck Ret g hv)

/-- `TraceOkAt` reduced through an unfolding equation at a denied `.ret` layer. -/
theorem traceOkAt_ret_denied_of_unfold (Ret : VH -n> SiProp)
    {t : Trace VH} {vμ : VH} (hv : vμ.1.isStuck = false)
    (hu : Trace.unfold t = .ret vμ) :
    TraceOkAt Ret Gate.step t ⊣⊢ (False : SiProp) :=
  (traceOkAt_proper Ret Gate.step (Trace.equiv_of_unfold hu).symm).trans
    (traceOkAt_ret_denied Ret hv)

/-- `TraceOkAt` reduced through an unfolding equation at a `.step` layer. -/
theorem traceOkAt_step_of_unfold (Ret : VH -n> SiProp) (g : Gate)
    {t : Trace VH} {ev : Event} {tl : Later (Trace VH)}
    (hu : Trace.unfold t = .step ev tl) :
    TraceOkAt Ret g t ⊣⊢ iprop(▷ (TraceOkAt Ret Gate.any tl.car)) :=
  (traceOkAt_proper Ret g (Trace.equiv_of_unfold hu).symm).trans (traceOkAt_step Ret g ev tl)

/-- `TraceOkAt` reduced through an unfolding equation at an `.invis` layer. -/
theorem traceOkAt_invis_of_unfold (Ret : VH -n> SiProp)
    {t : Trace VH} {tl : Later (Trace VH)} (hu : Trace.unfold t = .invis tl) :
    TraceOkAt Ret Gate.any t ⊣⊢ iprop(▷ (TraceOkAt Ret Gate.step tl.car)) :=
  (traceOkAt_proper Ret Gate.any (Trace.equiv_of_unfold hu).symm).trans (traceOkAt_invis Ret tl)

/-- `TraceOkAt` reduced through an unfolding equation at a denied `.invis` layer. -/
theorem traceOkAt_invis_denied_of_unfold (Ret : VH -n> SiProp) (g : Gate) (hg : g ≠ Gate.any)
    {t : Trace VH} {tl : Later (Trace VH)} (hu : Trace.unfold t = .invis tl) :
    TraceOkAt Ret g t ⊣⊢ (False : SiProp) :=
  (traceOkAt_proper Ret g (Trace.equiv_of_unfold hu).symm).trans
    (traceOkAt_invis_denied Ret g hg tl)

/-- Widening the gate weakens the predicate. One layer suffices: the tails on
    both sides are gated identically. -/
theorem traceOkAt_mono (Ret : VH -n> SiProp) {g g' : Gate} (h : g ≤ g') (t : Trace VH) :
    TraceOkAt Ret g t ⊢ TraceOkAt Ret g' t := by
  rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
  · by_cases hg : g = Gate.step
    · subst hg
      cases hv : vμ.1.isStuck with
      | false => exact (traceOkAt_ret_denied_of_unfold Ret hv hu).1.trans false_elim
      | true =>
        exact (traceOkAt_ret_isStuck_of_unfold Ret Gate.step hv hu).1.trans
          (traceOkAt_ret_isStuck_of_unfold Ret g' hv hu).2
    · have hg' : g' ≠ Gate.step := fun hh => hg (Gate.le_step (hh ▸ h))
      exact (traceOkAt_ret_of_unfold Ret g hg hu).1.trans
        (traceOkAt_ret_of_unfold Ret g' hg' hu).2
  · exact (traceOkAt_step_of_unfold Ret g hu).1.trans (traceOkAt_step_of_unfold Ret g' hu).2
  · by_cases hg : g = Gate.any
    · subst hg
      obtain rfl : g' = Gate.any := Gate.any_le h
      exact .rfl
    · exact (traceOkAt_invis_denied_of_unfold Ret g hg hu).1.trans false_elim

/-! ## Value-level goodness (guarded recursion in the gate-indexed family) -/

/-- The return predicate induced by a gate-indexed goodness family: a returned
    `(v, μ)` is `value`-good in `v` with heap entries good at the `.step`
    gate. -/
def RetOkAt (rec : Gate → D -n> SiProp) : VH -n> SiProp :=
  ⟨fun vμ => iprop(ValueOk rec vμ.1 ∧ HeapOk (rec Gate.step) vμ.2),
   ⟨fun {_ _ _} h => andD ((ValueOk rec).ne.ne (dist_fst h))
      ((HeapOk (rec Gate.step)).ne.ne (dist_snd h))⟩⟩

/-- The body of the gate-indexed goodness family's fixpoint: `d` is good at
    gate `g` iff, against every heap whose entries are good, running `d`
    yields a trace good at `g` whose returns are `value`/`heap`-good. Heap
    entries are good at the `.step` gate: a dereference reaches them behind
    its guard `.invis`, so they must not open silently. Every recursive
    reference sits under `▷` (in `value`/`heap`), so the operator is
    contractive. The analogue of `Productive.D.F`'s budget-indexed family. -/
def DomainOk.body (rec : Gate → D -n> SiProp) : Gate → D -n> SiProp := fun g =>
  ⟨fun d => iprop(∀ μ : Heap D, HeapOk (rec Gate.step) μ →
      TraceOkAt (RetOkAt rec) g (D.unfold d μ)),
   ⟨fun {_ _ _} hd => by
     apply forall_ne; intro μ
     refine impD (reflD _) ?_
     exact (TraceOkAt _ g).ne.ne ((D.unfold.ne.ne hd) μ)⟩⟩

instance : OFE.Contractive DomainOk.body where
  distLater_dist {_ rec rec'} H := by
    intro g d
    apply forall_ne; intro μ
    refine impD (heapOk_distLater (fun m hm => H m hm Gate.step) μ) ?_
    refine traceOkAt_ne ?_ g (D.unfold d μ)
    intro vμ
    exact andD (valueOk_distLater H vμ.1)
      (heapOk_distLater (fun m hm => H m hm Gate.step) vμ.2)

/-- The gate-indexed productive-value family; `domain` is its full-gate entry. -/
def DomainOkAt : Gate → D -n> SiProp := (Function.toContractiveHom DomainOk.body).fixpoint

/-- The productive-value predicate (full gate). -/
def DomainOk : D -n> SiProp := DomainOkAt Gate.any

theorem domainOkAt_unfold : DomainOkAt ≡ DomainOk.body DomainOkAt :=
  fixpoint_unfold (Function.toContractiveHom DomainOk.body)

/-! ## The productivity logical relation as an `LR` instance

`P` is `DomainOkAt .visible`: every `eval` result opens with a returned value or
a visible step. `IsThunk` is what `bind`'s `rhs`/`body` receive, the
dereferencing thunk `fetch addr`; it is plain `domain`-good, since forcing it
spends the guard `.invis` the full gate admits against the `.step`-gate
goodness of heap entries, and an unbound address terminates `stuck`. -/

/-- The trace's return predicate: a `value`-good value with a heap whose
    entries are good at the `.step` gate. -/
def RetOk : VH -n> SiProp := RetOkAt DomainOkAt

/-- Unfold the goodness family at gate `g` to its heap-quantified trace form. -/
theorem domainOkAt_run (g : Gate) (d : D) :
    DomainOkAt g d ⊣⊢ iprop(∀ μ : Heap D, HeapOk (DomainOkAt Gate.step) μ →
      TraceOkAt RetOk g (D.unfold d μ)) :=
  equiv_iff.mp (domainOkAt_unfold g d)

/-- Unfold `domain` to its heap-quantified trace form. -/
theorem domainOk_run (d : D) :
    DomainOk d ⊣⊢ iprop(∀ μ : Heap D, HeapOk (DomainOkAt Gate.step) μ →
      TraceOk RetOk (D.unfold d μ)) :=
  domainOkAt_run Gate.any d

/-- A `.step`-headed denotation at any gate: the leading step refills the
    gate, so the entry gate is irrelevant. -/
theorem domainOkAt_dstep (g : Gate) (ev : Event) (d : D) :
    DomainOkAt g (D.step ev d)
      ⊣⊢ iprop(∀ μ : Heap D, HeapOk (DomainOkAt Gate.step) μ →
          ▷ (TraceOk RetOk (D.unfold d μ))) := by
  refine (domainOkAt_run g (D.step ev d)).trans ?_
  have e : ∀ μ : Heap D, TraceOkAt RetOk g (D.unfold (D.step ev d) μ)
      ⊣⊢ iprop(▷ (TraceOk RetOk (D.unfold d μ))) := fun μ =>
    (traceOkAt_proper RetOk g (D.step_run ev d μ)).trans (traceOkAt_step RetOk g ev _)
  exact ⟨forall_mono fun μ => imp_mono_right (e μ).1,
         forall_mono fun μ => imp_mono_right (e μ).2⟩

/-- Gate transport for `.step`-headed denotations. -/
theorem domainOk_domainAt_step (g : Gate) (ev : Event) (d : D) :
    DomainOk (D.step ev d) ⊢ DomainOkAt g (D.step ev d) :=
  (domainOkAt_dstep Gate.any ev d).1.trans (domainOkAt_dstep g ev d).2

/-- Gate monotonicity, lifted from the traces to the goodness family. -/
theorem domainOkAt_mono {g g' : Gate} (h : g ≤ g') (d : D) : DomainOkAt g d ⊢ DomainOkAt g' d :=
  (domainOkAt_run g d).1.trans
    ((forall_mono fun _ => imp_mono_right (traceOkAt_mono RetOk h _)).trans
      (domainOkAt_run g' d).2)

/-- On look-shaped denotations every gate agrees: the leading look step refills
    the gate, so lookups transport freely between gates. -/
theorem IsLookup_domainAt (g g' : Gate) (a : D) :
    IsLookup (DomainOkAt g) a ⊢ IsLookup (DomainOkAt g') a := by
  show iprop(DomainOkAt g a ∧ IsLookShape a) ⊢ iprop(DomainOkAt g' a ∧ IsLookShape a)
  refine and_intro (and_comm.1.trans (imp_elim ?_)) and_elim_r
  show IsLookShape a ⊢ iprop(DomainOkAt g a → DomainOkAt g' a)
  refine exists_elim fun x => exists_elim fun a' => ?_
  haveI : NonExpansive (fun b : D => iprop(DomainOkAt g b → DomainOkAt g' b)) :=
    ⟨fun {_ _ _} h => impD ((DomainOkAt g).ne.ne h) ((DomainOkAt g').ne.ne h)⟩
  refine internalEq.rewrite' (fun b : D => iprop(DomainOkAt g b → DomainOkAt g' b))
    internalEq.symm (LR.of_empValid (imp_intro ?_))
  exact and_elim_r.trans
    ((domainOkAt_dstep g (.look x) a').1.trans (domainOkAt_dstep g' (.look x) a').2)

/-- A visible step preserves goodness: a step leads immediately, so the tail (one
    step later) is exactly `domain a`. -/
theorem domainOk_step (ev : Event) (a : D) : DomainOk a ⊢ DomainOk (Domain.step ev a) := by
  refine .trans (domainOk_run a).1 ?_
  refine .trans ?_ (domainOk_run (Domain.step ev a)).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOk_proper RetOk (D.step_run ev a μ)).2
  refine .trans ?_ (traceOk_step RetOk ev _).2
  refine .trans ?_ later_intro
  exact (and_intro (and_elim_l.trans (forall_elim μ)) and_elim_r).trans imp_elim_left

/-- `DomainOkAt` at a fixed gate respects `≡` in the denotation. -/
theorem domainOkAt_proper (g : Gate) {d d' : D} (h : d ≡ d') :
    DomainOkAt g d ⊣⊢ DomainOkAt g d' :=
  equiv_iff.mp ((DomainOkAt g).ne.eqv h)

/-- A `Parametric.Fn`-good function, stepped with `ev`, is `value`-good: the
    body's leading step lands the result at the `.step` gate the `applyCont`
    guard `.invis` demands. -/
theorem fn_bridge (ev : Event) (f : D -n> D) :
    Parametric.Fn (DomainOkAt Gate.visible) f
      ⊢ ValueOk DomainOkAt (Value.fn (Later.next ((Domain.step ev).comp f))) := by
  show Parametric.Fn (DomainOkAt Gate.visible) f
    ⊢ iprop(▷ Parametric.Fn (DomainOkAt Gate.step) ((Domain.step ev).comp f))
  refine .trans ?_ later_intro
  simp only [Parametric.Fn]
  refine forall_intro fun a => imp_intro ?_
  refine .trans (and_mono (forall_elim a) (IsLookup_domainAt Gate.step Gate.visible a)) ?_
  exact imp_elim_left.trans
    (((domainOkAt_mono Gate.visible_le_any (f a)).trans (domainOk_step ev (f a))).trans
      (domainOk_domainAt_step Gate.step ev (f a)))

/-- Constructor fields good are good thunks: one step later, the forcings of
    the freshly-thunked fields are `Con`-good at the full gate. -/
theorem con_bridge (ds : List D) :
    Parametric.Con (DomainOkAt Gate.visible) ds
      ⊢ iprop(▷ Parametric.Con DomainOk ((ds.map Later.next).map (·.car))) := by
  rw [List.map_map]
  simp only [Function.comp_def, List.map_id']
  refine .trans ?_ later_intro
  exact Parametric.Con_mono (fun a => IsLookup_domainAt Gate.visible Gate.any a) ds

/-- Stored constructor fields are `Con`-good for eval results: their look
    shape transports the gate. -/
theorem Con_visible (ds : List D) :
    Parametric.Con DomainOk ds ⊢ Parametric.Con (DomainOkAt Gate.visible) ds :=
  Parametric.Con_mono (fun a => IsLookup_domainAt Gate.any Gate.visible a) ds

/-- Monadic-bind compatibility for the productive-trace predicate, by Löb
    induction over the trace layers: binding a good trace with a continuation
    that is good at every `RetOk`-return yields a good trace. Along the bind
    only the `.any` and `.step` gates occur, and `.step` passes only a `stuck`
    return, so the continuation is spliced in at the full gate or, on a
    `stuck` value, at `.step`. `Q` carries whatever context the continuation's
    goodness needs. -/
theorem traceOk_bind (Q : SiProp) (k : VH -n> Trace VH)
    (Hk : ∀ (g : Gate) (vμ : VH), g ≠ Gate.visible →
      (g = Gate.step → vμ.1.isStuck = true) →
      iprop(Q ∧ RetOk vμ) ⊢ TraceOkAt RetOk g (k vμ))
    (g : Gate) (hg : g ≠ Gate.visible) (t : Trace VH) :
    iprop(Q ∧ TraceOkAt RetOk g t) ⊢ TraceOkAt RetOk g (Trace.bind k t) := by
  have main : ⊢ iprop(∀ (g : Gate) (t : Trace VH),
      ⌜g ≠ Gate.visible⌝ → (Q ∧ TraceOkAt RetOk g t) → TraceOkAt RetOk g (Trace.bind k t)) := by
    refine Entails.trans ?_ loeb
    refine imp_intro ?_
    refine .trans and_elim_r ?_
    refine forall_intro fun g => forall_intro fun t => imp_intro (imp_intro ?_)
    refine pure_elim (g ≠ Gate.visible) (and_elim_l.trans and_elim_r) fun hg => ?_
    rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · -- `.ret`: the gate passes the return (`.step` only a `stuck` one); splice.
      have splice : ∀ (hgs : g = Gate.step → vμ.1.isStuck = true) {P : SiProp},
          (P ⊢ Q) → (P ⊢ TraceOkAt RetOk g t) → P ⊢ TraceOkAt RetOk g (Trace.bind k t) := by
        intro hgs P hQ hT
        have hret : TraceOkAt RetOk g (Trace.ret vμ) ⊣⊢ RetOk vμ := by
          by_cases hstep : g = Gate.step
          · subst hstep
            exact traceOkAt_ret_isStuck RetOk Gate.step (hgs rfl)
          · exact traceOkAt_ret RetOk g hstep vμ
        have hR : TraceOkAt RetOk g (Trace.bind k t) ⊣⊢ TraceOkAt RetOk g (k vμ) :=
          traceOkAt_proper RetOk g
            (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
              (Trace.bind_ret k vμ))
        refine .trans ?_ hR.2
        refine .trans ?_ (Hk g vμ hg hgs)
        exact and_intro hQ (hT.trans
          ((traceOkAt_proper RetOk g (Trace.equiv_of_unfold hu).symm).trans hret).1)
      by_cases hgs : g = Gate.step
      · subst hgs
        cases hv : vμ.1.isStuck with
        | false => exact (and_elim_r.trans (and_elim_r.trans
            (traceOkAt_ret_denied_of_unfold RetOk hv hu).1)).trans false_elim
        | true =>
          exact splice (fun _ => hv) (and_elim_r.trans and_elim_l)
            (and_elim_r.trans and_elim_r)
      · exact splice (fun h => absurd h hgs) (and_elim_r.trans and_elim_l)
          (and_elim_r.trans and_elim_r)
    · -- `.step`: both sides refill the gate; recurse one step later.
      have hR : TraceOkAt RetOk g (Trace.bind k t)
          ⊣⊢ iprop(▷ (TraceOkAt RetOk Gate.any (Trace.bind k tl.car))) :=
        (traceOkAt_proper RetOk g
          (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
            (Trace.bind_step k ev tl))).trans
          (traceOkAt_step RetOk g ev _)
      refine .trans (and_mono .rfl (and_mono .rfl (traceOkAt_step_of_unfold RetOk g hu).1)) ?_
      refine .trans ?_ hR.2
      refine .trans (and_mono and_elim_l .rfl) ?_
      refine .trans (and_mono .rfl (and_mono later_intro .rfl)) ?_
      refine .trans (and_mono .rfl later_and.2) ?_
      refine .trans later_and.2 (later_mono ?_)
      refine .trans (and_mono ((forall_elim Gate.any).trans (forall_elim tl.car)) .rfl) ?_
      exact (and_mono (pure_imp_elim (by decide)) .rfl).trans imp_elim_left
    · -- `.invis`: only the full gate passes; both tails land at `.step`.
      by_cases hga : g = Gate.any
      · subst hga
        have hR : TraceOkAt RetOk Gate.any (Trace.bind k t)
            ⊣⊢ iprop(▷ (TraceOkAt RetOk Gate.step (Trace.bind k tl.car))) :=
          (traceOkAt_proper RetOk Gate.any
            (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
              (Trace.bind_invis k tl))).trans
            (traceOkAt_invis RetOk _)
        refine .trans (and_mono .rfl (and_mono .rfl (traceOkAt_invis_of_unfold RetOk hu).1)) ?_
        refine .trans ?_ hR.2
        refine .trans (and_mono and_elim_l .rfl) ?_
        refine .trans (and_mono .rfl (and_mono later_intro .rfl)) ?_
        refine .trans (and_mono .rfl later_and.2) ?_
        refine .trans later_and.2 (later_mono ?_)
        refine .trans (and_mono ((forall_elim Gate.step).trans (forall_elim tl.car)) .rfl) ?_
        exact (and_mono (pure_imp_elim (by decide)) .rfl).trans imp_elim_left
      · exact (and_elim_r.trans (and_elim_r.trans
          (traceOkAt_invis_denied_of_unfold RetOk g hga hu).1)).trans false_elim
  refine .trans (and_intro ((LR.of_empValid main).trans
    ((forall_elim g).trans (forall_elim t))) .rfl) ?_
  exact (and_mono (pure_imp_elim hg) .rfl).trans imp_elim_left

/-- A returned `stuck` against a good heap is a good trace at every gate: the
    trace has terminated, so it is trivially productive. -/
theorem traceOkAt_ret_stuck (g : Gate) (μ : Heap D) :
    HeapOk (DomainOkAt Gate.step) μ ⊢ TraceOkAt RetOk g (Trace.ret (Value.stuck, μ)) := by
  refine .trans ?_ (traceOkAt_ret_isStuck RetOk g (vμ := (Value.stuck, μ)) rfl).2
  exact and_intro true_intro .rfl

/-- The `stuck` closure, at every gate. -/
theorem domainOkAt_stuck (g : Gate) : ⊢ DomainOkAt g Domain.stuck := by
  refine .trans ?_ (domainOkAt_run g Domain.stuck).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run Value.stuck μ)).2
  exact and_elim_r.trans (traceOkAt_ret_stuck g μ)

/-- The `applyCont` continuation is good at every good return it can be
    spliced at: a returned `stuck` or constructor gets `stuck` (a good
    immediate return at every gate), and a returned function pays the guard
    `.invis` into the `.step`-gate goodness its `value` clause supplies (a
    function return only arrives at the full gate). -/
theorem traceOkAt_applyCont (da : D) (g : Gate) (vμ : VH) (hg : g ≠ Gate.visible)
    (hgs : g = Gate.step → vμ.1.isStuck = true) :
    iprop(IsLookup DomainOk da ∧ RetOk vμ) ⊢
      TraceOkAt RetOk g (D.kCont (D.applyCont da) vμ) := by
  obtain ⟨v, μ'⟩ := vμ
  show iprop(IsLookup DomainOk da ∧ RetOk (v, μ'))
    ⊢ TraceOkAt RetOk g (D.unfold (D.applyCont da v) μ')
  rcases v with _ | f | ⟨K, ds⟩
  · refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run Value.stuck μ')).2
    exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck g μ')
  · obtain rfl : g = Gate.any := by
      cases g with
      | any => rfl
      | visible => exact absurd rfl hg
      | step => exact Bool.noConfusion (hgs rfl)
    refine .trans ?_ (traceOkAt_proper RetOk Gate.any (D.invis_run (Later.next (f.car da)) μ')).2
    refine .trans ?_ (traceOkAt_invis RetOk _).2
    refine .trans (and_intro
      (and_intro
        (and_elim_r.trans and_elim_l)
        (and_elim_l.trans ((IsLookup_domainAt Gate.any Gate.step da).trans
          later_intro)))
      (and_elim_r.trans (and_elim_r.trans later_intro))) ?_
    refine .trans (and_mono later_and.2 .rfl) ?_
    refine .trans later_and.2 (later_mono ?_)
    refine .trans (and_mono (and_mono (forall_elim da) .rfl) .rfl) ?_
    refine .trans (and_mono imp_elim_left .rfl) ?_
    exact (and_intro
      (and_elim_l.trans ((domainOkAt_run Gate.step _).1.trans (forall_elim μ')))
      and_elim_r).trans imp_elim_left
  · refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run Value.stuck μ')).2
    exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck g μ')

/-- Application is a good denotation (the `apply` closure). -/
theorem apply_closed (dv da : D) :
    iprop(DomainOk dv ∧ IsLookup DomainOk da) ⊢
      DomainOk (Domain.step .app1 (Domain.apply dv da)) := by
  refine .trans ?_ (domainOk_step .app1 (Domain.apply dv da))
  show iprop(DomainOk dv ∧ IsLookup DomainOk da) ⊢ DomainOk (D.bind dv (D.applyCont da))
  refine .trans ?_ (domainOk_run (D.bind dv (D.applyCont da))).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOk_proper RetOk (D.bind_run dv (D.applyCont da) μ)).2
  refine .trans ?_ (traceOk_bind (IsLookup DomainOk da) (D.kCont (D.applyCont da))
    (traceOkAt_applyCont da) Gate.any (by decide) (D.unfold dv μ))
  exact and_intro
    (and_elim_l.trans and_elim_r)
    ((and_intro
      (and_elim_l.trans (and_elim_l.trans ((domainOk_run dv).1.trans (forall_elim μ))))
      and_elim_r).trans imp_elim_left)

/-- The `selectCont` continuation is good at every good return it can be
    spliced at: a non-constructor return or a missing constructor gets `stuck`
    (a good immediate return at every gate), and a matching branch pays the
    guard `.invis` with its leading `.case2` step, receiving the forced fields
    (`Con`-good per the stored value clause; a constructor return only arrives
    at the full gate); an arity mismatch is a stuck return behind the guard. -/
theorem traceOkAt_selectCont (alts : List (ConTag × Nat × (List D -n> D))) (g : Gate) (vμ : VH)
    (hg : g ≠ Gate.visible) (hgs : g = Gate.step → vμ.1.isStuck = true) :
    iprop(Parametric.Alts (DomainOkAt Gate.visible) alts ∧ RetOk vμ) ⊢
      TraceOkAt RetOk g (D.kCont (D.selectCont (Parametric.stepAlts alts)) vμ) := by
  obtain ⟨v, μ'⟩ := vμ
  show iprop(Parametric.Alts (DomainOkAt Gate.visible) alts ∧ RetOk (v, μ'))
    ⊢ TraceOkAt RetOk g (D.unfold (D.selectCont (Parametric.stepAlts alts) v) μ')
  rcases v with _ | f | ⟨K, ds⟩
  · refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run Value.stuck μ')).2
    exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck g μ')
  · refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run Value.stuck μ')).2
    exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck g μ')
  · obtain rfl : g = Gate.any := by
      cases g with
      | any => rfl
      | visible => exact absurd rfl hg
      | step => exact Bool.noConfusion (hgs rfl)
    show iprop(Parametric.Alts (DomainOkAt Gate.visible) alts ∧ RetOk (Value.con K ds, μ'))
      ⊢ TraceOkAt RetOk Gate.any
          (D.unfold (D.selectCont (Parametric.stepAlts alts) (Value.con K ds)) μ')
    rw [D.selectCont_stored (Parametric.stepAlts alts) K ds]
    rcases hfind : (Parametric.stepAlts alts).find? (·.1 == K) with _ | p
    all_goals rw [hfind]
    · refine .trans ?_ (traceOkAt_proper RetOk Gate.any (D.ret_run Value.stuck μ')).2
      exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck Gate.any μ')
    · obtain ⟨q, hq, hp⟩ : ∃ q ∈ alts,
          (q.1, q.2.1, ofe_fun dsx =>
            if dsx.length = q.2.1 then Domain.step .case2 (q.2.2 dsx)
            else Domain.stuck) = p := by
        have hmem := List.mem_of_find?_eq_some hfind
        simpa only [Parametric.stepAlts, List.mem_map] using hmem
      dsimp only [Option.elim]
      by_cases hlen : (ds.map (·.car)).length = q.2.1
      · -- matching arity: the branch's leading `.case2` pays the guard
        have hbr : p.2.2 (ds.map (·.car))
            = Domain.step .case2 (q.2.2 (ds.map (·.car))) := by
          rw [← hp]
          exact if_pos hlen
        rw [hbr]
        refine .trans ?_ (traceOkAt_proper RetOk Gate.any (D.invis_run _ μ')).2
        refine .trans ?_ (traceOkAt_invis RetOk _).2
        refine .trans (and_intro ?_ (and_elim_r.trans (and_elim_r.trans later_intro)))
          (later_and.2.trans (later_mono ((and_intro
            (and_elim_l.trans ((domainOkAt_run Gate.step _).1.trans (forall_elim μ')))
            and_elim_r).trans imp_elim_left)))
        refine .trans (and_intro
          (and_elim_l.trans (BigAndL.bigAndL_mem hq))
          (and_elim_r.trans (and_elim_l.trans
            (later_mono (Con_visible (ds.map (·.car))))))) ?_
        refine .trans (and_mono later_intro .rfl) ?_
        refine .trans later_and.2 (later_mono ?_)
        refine .trans (and_mono (forall_elim (ds.map (·.car))) .rfl) ?_
        exact (imp_elim_left.trans
          ((domainOkAt_mono Gate.visible_le_any _).trans (domainOk_step .case2 _))).trans
          (domainOk_domainAt_step Gate.step .case2 _)
      · -- arity mismatch: the branch is a stuck return behind the guard
        have hbr : p.2.2 (ds.map (·.car)) = Domain.stuck := by
          rw [← hp]
          exact if_neg hlen
        rw [hbr]
        refine .trans ?_ (traceOkAt_proper RetOk Gate.any (D.invis_run _ μ')).2
        refine .trans ?_ (traceOkAt_invis RetOk _).2
        refine .trans ?_ later_intro
        refine .trans ?_ (traceOkAt_proper RetOk Gate.step (D.ret_run Value.stuck μ')).2
        exact (and_elim_r.trans and_elim_r).trans (traceOkAt_ret_stuck Gate.step μ')

/-- Case selection is a good denotation (the `select` closure). -/
theorem select_closed (dv : D) (alts : List (ConTag × Nat × (List D -n> D))) :
    iprop(DomainOk dv ∧ Parametric.Alts (DomainOkAt Gate.visible) alts) ⊢
      DomainOk (Domain.step .case1 (Domain.select dv (Parametric.stepAlts alts))) := by
  refine .trans ?_ (domainOk_step .case1 (Domain.select dv (Parametric.stepAlts alts)))
  show iprop(DomainOk dv ∧ Parametric.Alts (DomainOkAt Gate.visible) alts)
    ⊢ DomainOk (D.bind dv (D.selectCont (Parametric.stepAlts alts)))
  refine .trans ?_ (domainOk_run (D.bind dv (D.selectCont (Parametric.stepAlts alts)))).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOk_proper RetOk
    (D.bind_run dv (D.selectCont (Parametric.stepAlts alts)) μ)).2
  refine .trans ?_ (traceOk_bind (Parametric.Alts (DomainOkAt Gate.visible) alts)
    (D.kCont (D.selectCont (Parametric.stepAlts alts))) (traceOkAt_selectCont alts)
    Gate.any (by decide) (D.unfold dv μ))
  exact and_intro
    (and_elim_l.trans and_elim_r)
    ((and_intro
      (and_elim_l.trans (and_elim_l.trans ((domainOk_run dv).1.trans (forall_elim μ))))
      and_elim_r).trans imp_elim_left)

/-! ## Recursive `let` (the `bind` closure)

`bindLet` allocates a fresh cell holding `D.memo a (▶(rhs thunk))` and runs the
body on `thunk := fetch a`. The pieces: forcing the thunk spends the guard
`.invis` against the entry's `.step`-gate goodness (`domain_fetch`); the
memoized entry is `.step`-gate good by Löb induction over forcings
(`memoInv_valid`), using the rhs's `.visible` gate at the first force and
re-entering the invariant at the memoized value on `.update`. -/

/-- `Later`'s `Equiv` is `Equiv` of the payloads. -/
theorem later_equiv_car {α : Type _} [OFE α] {x y : Later α} (h : x ≡ y) :
    x.car ≡ y.car := h

/-- A `value`-good return is a good denotation at every gate that passes a
    return. -/
theorem domainOkAt_ret (g : Gate) (hg : g ≠ Gate.step) (v : Value D) :
    ValueOk DomainOkAt v ⊢ DomainOkAt g (D.ret v) := by
  refine .trans ?_ (domainOkAt_run g (D.ret v)).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOkAt_proper RetOk g (D.ret_run v μ)).2
  refine .trans ?_ (traceOkAt_ret RetOk g hg (v, μ)).2
  exact and_intro and_elim_l and_elim_r

/-- Extending a good heap with a good entry keeps it good. -/
theorem heapOk_set (P : D -n> SiProp) (μ : Heap D) (a : Addr) (dl : Later D) :
    iprop(HeapOk P μ ∧ ▷ (P dl.car)) ⊢ HeapOk P (Heap.set μ a dl) := by
  show _ ⊢ iprop(∀ k, EntryOk P ((Heap.set μ a dl).car k))
  refine forall_intro fun k => ?_
  rw [Heap.set_get μ a dl k]
  by_cases hk : a = k
  · rw [if_pos hk]
    exact and_elim_r
  · rw [if_neg hk]
    exact and_elim_l.trans (forall_elim k)

/-- The thunk a `let` binds is good: forcing it spends the single `.invis`
    that opens the stored `▶D`, and an unbound address rets `stuck`. -/
theorem domainOk_fetch (a : Addr) : ⊢ DomainOk (fetch a) := by
  refine .trans ?_ (domainOk_run (fetch a)).2
  refine forall_intro fun μ => imp_intro ?_
  rcases hμa : μ.car a with _ | dl
  · refine .trans ?_ (traceOk_proper RetOk (fetch_run_none hμa)).2
    exact and_elim_r.trans (traceOkAt_ret_stuck Gate.any μ)
  · refine .trans ?_ (traceOk_proper RetOk (fetch_run_some hμa)).2
    refine .trans ?_ (traceOk_invis RetOk _).2
    have hent : iprop(∀ k, EntryOk (DomainOkAt Gate.step) (μ.car k))
        ⊢ iprop(▷ (DomainOkAt Gate.step dl.car)) := by
      refine (forall_elim a).trans ?_
      rw [hμa]
      exact .rfl
    refine .trans (and_intro (and_elim_r.trans hent) (and_elim_r.trans later_intro)) ?_
    refine .trans later_and.2 (later_mono ?_)
    exact (and_intro
      (and_elim_l.trans ((domainOkAt_run Gate.step dl.car).1.trans (forall_elim μ)))
      and_elim_r).trans imp_elim_left

/-- The invariant Löb-recursed for memoized entries at cell `a`: binding any
    computation good at the `.visible` gate with the cell's update continuation
    is a good `.step`-gate entry. -/
def MemoInv (a : Addr) : SiProp :=
  iprop(∀ X : D, DomainOkAt Gate.visible X →
    DomainOkAt Gate.step (D.bind X (D.memo.cont a (D.memo a))))

/-- The update continuation of a memoized cell is good at every good return, at
    every gate: a `stuck` result is returned untouched (good at every gate),
    and a value's `.update` step refills the gate, the rewritten cell holding
    the memoized value, a good entry by the invariant. -/
theorem traceOkAt_memoCont (a : Addr) (v : Value D) (μ : Heap D) (g : Gate) :
    iprop(▷ (MemoInv a) ∧ RetOk (v, μ)) ⊢
      TraceOkAt RetOk g (D.kCont (D.memo.cont a (D.memo a)) (v, μ)) := by
  cases hv : v.isStuck with
  | true =>
    obtain rfl : v = Value.stuck := by
      cases v <;> first | rfl | exact Bool.noConfusion hv
    refine .trans ?_ (traceOkAt_proper RetOk g (D.memoCont_run_stuck a (D.memo a) μ)).2
    exact and_elim_r.trans (and_elim_r.trans (traceOkAt_ret_stuck g μ))
  | false =>
    refine .trans ?_ (traceOkAt_proper RetOk g (D.memoCont_run a (D.memo a) hv μ)).2
    refine .trans ?_ (traceOkAt_step RetOk g .update _).2
    refine .trans (and_mono .rfl later_intro) ?_
    refine .trans later_and.2 (later_mono ?_)
    refine .trans ?_ (traceOk_ret RetOk (v, Heap.set μ a (D.memo a (Later.next (D.ret v))))).2
    refine and_intro (and_elim_r.trans and_elim_l) ?_
    refine .trans (and_intro (and_elim_r.trans and_elim_r) ?_)
      (heapOk_set (DomainOkAt Gate.step) μ a _)
    refine .trans ?_ later_intro
    refine .trans ?_
      (domainOkAt_proper Gate.step
        (later_equiv_car ((D.memo_unfold a) (Later.next (D.ret v))))).2
    refine .trans (and_intro (and_elim_l.trans (forall_elim (D.ret v)))
      (and_elim_r.trans (and_elim_l.trans (domainOkAt_ret Gate.visible (by decide) v))))
      imp_elim_left

/-- Every memoized binding is a good `.step`-gate heap entry, by Löb induction
    over forcings: the stored computation's `.visible` gate leaves a return
    (the continuation splices in, rewriting the cell to the memoized value,
    which re-enters the invariant) or a visible step (recurse across it via
    `trace_bind`); a silent head is denied outright. -/
theorem memoInv_valid (a : Addr) : ⊢ MemoInv a := by
  refine .trans ?_ loeb
  refine imp_intro ?_
  refine .trans and_elim_r ?_
  refine forall_intro fun X => imp_intro ?_
  refine .trans ?_ (domainOkAt_run Gate.step (D.bind X (D.memo.cont a (D.memo a)))).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOkAt_proper RetOk Gate.step
    (D.bind_run X (D.memo.cont a (D.memo a)) μ)).2
  have htr : iprop((▷ MemoInv a ∧ DomainOkAt Gate.visible X) ∧ HeapOk (DomainOkAt Gate.step) μ)
      ⊢ TraceOkAt RetOk Gate.visible (D.unfold X μ) :=
    (and_intro (and_elim_l.trans (and_elim_r.trans
        ((domainOkAt_run Gate.visible X).1.trans (forall_elim μ)))) and_elim_r).trans
      imp_elim_left
  rcases hu : Trace.unfold (D.unfold X μ) with vμ' | ⟨ev, tl⟩ | tl
  · -- the stored computation returns immediately: the continuation splices in
    have hR : TraceOkAt RetOk Gate.step
          (Trace.bind (D.kCont (D.memo.cont a (D.memo a))) (D.unfold X μ))
        ⊣⊢ TraceOkAt RetOk Gate.step (D.kCont (D.memo.cont a (D.memo a)) vμ') :=
      traceOkAt_proper RetOk Gate.step
        (((Trace.bind (D.kCont (D.memo.cont a (D.memo a)))).ne.eqv
          (Trace.equiv_of_unfold hu).symm).trans
          (Trace.bind_ret (D.kCont (D.memo.cont a (D.memo a))) vμ'))
    refine .trans ?_ hR.2
    refine .trans ?_ (traceOkAt_memoCont a vμ'.1 vμ'.2 Gate.step)
    exact and_intro (and_elim_l.trans and_elim_l)
      (htr.trans (traceOkAt_ret_of_unfold RetOk Gate.visible (by decide) hu).1)
  · -- the stored computation steps: recurse via `trace_bind` under the `▷`
    have hR : TraceOkAt RetOk Gate.step
          (Trace.bind (D.kCont (D.memo.cont a (D.memo a))) (D.unfold X μ))
        ⊣⊢ iprop(▷ (TraceOkAt RetOk Gate.any
            (Trace.bind (D.kCont (D.memo.cont a (D.memo a))) tl.car))) :=
      (traceOkAt_proper RetOk Gate.step
        (((Trace.bind (D.kCont (D.memo.cont a (D.memo a)))).ne.eqv
          (Trace.equiv_of_unfold hu).symm).trans
          (Trace.bind_step (D.kCont (D.memo.cont a (D.memo a))) ev tl))).trans
        (traceOkAt_step RetOk Gate.step ev _)
    refine .trans ?_ hR.2
    refine .trans (and_intro (and_elim_l.trans and_elim_l)
      (htr.trans (traceOkAt_step_of_unfold RetOk Gate.visible hu).1)) ?_
    refine .trans later_and.2 (later_mono ?_)
    exact traceOk_bind (MemoInv a) (D.kCont (D.memo.cont a (D.memo a)))
      (fun g' vμ _ _ => (and_mono later_intro .rfl).trans (traceOkAt_memoCont a vμ.1 vμ.2 g'))
      Gate.any (by decide) tl.car
  · -- a silent head: the `.visible` gate denies it
    exact (htr.trans
      (traceOkAt_invis_denied_of_unfold RetOk Gate.visible (by decide) hu).1).trans
      false_elim

/-- Recursive `let` is a good denotation (the `bind` closure). -/
theorem bind (rhs body : D -n> D) :
    iprop((∀ a, DomainOk a → DomainOkAt Gate.visible (rhs a)) ∧
        (∀ a, DomainOk a → DomainOkAt Gate.visible (body a)))
      ⊢ DomainOkAt Gate.visible (Domain.step .let1 (Domain.bind rhs body)) := by
  refine .trans ?_ (domainOk_domainAt_step Gate.visible .let1 (Domain.bind rhs body))
  refine .trans ?_ (domainOk_step .let1 (Domain.bind rhs body))
  show _ ⊢ DomainOk (D.bindLet rhs body)
  refine .trans ?_ (domainOk_run (D.bindLet rhs body)).2
  refine forall_intro fun μ => imp_intro ?_
  refine .trans ?_ (traceOk_proper RetOk (D.bindLet_run rhs body μ)).2
  -- the body is good, fed the raw thunk
  have hbody : iprop((∀ a, DomainOk a → DomainOkAt Gate.visible (rhs a)) ∧
        (∀ a, DomainOk a → DomainOkAt Gate.visible (body a)))
      ⊢ DomainOk (body (fetch (Heap.nextFree μ))) := by
    refine .trans and_elim_r ?_
    refine .trans (forall_elim (fetch (Heap.nextFree μ))) ?_
    refine .trans (and_intro .rfl (LR.of_empValid (domainOk_fetch (Heap.nextFree μ)))) ?_
    exact imp_elim_left.trans (domainOkAt_mono Gate.visible_le_any _)
  -- the extended heap is good: the memoized entry re-enters the invariant
  have hheap : iprop(((∀ a, DomainOk a → DomainOkAt Gate.visible (rhs a)) ∧
        (∀ a, DomainOk a → DomainOkAt Gate.visible (body a)))
        ∧ HeapOk (DomainOkAt Gate.step) μ)
      ⊢ HeapOk (DomainOkAt Gate.step) (Heap.set μ (Heap.nextFree μ) (D.memo (Heap.nextFree μ)
          (Later.next (rhs (fetch (Heap.nextFree μ)))))) := by
    refine .trans (and_intro and_elim_r ?_)
      (heapOk_set (DomainOkAt Gate.step) μ (Heap.nextFree μ) _)
    refine .trans ?_ later_intro
    refine .trans ?_ (domainOkAt_proper Gate.step (later_equiv_car
      ((D.memo_unfold (Heap.nextFree μ))
        (Later.next (rhs (fetch (Heap.nextFree μ))))))).2
    refine .trans (and_intro
      (LR.of_empValid ((memoInv_valid (Heap.nextFree μ)).trans
        (forall_elim (rhs (fetch (Heap.nextFree μ)))))) ?_) imp_elim_left
    refine .trans (and_elim_l.trans and_elim_l) ?_
    refine .trans (forall_elim (fetch (Heap.nextFree μ))) ?_
    exact (and_intro .rfl (LR.of_empValid (domainOk_fetch (Heap.nextFree μ)))).trans
      imp_elim_left
  refine .trans (and_intro
    (and_elim_l.trans (hbody.trans ((domainOk_run _).1.trans (forall_elim _)))) hheap)
    imp_elim_left

def lr : LR SiProp D where
  P := DomainOkAt Gate.visible
  IsThunk := DomainOk
  IsThunk_to_P := fun x a =>
    (domainOk_step (.look x) a).trans (domainOk_domainAt_step Gate.visible (.look x) a)
  stuck := domainOkAt_stuck Gate.visible
  fn := fun _ f => by
    refine .trans ?_ (domainOkAt_run Gate.visible (D.fn ((Domain.step .app2).comp f))).2
    refine forall_intro fun μ => imp_intro ?_
    refine .trans ?_ (traceOkAt_proper RetOk Gate.visible
      (D.fn_run ((Domain.step .app2).comp f) μ)).2
    refine .trans ?_ (traceOkAt_ret RetOk Gate.visible (by decide)
      (Value.fn (Later.next ((Domain.step .app2).comp f)), μ)).2
    exact and_intro (and_elim_l.trans (fn_bridge .app2 f)) and_elim_r
  con := fun K ds => by
    refine .trans ?_ (domainOkAt_run Gate.visible (D.con K ds)).2
    refine forall_intro fun μ => imp_intro ?_
    refine .trans ?_ (traceOkAt_proper RetOk Gate.visible (D.con_run K ds μ)).2
    refine .trans ?_ (traceOkAt_ret RetOk Gate.visible (by decide)
      (Value.con K (ds.map Later.next), μ)).2
    exact and_intro (and_elim_l.trans (con_bridge ds)) and_elim_r
  apply := fun dv da =>
    ((and_mono (domainOkAt_mono Gate.visible_le_any dv)
      (IsLookup_domainAt Gate.visible Gate.any da)).trans (apply_closed dv da)).trans
      (domainOk_domainAt_step Gate.visible .app1 (Domain.apply dv da))
  select := fun dv alts =>
    ((and_mono (domainOkAt_mono Gate.visible_le_any dv) .rfl).trans
      (select_closed dv alts)).trans
      (domainOk_domainAt_step Gate.visible .case1 (Domain.select dv (Parametric.stepAlts alts)))
  bind := bind

/-! ## Extraction: pure productivity of closed programs

The logical relation lives in `SiProp`; its payoff is a pure statement about
the trace itself. `PureTraceOkAt` is the fuel-indexed shadow of `TraceOkAt` on plain
`Prop` (one fuel per layer, matching the step index each `▷` burns), extracted
from `holds` through the `traceOkAt_ret/step/invis` reductions. The headline: in
the trace of a closed program, silent layers never run two in a row, so at
most two step indices are burnt between consecutive visible steps. -/

/-- The fuel-indexed pure shadow of `TraceOkAt`: unrolling `n` layers from gate
    `g`, a return passes every gate (`.step` only with a `stuck` value), a
    visible step refills the gate, a silent step passes only the full gate and
    lands at `.step`. -/
def PureTraceOkAt : Nat → Gate → Trace VH → Prop
  | 0, _, _ => True
  | n+1, g, t =>
    match Trace.unfold t with
    | .ret vμ => g = Gate.step → vμ.1.isStuck = true
    | .step _ tl => PureTraceOkAt n Gate.any tl.car
    | .invis tl => g = Gate.any ∧ PureTraceOkAt n Gate.step tl.car

/-- Extraction: a trace the step-indexed predicate accepts at index `n` is
    `PureTraceOkAt` for `n` layers (each layer's `▷` burns one index). -/
theorem pureTraceOkAt_of_holds (Ret : VH -n> SiProp) :
    ∀ (n : Nat) (g : Gate) (t : Trace VH),
      (TraceOkAt Ret g t).holds n → PureTraceOkAt n g t := by
  intro n
  induction n with
  | zero => intro g t _; trivial
  | succ n ih =>
    intro g t H
    show (match Trace.unfold t with
      | .ret vμ => g = Gate.step → vμ.1.isStuck = true
      | .step _ tl => PureTraceOkAt n Gate.any tl.car
      | .invis tl => g = Gate.any ∧ PureTraceOkAt n Gate.step tl.car)
    rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · intro hg
      subst hg
      cases hv : vμ.1.isStuck with
      | false =>
        exact (((equiv_iff.mpr
          (traceOkAt_ret_denied_of_unfold Ret hv hu)).mp H : False)).elim
      | true => rfl
    · have h2 : (TraceOkAt Ret Gate.any tl.car).holds n :=
        (equiv_iff.mpr (traceOkAt_step_of_unfold Ret g hu)).mp H
      exact ih Gate.any tl.car h2
    · by_cases hg : g = Gate.any
      · subst hg
        have h2 : (TraceOkAt Ret Gate.step tl.car).holds n :=
          (equiv_iff.mpr (traceOkAt_invis_of_unfold Ret hu)).mp H
        exact ⟨rfl, ih Gate.step tl.car h2⟩
      · exact (((equiv_iff.mpr (traceOkAt_invis_denied_of_unfold Ret g hg hu)).mp H
          : False)).elim

/-- A suffix of a trace: what remains after peeling finitely many layers. -/
inductive Suffix : Trace VH → Trace VH → Prop
  | refl (t : Trace VH) : Suffix t t
  | step {t : Trace VH} {ev : Event} {tl : Later (Trace VH)} {t' : Trace VH} :
      Trace.unfold t = .step ev tl → Suffix tl.car t' → Suffix t t'
  | invis {t : Trace VH} {tl : Later (Trace VH)} {t' : Trace VH} :
      Trace.unfold t = .invis tl → Suffix tl.car t' → Suffix t t'

/-- `PureTraceOkAt` at every fuel transports to suffixes (at the gate the path
    leaves behind). -/
theorem pureTraceOkAt_suffix {t t' : Trace VH} (hs : Suffix t t') :
    ∀ g, (∀ n, PureTraceOkAt n g t) → ∃ g', ∀ n, PureTraceOkAt n g' t' := by
  induction hs with
  | refl t => exact fun g h => ⟨g, h⟩
  | @step t ev tl t' hu _ ih =>
    refine fun g h => ih Gate.any fun n => ?_
    have h' : (match Trace.unfold t with
      | .ret vμ => g = Gate.step → vμ.1.isStuck = true
      | .step _ tl => PureTraceOkAt n Gate.any tl.car
      | .invis tl => g = Gate.any ∧ PureTraceOkAt n Gate.step tl.car) := h (n+1)
    rw [hu] at h'
    exact h'
  | @invis t tl t' hu _ ih =>
    refine fun g h => ih Gate.step fun n => ?_
    have h' : (match Trace.unfold t with
      | .ret vμ => g = Gate.step → vμ.1.isStuck = true
      | .step _ tl => PureTraceOkAt n Gate.any tl.car
      | .invis tl => g = Gate.any ∧ PureTraceOkAt n Gate.step tl.car) := h (n+1)
    rw [hu] at h'
    exact h'.2

/-- `t` opens with two consecutive silent layers. -/
def TwoInvis (t : Trace VH) : Prop :=
  ∃ (tl₁ tl₂ : Later (Trace VH)),
    Trace.unfold t = .invis tl₁ ∧
    Trace.unfold tl₁.car = .invis tl₂

/-- Two layers of `PureTraceOkAt` refute two consecutive silent layers: the first
    lands the gate at `.step`, which denies the second. -/
theorem pureTraceOkAt_no_twoInvis {g : Gate} {t : Trace VH}
    (h : PureTraceOkAt 2 g t) : ¬ TwoInvis t := by
  rintro ⟨tl₁, tl₂, h₁, h₂⟩
  have h' : (match Trace.unfold t with
    | .ret vμ => g = Gate.step → vμ.1.isStuck = true
    | .step _ tl => PureTraceOkAt 1 Gate.any tl.car
    | .invis tl => g = Gate.any ∧ PureTraceOkAt 1 Gate.step tl.car) := h
  rw [h₁] at h'
  have h'' : (match Trace.unfold tl₁.car with
    | .ret vμ => Gate.step = Gate.step → vμ.1.isStuck = true
    | .step _ tl => PureTraceOkAt 0 Gate.any tl.car
    | .invis tl => Gate.step = Gate.any ∧ PureTraceOkAt 0 Gate.step tl.car) := h'.2
  rw [h₂] at h''
  exact absurd h''.1 (by decide)

/-- **Productivity.** In the by-need trace of a closed program, silent layers
    never run two in a row: from any point of the trace, the next visible
    step or the final return arrives within two layer unfoldings, so at most
    two step indices are burnt between consecutive visible steps. Via the
    fundamental lemma at the `lr` instance, run on the empty environment and
    heap. -/
theorem productivity (e : Exp) {t' : Trace VH}
    (hs : Suffix (D.unfold (eval e ρ₀) μ₀) t') : ¬ TwoInvis t' := by
  have HP : ⊢ DomainOkAt Gate.visible (eval e ρ₀) :=
    (LR.envOk_empty lr).trans (LR.fundamental lr e ρ₀)
  have Hμ₀ : ⊢ HeapOk (DomainOkAt Gate.step) μ₀ :=
    forall_intro fun _ => true_intro
  have Ht : ⊢ TraceOk RetOk (D.unfold (eval e ρ₀) μ₀) :=
    (and_intro
      ((HP.trans (domainOkAt_mono Gate.visible_le_any _)).trans
        ((domainOk_run (eval e ρ₀)).1.trans (forall_elim μ₀)))
      Hμ₀).trans imp_elim_left
  have Hh : ∀ n, (TraceOk RetOk (D.unfold (eval e ρ₀) μ₀)).holds n :=
    fun n => (LR.of_empValid Ht (P := iprop(True))) n trivial
  obtain ⟨g', hg'⟩ := pureTraceOkAt_suffix hs Gate.any
    (fun n => pureTraceOkAt_of_holds RetOk n Gate.any (D.unfold (eval e ρ₀) μ₀) (Hh n))
  exact pureTraceOkAt_no_twoInvis (hg' 2)

end Productive

end AbsDen
