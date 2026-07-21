import AbsDen.NeedSound

/-! # Usage analysis approximates the by-need semantics (`thm:absence`)

The `Prop`-level reading of the soundness theorem, in the Galois-connection
form of the paper: the trace representation of the by-need denotation is below
the analysis result, `β(⟦e⟧_need) ⊑ ⟦e⟧_usage`.

The trace representation `β` is the fold `α_S` of `fig:abstract-name-need`
over the trace, which has no direct meaning on an infinite trace. Following
`sec:safety-extension`, `β` is the least upper bound of its finite-depth
approximants `Trace.βn n`, computed as a `csup`: the *representation
function* of the Galois connection. Because "`β(t) ⊑ dh`" is a safety
property, `β(t)` is the least `dh` bounding every finite prefix. Soundness
produces `β(⟦e⟧_need) ⊑ ⟦e⟧_usage` directly; the number of `look x` events in
any prefix is read off the approximants, and `absence` is the corollary at
usage `u0`: a variable the analysis reports absent is never looked up.

Producing the prefix bounds from the by-need relation `Rel` runs it down a
prefix: each unfolded layer sits under one `|==> ▷`, so an `n`-prefix fact
surfaces under the modality tower `(|==> ▷)^n`, sound to strip at the `UPred`
model seeded with the authoritative empty ghost table. -/

open Iris Iris.BI Iris.COFE OFE CMRA

namespace AbsDen

/-! ## The look count of a trace prefix -/

/-- Clamp a count into a usage: none, once, or many. -/
def U.ofCount : Nat → U
  | 0 => .u0
  | 1 => .u1
  | _ => .uω

theorem U.ofCount_succ_le (c : Nat) :
    U.ofCount (1 + c) ⊑ U.u1 + U.ofCount c := by
  rcases c with _ | _ | c
  · decide
  · decide
  · show U.uω ⊑ U.u1 + U.uω
    decide

/-- Only a zero count clamps below `u0`. -/
theorem U.ofCount_le_u0 : ∀ {c : Nat}, U.ofCount c ⊑ U.u0 → c = 0
  | 0, _ => rfl
  | 1, h => absurd h (by decide)
  | _ + 2, h => absurd h (by decide : ¬ U.uω ⊑ U.u0)

/-- Only counts up to one clamp below `u1`. -/
theorem U.ofCount_le_u1 : ∀ {c : Nat}, U.ofCount c ⊑ U.u1 → c ≤ 1
  | 0, _ => Nat.zero_le _
  | 1, _ => Nat.le_refl _
  | _ + 2, h => absurd h (by decide : ¬ U.uω ⊑ U.u1)

/-- The number of `look x` events in the first `n` layers of a trace. -/
def Trace.lookCount (x : Var) : Nat → Trace VH → Nat
  | 0, _ => 0
  | n + 1, t =>
    match Trace.unfold t with
    | .ret _ => 0
    | .step ev tl => (if ev = .look x then 1 else 0) + Trace.lookCount x n tl.car
    | .invis tl => Trace.lookCount x n tl.car

/-! ## The trace representation and its safety extension

`Trace.βn n t` is the paper's trace representation `α_S` folded to depth `n`:
a returned value ends the fold at `stuck`, a visible `step ev` charges its
abstract step, a silent step passes through. The full representation `Trace.β`
is their least upper bound (`csup`) -- the representation function `β` of the
Galois connection, and the least `dh` bounding every finite prefix. -/

variable {V : Type} [AbstractDomain V] [Lat V]

/-- The representation `β` folded to depth `n` (the `α_S` fold of `fig:abstract-name-need`). -/
def Trace.βn : Nat → Trace VH → V
  | 0, _ => AbstractDomain.stuck
  | n + 1, t =>
    match Trace.unfold t with
    | .ret _ => AbstractDomain.stuck
    | .step ev tl => AbstractDomain.step ev (Trace.βn n tl.car)
    | .invis tl => Trace.βn n tl.car

/-- The trace representation `β`: the least upper bound of the finite-depth
    folds, the representation function of the Galois connection. -/
noncomputable def Trace.β [ChainComplete V] (t : Trace VH) : V :=
  csup (fun n => Trace.βn n t)

/-! ## Soundness of the `(|==> ▷)^n` modality tower

Each unfolded trace layer of `Rel` sits under one basic update and one
later. The tower strips at the `UPred` model: updates are run against the
empty frame and laters spend one step index, so a pure fact under an
`n`-tower holds outright once the seed resource is valid at index `n`. -/

section BupdLaterN

variable {M : Type _} [UCMRA M]

/-- `n` layers of `|==> ▷`. -/
def bupdLaterN : Nat → UPred M → UPred M
  | 0, P => P
  | n + 1, P => iprop(|==> ▷ bupdLaterN n P)

theorem bupdLaterN_intro : ∀ (n : Nat) (P : UPred M), P ⊢ bupdLaterN n P
  | 0, _ => .rfl
  | n + 1, P => ((bupdLaterN_intro n P).trans later_intro).trans bupd_intro

theorem bupdLaterN_mono {P Q : UPred M} (h : P ⊢ Q) :
    ∀ n : Nat, bupdLaterN n P ⊢ bupdLaterN n Q
  | 0 => h
  | n + 1 => bupd_mono (later_mono (bupdLaterN_mono h n))

theorem bupdLaterN_pure_soundness {φ : Prop} :
    ∀ (n : Nat) (x : ValidAt M n), (bupdLaterN n (iprop(⌜φ⌝) : UPred M)).holds n x → φ
  | 0, _, h => h
  | n + 1, x, h => by
    have hval : ✓{n + 1} (x.val • (unit : M)) :=
      validN_ne (OFE.equiv_dist.mp (comm.trans unit_left_id) _).symm x.property
    obtain ⟨x', hval', hP⟩ := h (n + 1) unit (Nat.le_refl _) hval
    exact bupdLaterN_pure_soundness n _ hP

/-- A pure fact under an `n`-tower, established from a valid seed resource,
    holds outright. -/
theorem ownM_bupdLaterN_soundness {m : M} {φ : Prop} (n : Nat) (hv : ✓{n} m)
    (h : UPred.ownM m ⊢ bupdLaterN n (iprop(⌜φ⌝) : UPred M)) : φ :=
  bupdLaterN_pure_soundness n ⟨m, hv⟩ (h n ⟨m, hv⟩ (incN_refl m))

end BupdLaterN

/-! ## Reading the look count off the representation

Each `look x` in the representation charges `singenv x .u1` against the usage, so
the clamped count of the first `n` layers is below the representation's usage at
`x`. This is the finitary Galois connection on the syntactic side. -/

theorem βn_lookCount {k : Nat} (x : Var) :
    ∀ (n : Nat) (t : Trace VH),
      U.ofCount (Trace.lookCount x n t) ⊑ (Trace.βn n t : UDk k).uses !? x
  | 0, t => U.u0_le _
  | n + 1, t => by
    rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · rw [show Trace.lookCount x (n + 1) t = 0 by simp only [Trace.lookCount, hu]]
      exact U.u0_le _
    · have hc := βn_lookCount (k := k) x n tl.car
      rw [show Trace.lookCount x (n + 1) t
          = (if ev = .look x then 1 else 0) + Trace.lookCount x n tl.car by
        simp only [Trace.lookCount, hu]]
      simp only [Trace.βn, hu]
      by_cases hev : ev = .look x
      · subst hev
        rw [UDk.step_look_uses, Uses.get_add, Uses.get_singenv_self, if_pos rfl]
        exact U.le_trans (U.ofCount_succ_le _) (U.add_mono (U.le_refl _) hc)
      · rw [UDk.step_uses_get_ne hev, if_neg hev, Nat.zero_add]
        exact hc
    · rw [show Trace.lookCount x (n + 1) t = Trace.lookCount x n tl.car by
        simp only [Trace.lookCount, hu]]
      simp only [Trace.βn, hu]
      exact βn_lookCount x n tl.car

/-! ## Producing the representation from the relation -/

/-- Running `Rel` down an `n`-prefix produces the depth-`n` representation bound,
    under one `|==> ▷` per layer: each visible step charges its abstract step
    (`Step` monotone) against the bound, each silent step passes it on. -/
theorem rel_βn {k : Nat} {L : List Var} :
    ∀ (n : Nat) (dh : UDk k) (t : Trace VH),
      Need.Rel (V := UDk k) L dh t ⊢
        bupdLaterN n (iprop(⌜Trace.βn n t ⊑ dh⌝) : NeedProp (UDk k))
  | 0, dh, t => pure_intro (UDk.stuck_le dh)
  | n + 1, dh, t => by
    rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · exact .trans (pure_intro (by simp only [Trace.βn, hu]; exact UDk.stuck_le dh))
        (bupdLaterN_intro (n + 1) _)
    · refine .trans (Need.rel_step_of_unfold dh hu).1 ?_
      refine exists_elim fun dh' => ?_
      refine pure_elim (AbstractDomain.step (D := UDk k) ev dh' ≤ dh) and_elim_l
        fun hstep => ?_
      refine and_elim_r.trans (bupd_mono (later_mono
        ((rel_βn n dh' tl.car).trans (bupdLaterN_mono (pure_mono ?_) n))))
      intro hc
      simp only [Trace.βn, hu]
      exact le_iff_le.mp (Std.IsPreorder.le_trans _ _ _
        (le_iff_le.mpr (UDk.step_mono ev hc)) hstep)
    · refine .trans (Need.rel_invis_of_unfold dh hu).1 ?_
      refine bupd_mono (later_mono
        ((rel_βn n dh tl.car).trans (bupdLaterN_mono (pure_mono ?_) n)))
      intro hc
      simp only [Trace.βn, hu]
      exact hc

/-! ## Seeding the invariant at the empty heap -/

/-- The authoritative empty table establishes the invariant at the empty
    heap: nothing is allocated on either side. -/
theorem heapInv_init [AbstractDomain V'] [Lat V'] {L' : List Var} :
    HeapAbsAuth (∅ : HeapAbs V') ⊢
      Need.HeapInv (Need.Rel (V := V') L') (μ₀ : Heap D) := by
  refine .trans ?_ (Need.heapInv_eq _ μ₀).2
  refine .trans ?_ (exists_intro (∅ : HeapAbs V'))
  refine .trans sep_emp.2 (sep_mono .rfl ?_)
  refine forall_intro fun a => ?_
  rw [Std.LawfulPartialMap.get?_empty (k := a), show (μ₀ : Heap D).car a = none from rfl]
  exact true_intro

/-- The soundness entailment for a closed Barendregt program: every
    hypothesis is discharged. -/
theorem usage_abstracts_need_closed (k : Nat) (e : Exp) (hb : Barendregt e) :
    ⊢ Need.SoundR (V := UDk k) e.letBV
        (evalByNeed e Env.empty) (evalUsgk k e Env.empty) :=
  (LR2.envOk_empty (Need.soundLR2 (usageAbstractionLaws k) e.letBV)).trans
    (usage_abstracts_need k e hb Env.empty Env.empty EnvPred.empty)

/-! ## The theorem (`thm:absence`) -/

/-- The representation `β(t)` is the least abstract element bounding every finite
    prefix: `β(t) ⊑ dh` exactly when every depth-`n` fold is (`csup_le_iff`,
    the safety extension of the finitary Galois connection). -/
theorem β_le_iff {k : Nat} {t : Trace VH} {d₀ : UDk k}
    (hb : ∀ n, Trace.βn n t ⊑ d₀) (dh : UDk k) :
    Trace.β t ⊑ dh ↔ ∀ n, Trace.βn n t ⊑ dh := by
  rw [← le_iff_le (x := Trace.β t) (y := dh)]
  show csup (fun n => Trace.βn n t) ≤ dh ↔ _
  rw [csup_le_iff (fun n => le_iff_le.mpr (hb n)) dh]
  exact ⟨fun h n => le_iff_le.mp (h n), fun h n => le_iff_le.mpr (h n)⟩

/-- The depth-`n` representation of a closed Barendregt program's by-need trace
    at the empty heap is below its usage analysis, established by seeding the
    invariant with the authoritative empty ghost table and stripping the
    `(|==> ▷)^n` tower at the `UPred` model. -/
theorem βn_need (k : Nat) (e : Exp) (hb : Barendregt e) (n : Nat) :
    Trace.βn n (D.runAt μ₀ (evalByNeed e Env.empty)) ⊑ evalUsgk k e Env.empty := by
  have hent : HeapAbsAuth (∅ : HeapAbs (UDk k)) ⊢
      bupdLaterN n (iprop(⌜Trace.βn n (D.runAt μ₀ (evalByNeed e Env.empty))
        ⊑ evalUsgk k e Env.empty⌝) : NeedProp (UDk k)) := by
    refine .trans ?_ (rel_βn (L := e.letBV) n (evalUsgk k e Env.empty)
      (D.runAt μ₀ (evalByNeed e Env.empty)))
    refine .trans emp_sep.2 ?_
    refine .trans (sep_mono (usage_abstracts_need_closed k e hb)
      (heapInv_init (L' := e.letBV))) ?_
    exact Need.soundR_elim _ _ μ₀
  exact ownM_bupdLaterN_soundness n HeapView.auth_one_valid.validN hent

/-- **Usage analysis approximates the by-need semantics** (`thm:absence`, the
    Galois-connection form). For a closed Barendregt program, the representation
    of its by-need trace at the empty heap is below the usage the analysis
    reports: `β(⟦e⟧_need) ⊑ ⟦e⟧_usage`. -/
theorem usage_approximates_need (k : Nat) (e : Exp) (hb : Barendregt e) :
    Trace.β (D.runAt μ₀ (evalByNeed e Env.empty)) ⊑ evalUsgk k e Env.empty :=
  le_iff_le.mp (csup_le (fun n => le_iff_le.mpr (βn_need k e hb n)))

/-- The observable reading of the approximation: at every variable and every
    prefix length, the clamped look count is below the analysis usage. -/
theorem lookCount_le_usage (k : Nat) (e : Exp) (hb : Barendregt e)
    (x : Var) (n : Nat) :
    U.ofCount (Trace.lookCount x n (D.runAt μ₀ (evalByNeed e Env.empty)))
      ⊑ (evalUsgk k e Env.empty).uses !? x :=
  U.le_trans (βn_lookCount x n _)
    ((Uses.le_iff_get _ _).mp ((UDk.le_iff _ _).mp (βn_need k e hb n)).1 x)

/-- **Absence.** A variable the analysis reports absent is never looked up
    by the by-need evaluation, at any prefix length. -/
theorem absence (k : Nat) (e : Exp) (hb : Barendregt e) (x : Var)
    (habs : (evalUsgk k e Env.empty).uses !? x = U.u0) (n : Nat) :
    Trace.lookCount x n (D.runAt μ₀ (evalByNeed e Env.empty)) = 0 :=
  U.ofCount_le_u0 (habs ▸ lookCount_le_usage k e hb x n)

/-- info: 'AbsDen.absence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms absence

/-- The analysis reports a variable the program does not let-bind absent:
    its evaluation is fresh at every such variable, and freshness pins the
    usage to zero. So the evaluation never looks it up. -/
theorem absence_not_letBV (k : Nat) (e : Exp) (hb : Barendregt e) (x : Var)
    (hx : x ∉ e.letBV) (n : Nat) :
    Trace.lookCount x n (D.runAt μ₀ (evalByNeed e Env.empty)) = 0 :=
  absence k e hb x
    (UDk.get_eq_zero_of_fresh (fun _P hP => hP.eval_pred e Env.empty hx EnvPred.empty)) n

end AbsDen
