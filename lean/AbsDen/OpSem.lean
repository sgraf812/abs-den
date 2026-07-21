import AbsDen.ByNeed

/-! # The lazy Krivine machine (`OpSem.lhs`)

The reference operational semantics: the Mark II machine of Sestoft, a
small-step transition system over states `σ = (e, ρ, μ, κ)` of control
expression, environment, heap, and continuation stack. Each heap entry carries
the let-bound variable that allocated it, so a `Look` transition can report
that variable, mirroring the interpreter's `.look` event. The seven rules
Let₁, App₁, Case₁, Look, App₂, Case₂, Upd emit the same-named `Event`s of the
denotational trace, which is what the adequacy relation between machine runs
and `evalByNeed` traces is stated in. -/

namespace AbsDen

namespace LK

/-- A heap stores one closure per allocated address, each tagged with the
    let-bound variable that allocated it: the entry `(y, ρ, e)` at address `a`
    is the thunk for `e` in `ρ`, allocated by `let y = e in …`. The
    representation is the same `GenMap` as the denotational heap's, so both
    sides allocate at `genMapLeast`. -/
abbrev Heap := Iris.GenMap (Var × Env Addr × Exp)

/-- Continuation stacks
    `κ ::= stop ∣ ap(a) ▹ κ ∣ sel(ρ, alts) ▹ κ ∣ upd(a) ▹ κ`. -/
inductive Cont where
  | stop : Cont
  | ap   : Addr → Cont → Cont
  | sel  : Env Addr → List Alt → Cont → Cont
  | upd  : Addr → Cont → Cont

/-- Machine states `σ = (e, ρ, μ, κ)`. -/
abbrev State := Exp × Env Addr × Heap × Cont

/-- The initial state for a closed expression: `init(e) = (e, [], [], stop)`.
    Final states are of the form `(v, _, _, stop)` with `v` a value. -/
def init (e : Exp) : State := (e, Env.empty, Iris.GenMap.empty, .stop)

/-- Answers, the machine's value judgment: a lambda, or a constructor
    application whose fields are in scope. A constructor application with an
    unbound field is stuck at its build site, where `eval`'s constructor case
    is `stuck`; the `Upd` rule and the finality test range over answers. -/
def isAnswer (ρ : Env Addr) : Exp → Bool
  | .lam .. => true
  | .conapp _ xs => ρ[xs]?.isSome
  | _ => false

/-- The transition function `σ₁ ↪ σ₂`, one rule per arm. The machine is
    deterministic; `none` marks final and stuck states. -/
def step : State → Option State
  -- Let₁
  | (.«let» x e₁ e₂, ρ, μ, κ) =>
    let a := genMapLeast μ
    let ρ' := ρ[x ↦ a]
    some (e₂, ρ', μ.alter a (some (x, ρ', e₁)), κ)
  -- App₁
  | (.app e x, ρ, μ, κ) => (ρ.get x).map fun a => (e, ρ, μ, .ap a κ)
  -- Case₁
  | (.«case» eₛ alts, ρ, μ, κ) => some (eₛ, ρ, μ, .sel ρ alts κ)
  -- Look
  | (.ref x, ρ, μ, κ) => do
    let a ← ρ.get x
    let (_y, ρ', e) ← μ.car a
    some (e, ρ', μ, .upd a κ)
  -- App₂
  | (.lam x e, ρ, μ, .ap a κ) => some (e, ρ[x ↦ a], μ, κ)
  -- Case₂ (the pairwise binding presupposes matching arity)
  | (.conapp K ys, ρ, μ, .sel ρ' alts κ) => do
    let alt ← alts.find? (·.con == K)
    let as ← ρ[ys]?
    if alt.vars.length = as.length then
      some (alt.rhs, ρ'[alt.vars ↦* as], μ, κ)
    else
      none
  -- Upd (only answers update their cell)
  | (v@(.lam ..), ρ, μ, .upd a κ) => do
    let (x, _, _) ← μ.car a
    some (v, ρ, μ.alter a (some (x, ρ, v)), κ)
  | (v@(.conapp _ ys), ρ, μ, .upd a κ) => do
    let _ ← ρ[ys]?
    let (x, _, _) ← μ.car a
    some (v, ρ, μ.alter a (some (x, ρ, v)), κ)
  | _ => none

/-- The number of frames on a continuation stack. -/
def Cont.depth : Cont → Nat
  | .stop => 0
  | .ap _ κ => κ.depth + 1
  | .sel _ _ κ => κ.depth + 1
  | .upd _ κ => κ.depth + 1

/-- The interior-maximal machine run from `σ` at initial stack depth `d₀` ends
    at `σ`: either `σ` holds an answer back at depth `d₀` (a balanced return,
    whose next transition would pop below `d₀`), or the machine cannot step at
    all (a stuck end). -/
def stop (d₀ : Nat) : State → Bool
  | σ@(e, ρ, _, κ) => (isAnswer ρ e && κ.depth == d₀) || (step σ).isNone

/-- The heap component of a machine state. -/
abbrev heapOf (σ : State) : Heap := σ.2.2.1

/-- The continuation component of a machine state. -/
abbrev contOf (σ : State) : Cont := σ.2.2.2

/-! ## Stack extension

`κ₀.Ext κ` says `κ` extends `κ₀` by zero or more frames on top; a machine run
interior to `κ₀` moves between such stacks. -/

/-- `κ` is `κ₀` with zero or more frames pushed on top. -/
inductive Cont.Ext (κ₀ : Cont) : Cont → Prop
  | refl : Cont.Ext κ₀ κ₀
  | ap {a κ} : Cont.Ext κ₀ κ → Cont.Ext κ₀ (.ap a κ)
  | sel {ρ alts κ} : Cont.Ext κ₀ κ → Cont.Ext κ₀ (.sel ρ alts κ)
  | upd {a κ} : Cont.Ext κ₀ κ → Cont.Ext κ₀ (.upd a κ)

theorem Cont.Ext.depth_le {κ₀ κ : Cont} (h : κ₀.Ext κ) : κ₀.depth ≤ κ.depth := by
  induction h with
  | refl => exact Nat.le_refl _
  | ap _ ih => exact Nat.le_succ_of_le ih
  | sel _ ih => exact Nat.le_succ_of_le ih
  | upd _ ih => exact Nat.le_succ_of_le ih

/-- An extension back at the base depth is the base stack. -/
theorem Cont.Ext.eq_of_depth_le {κ₀ κ : Cont} (h : κ₀.Ext κ) (hd : κ.depth ≤ κ₀.depth) :
    κ = κ₀ := by
  cases h with
  | refl => rfl
  | ap h' => exact absurd (Nat.le_trans hd h'.depth_le) (Nat.not_succ_le_self _)
  | sel h' => exact absurd (Nat.le_trans hd h'.depth_le) (Nat.not_succ_le_self _)
  | upd h' => exact absurd (Nat.le_trans hd h'.depth_le) (Nat.not_succ_le_self _)

/-! ## Well-addressed configurations

Every address a configuration mentions, in its environment, in the stored
closures' environments, and in its stack frames, is allocated in its heap.
`step` preserves this, so every state reachable from `init e` is `WF`. -/

/-- Every address the environment mentions is allocated. -/
def EnvWF (μ : Heap) (ρ : Env Addr) : Prop :=
  ∀ x a, ρ.get x = some a → (μ.car a).isSome

/-- Every stored closure's environment is allocated. -/
def HeapWF (μ : Heap) : Prop :=
  ∀ a p, μ.car a = some p → EnvWF μ p.2.1

/-- Every frame's address and environment is allocated. -/
def ContWF (μ : Heap) : Cont → Prop
  | .stop => True
  | .ap a κ => (μ.car a).isSome ∧ ContWF μ κ
  | .sel ρ _ κ => EnvWF μ ρ ∧ ContWF μ κ
  | .upd a κ => (μ.car a).isSome ∧ ContWF μ κ

/-- Well-addressed machine states. -/
def WF : State → Prop
  | (_, ρ, μ, κ) => EnvWF μ ρ ∧ HeapWF μ ∧ ContWF μ κ

/-- Reading through `alter`. -/
theorem Heap.car_alter (μ : Heap) (a : Addr) (o : Option (Var × Env Addr × Exp)) (b : Addr) :
    (μ.alter a o).car b = if a = b then o else μ.car b := rfl

/-- Storing an entry keeps every allocated address allocated. -/
theorem Heap.alter_isSome {μ : Heap} {p : Var × Env Addr × Exp} {a b : Addr}
    (h : (μ.car b).isSome) : ((μ.alter a (some p)).car b).isSome := by
  show (if a = b then some p else μ.car b).isSome
  split
  · rfl
  · exact h

theorem EnvWF.mono {μ μ' : Heap} {ρ : Env Addr}
    (hle : ∀ b, (μ.car b).isSome → (μ'.car b).isSome) (h : EnvWF μ ρ) : EnvWF μ' ρ :=
  fun x a hx => hle a (h x a hx)

theorem ContWF.mono {μ μ' : Heap} (hle : ∀ b, (μ.car b).isSome → (μ'.car b).isSome) :
    ∀ {κ : Cont}, ContWF μ κ → ContWF μ' κ
  | .stop, _ => trivial
  | .ap _ _, ⟨ha, hκ⟩ => ⟨hle _ ha, ContWF.mono hle hκ⟩
  | .sel _ _ _, ⟨hρ, hκ⟩ => ⟨hρ.mono hle, ContWF.mono hle hκ⟩
  | .upd _ _, ⟨ha, hκ⟩ => ⟨hle _ ha, ContWF.mono hle hκ⟩

/-- Storing an entry with an allocated environment preserves heap
    well-addressedness. -/
theorem HeapWF.alter {μ : Heap} {a : Addr} {p : Var × Env Addr × Exp}
    (hμ : HeapWF μ) (hp : EnvWF (μ.alter a (some p)) p.2.1) :
    HeapWF (μ.alter a (some p)) := by
  intro b q hq
  have hq' : (if a = b then some p else μ.car b) = some q := hq
  split at hq'
  · obtain rfl := Option.some.inj hq'
    exact hp
  · exact (hμ b q hq').mono (fun c hc => Heap.alter_isSome hc)

theorem EnvWF.extend {μ : Heap} {ρ : Env Addr} (h : EnvWF μ ρ) {x : Var} {a : Addr}
    (ha : (μ.car a).isSome) : EnvWF μ ρ[x ↦ a] := by
  intro y b hy
  have hy' : (if y = x then some a else ρ.get y) = some b := hy
  split at hy'
  · exact Option.some.inj hy' ▸ ha
  · exact h y b hy'

theorem EnvWF.extendMany {μ : Heap} :
    ∀ (xs : List Var) {ρ : Env Addr} (as : List Addr), EnvWF μ ρ →
      (∀ b ∈ as, (μ.car b).isSome) → EnvWF μ ρ[xs ↦* as]
  | [], _, _, h, _ => h
  | _ :: _, _, [], h, _ => h
  | _ :: xs, _, a :: as, h, hb =>
    EnvWF.extendMany xs as (h.extend (hb a (List.mem_cons_self ..)))
      (fun b hbmem => hb b (List.mem_cons_of_mem _ hbmem))

/-- A successful multi-lookup lands on allocated addresses. -/
theorem EnvWF.getMany {μ : Heap} {ρ : Env Addr} (h : EnvWF μ ρ) :
    ∀ (ys : List Var) {as : List Addr}, ρ[ys]? = some as → ∀ b ∈ as, (μ.car b).isSome := by
  intro ys
  induction ys with
  | nil =>
    intro as hget b hb
    simp only [Env.getElem?_getMany, Env.getMany, Option.some.injEq] at hget
    subst hget
    simp at hb
  | cons y ys ih =>
    intro as hget b hb
    simp only [Env.getElem?_getMany, Env.getMany, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hget
    obtain ⟨a, hy, as', has', rfl⟩ := hget
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact h y b hy
    · exact ih has' b hb'

/-- The initial configuration is well-addressed. -/
theorem WF.init (e : Exp) : WF (init e) := by
  show EnvWF Iris.GenMap.empty Env.empty ∧ HeapWF Iris.GenMap.empty ∧
    ContWF Iris.GenMap.empty .stop
  exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), trivial⟩

/-- `step` preserves well-addressedness. -/
theorem WF.step : ∀ {σ σ' : State}, LK.step σ = some σ' → WF σ → WF σ'
  | (e, ρ, μ, κ), σ', hs, ⟨hρ, hμ, hκ⟩ => by
    cases e with
    | «let» x e₁ e₂ =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      have hle : ∀ b, (μ.car b).isSome →
          ((μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁))).car b).isSome :=
        fun _ hb => Heap.alter_isSome hb
      have hρ' : EnvWF (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)))
          (ρ[x ↦ genMapLeast μ]) :=
        (hρ.mono hle).extend (by rw [Heap.car_alter, if_pos rfl]; rfl)
      exact ⟨hρ', hμ.alter hρ', hκ.mono hle⟩
    | app e x =>
      simp only [LK.step, Option.map_eq_some_iff] at hs
      obtain ⟨a, hx, rfl⟩ := hs
      exact ⟨hρ, hμ, hρ x a hx, hκ⟩
    | «case» eₛ alts =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      exact ⟨hρ, hμ, hρ, hκ⟩
    | ref x =>
      cases hget : ρ.get x with
      | none => simp [LK.step, hget] at hs
      | some a =>
        cases hp : μ.car a with
        | none => simp [LK.step, hget, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hget, hp] at hs
          subst hs
          exact ⟨hμ a _ hp, hμ, (by rw [hp]; rfl), hκ⟩
    | lam x e =>
      cases κ with
      | stop => simp [LK.step] at hs
      | sel _ _ _ => simp [LK.step] at hs
      | ap a κ =>
        simp only [LK.step, Option.some.injEq] at hs
        subst hs
        exact ⟨hρ.extend hκ.1, hμ, hκ.2⟩
      | upd a κ =>
        cases hp : μ.car a with
        | none => simp [LK.step, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hp] at hs
          subst hs
          have hle : ∀ b, (μ.car b).isSome →
              ((μ.alter a (some (y, ρ, Exp.lam x e))).car b).isSome :=
            fun _ hb => Heap.alter_isSome hb
          have hρ' : EnvWF (μ.alter a (some (y, ρ, Exp.lam x e))) ρ := hρ.mono hle
          exact ⟨hρ', hμ.alter hρ', hκ.2.mono hle⟩
    | conapp K ys =>
      cases κ with
      | stop => simp [LK.step] at hs
      | ap _ _ => simp [LK.step] at hs
      | sel ρ' alts κ =>
        cases halt : alts.find? (·.con == K) with
        | none => simp [LK.step, halt] at hs
        | some alt =>
          cases has : ρ[ys]? with
          | none => simp [LK.step, halt, has] at hs
          | some as =>
            by_cases hlen : alt.vars.length = as.length
            · simp [LK.step, halt, has, hlen] at hs
              subst hs
              exact ⟨EnvWF.extendMany _ as hκ.1 (hρ.getMany ys has), hμ, hκ.2⟩
            · simp [LK.step, halt, has, hlen] at hs
      | upd a κ =>
        cases has : ρ[ys]? with
        | none => simp [LK.step, has] at hs
        | some as =>
          cases hp : μ.car a with
          | none => simp [LK.step, has, hp] at hs
          | some p =>
            obtain ⟨y, ρ', e'⟩ := p
            simp [LK.step, has, hp] at hs
            subst hs
            have hle : ∀ b, (μ.car b).isSome →
                ((μ.alter a (some (y, ρ, Exp.conapp K ys))).car b).isSome :=
              fun _ hb => Heap.alter_isSome hb
            have hρ' : EnvWF (μ.alter a (some (y, ρ, Exp.conapp K ys))) ρ := hρ.mono hle
            exact ⟨hρ', hμ.alter hρ', hκ.2.mono hle⟩

/-! ## Tag-preserving heap evolution

A machine step only allocates fresh cells or rewrites a cell under its
original tag, so every allocated address stays allocated with its tag. The
abstraction of an environment reads only the tags of the cells it references,
so it is stable across an interior run. -/

/-- Every cell of `μ` is a cell of `μ'` with the same tag. -/
def Heap.Le (μ μ' : Heap) : Prop :=
  ∀ b q, μ.car b = some q → ∃ q', μ'.car b = some q' ∧ q'.1 = q.1

theorem Heap.Le.refl (μ : Heap) : Heap.Le μ μ := fun _ q h => ⟨q, h, rfl⟩

theorem Heap.Le.trans {μ₁ μ₂ μ₃ : Heap} (h₁ : Heap.Le μ₁ μ₂) (h₂ : Heap.Le μ₂ μ₃) :
    Heap.Le μ₁ μ₃ := fun b q h => by
  obtain ⟨q', h', ht⟩ := h₁ b q h
  obtain ⟨q'', h'', ht'⟩ := h₂ b q' h'
  exact ⟨q'', h'', ht'.trans ht⟩

/-- `step` evolves the heap tag-preservingly. -/
theorem step_heapLe : ∀ {σ σ' : State}, LK.step σ = some σ' →
    Heap.Le (heapOf σ) (heapOf σ')
  | (e, ρ, μ, κ), σ', hs => by
    cases e with
    | «let» x e₁ e₂ =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      intro b q h
      refine ⟨q, ?_, rfl⟩
      rw [Heap.car_alter, if_neg, h]
      rintro rfl
      rw [genMapLeast_spec μ] at h
      exact nomatch h
    | app e x =>
      simp only [LK.step, Option.map_eq_some_iff] at hs
      obtain ⟨a, hx, rfl⟩ := hs
      exact Heap.Le.refl μ
    | «case» eₛ alts =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      exact Heap.Le.refl μ
    | ref x =>
      cases hget : ρ.get x with
      | none => simp [LK.step, hget] at hs
      | some a =>
        cases hp : μ.car a with
        | none => simp [LK.step, hget, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hget, hp] at hs
          subst hs
          exact Heap.Le.refl μ
    | lam x e =>
      cases κ with
      | stop => simp [LK.step] at hs
      | sel _ _ _ => simp [LK.step] at hs
      | ap a κ =>
        simp only [LK.step, Option.some.injEq] at hs
        subst hs
        exact Heap.Le.refl μ
      | upd a κ =>
        cases hp : μ.car a with
        | none => simp [LK.step, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hp] at hs
          subst hs
          intro b q h
          rw [Heap.car_alter]
          split
          · next hab =>
            subst hab
            rw [hp] at h
            obtain rfl := Option.some.inj h
            exact ⟨_, rfl, rfl⟩
          · exact ⟨q, h, rfl⟩
    | conapp K ys =>
      cases κ with
      | stop => simp [LK.step] at hs
      | ap _ _ => simp [LK.step] at hs
      | sel ρ' alts κ =>
        cases halt : alts.find? (·.con == K) with
        | none => simp [LK.step, halt] at hs
        | some alt =>
          cases has : ρ[ys]? with
          | none => simp [LK.step, halt, has] at hs
          | some as =>
            by_cases hlen : alt.vars.length = as.length
            · simp [LK.step, halt, has, hlen] at hs
              subst hs
              exact Heap.Le.refl μ
            · simp [LK.step, halt, has, hlen] at hs
      | upd a κ =>
        cases has : ρ[ys]? with
        | none => simp [LK.step, has] at hs
        | some as =>
          cases hp : μ.car a with
          | none => simp [LK.step, has, hp] at hs
          | some p =>
            obtain ⟨y, ρ', e'⟩ := p
            simp [LK.step, has, hp] at hs
            subst hs
            intro b q h
            rw [Heap.car_alter]
            split
            · next hab =>
              subst hab
              rw [hp] at h
              obtain rfl := Option.some.inj h
              exact ⟨_, rfl, rfl⟩
            · exact ⟨q, h, rfl⟩

/-- An answer back at the base depth is a stopped state. -/
theorem stop_of_isAnswer {e : Exp} {ρ : Env Addr} (he : isAnswer ρ e) (μ : Heap) (κ : Cont) :
    stop κ.depth (e, ρ, μ, κ) = true := by
  simp [stop, he]

/-- A constructor application at its own depth is stopped: an answer if its
    fields are bound, stuck at its build site otherwise. -/
theorem stop_conapp (K : ConTag) (xs : List Var) (ρ : Env Addr) (μ : Heap) (κ : Cont) :
    stop κ.depth (Exp.conapp K xs, ρ, μ, κ) = true := by
  cases has : ρ[xs]? with
  | some as => simp [stop, isAnswer, has]
  | none =>
    have hs : step (Exp.conapp K xs, ρ, μ, κ) = none := by
      cases κ with
      | stop => rfl
      | ap _ _ => rfl
      | sel ρ' alts κ' =>
        cases halt : alts.find? (·.con == K) with
        | none => simp [step, halt]
        | some alt => simp [step, halt, has]
      | upd a κ' => simp [step, has]
    simp [stop, hs]

/-- A state that steps while strictly above the base depth is not stopped. -/
theorem stop_eq_false {d₀ : Nat} {σ σ' : State} (hs : step σ = some σ')
    (hdepth : d₀ < (contOf σ).depth) : stop d₀ σ = false := by
  obtain ⟨e, ρ, μ, κ⟩ := σ
  simp only [stop, hs, Option.isNone_some, Bool.or_false, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne]
  exact Or.inr (Nat.ne_of_gt hdepth)

/-- A machine step interior to `κ₁` (not stopped at `κ₁.depth`) stays on an
    extension of `κ₁`: pushes extend further, and the pops fire only from
    reduction states strictly above the base depth. -/
theorem Cont.Ext.step {κ₁ : Cont} : ∀ {σ σ' : State}, LK.step σ = some σ' →
    LK.stop κ₁.depth σ = false → κ₁.Ext (contOf σ) → κ₁.Ext (contOf σ')
  | (e, ρ, μ, κ), σ', hs, hstop, hext => by
    have hstop' : (isAnswer ρ e && κ.depth == κ₁.depth) = false :=
      (Bool.or_eq_false_iff.mp hstop).1
    cases e with
    | «let» x e₁ e₂ =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      exact hext
    | app e x =>
      simp only [LK.step, Option.map_eq_some_iff] at hs
      obtain ⟨a, hx, rfl⟩ := hs
      exact .ap hext
    | «case» eₛ alts =>
      simp only [LK.step, Option.some.injEq] at hs
      subst hs
      exact .sel hext
    | ref x =>
      cases hget : ρ.get x with
      | none => simp [LK.step, hget] at hs
      | some a =>
        cases hp : μ.car a with
        | none => simp [LK.step, hget, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hget, hp] at hs
          subst hs
          exact .upd hext
    | lam x e =>
      simp only [isAnswer, Bool.true_and] at hstop'
      cases κ with
      | stop => simp [LK.step] at hs
      | sel _ _ _ => simp [LK.step] at hs
      | ap a κ =>
        simp only [LK.step, Option.some.injEq] at hs
        subst hs
        cases hext with
        | refl => simp at hstop'
        | ap h' => exact h'
      | upd a κ =>
        cases hp : μ.car a with
        | none => simp [LK.step, hp] at hs
        | some p =>
          obtain ⟨y, ρ', e'⟩ := p
          simp [LK.step, hp] at hs
          subst hs
          cases hext with
          | refl => simp at hstop'
          | upd h' => exact h'
    | conapp K ys =>
      cases κ with
      | stop => simp [LK.step] at hs
      | ap _ _ => simp [LK.step] at hs
      | sel ρ' alts κ =>
        cases halt : alts.find? (·.con == K) with
        | none => simp [LK.step, halt] at hs
        | some alt =>
          cases has : ρ[ys]? with
          | none => simp [LK.step, halt, has] at hs
          | some as =>
            by_cases hlen : alt.vars.length = as.length
            · simp [LK.step, halt, has, hlen] at hs
              subst hs
              cases hext with
              | refl => simp [isAnswer, has] at hstop'
              | sel h' => exact h'
            · simp [LK.step, halt, has, hlen] at hs
      | upd a κ =>
        cases has : ρ[ys]? with
        | none => simp [LK.step, has] at hs
        | some as =>
          cases hp : μ.car a with
          | none => simp [LK.step, has, hp] at hs
          | some p =>
            obtain ⟨y, ρ', e'⟩ := p
            simp [LK.step, has, hp] at hs
            subst hs
            cases hext with
            | refl => simp [isAnswer, has] at hstop'
            | upd h' => exact h'

/-- The event emitted by a state's transition (`α_Events`); the rule taken by
    `step σ` is named by `αEvents σ`. A `Look` reports the let-bound variable
    tagging the heap entry it dereferences. -/
def αEvents : State → Option Event
  | (.«let» .., _, _, _)              => some .let1
  | (.app .., _, _, _)                => some .app1
  | (.«case» .., _, _, _)              => some .case1
  | (.ref x, ρ, μ, _)                 => do
    let a ← ρ.get x
    let (y, _, _) ← μ.car a
    some (.look y)
  | (.lam .., _, _, .ap ..)           => some .app2
  | (.conapp .., _, _, .sel ..)       => some .case2
  | (.lam .., _, _, .upd ..)
  | (.conapp .., _, _, .upd ..)       => some .update
  | _                                 => none

/-- Run for at most `fuel` transitions: the events of the transitions taken
    and the state reached. -/
def run : Nat → State → List Event × State
  | 0,      σ => ([], σ)
  | fuel+1, σ =>
    match step σ with
    | none    => ([], σ)
    | some σ' =>
      let (evs, σf) := run fuel σ'
      ((αEvents σ).toList ++ evs, σf)

/-! ## Machine traces of the example programs

A machine run renders in `runTrace`'s format, so the `#guard`s below state the
observable correspondence directly: the machine's events are exactly the
visible events of the by-need denotational trace (the trace's `invis` layers
are the guarded `▶` administration between events). -/

/-- Render the state a run ends in: a value at the empty continuation has
    returned; anything else the machine cannot step is stuck. -/
def descStop : State → String
  | (.lam .., _, _, .stop)      => "ret(fn)"
  | (.conapp K xs, _, _, .stop) => s!"ret(con{K}[{xs.length}])"
  | _                           => "ret(stuck)"

/-- The machine's observable trace on a closed program. -/
def machineTrace (e : Exp) : String :=
  let (evs, σ) := run 100 (init e)
  String.join (evs.map fun ev => descEv ev ++ ";") ++ descStop σ

-- The paper's first example trace: `let i = λx.x in i i`.
#guard machineTrace idAppId == "let1;app1;look(i);upd;app2;look(i);upd;ret(fn)"
-- The paper's memoisation example: `let i = (λy.λx.x) i in i i`.
#guard machineTrace idAppIdMemo ==
  "let1;app1;look(i);app1;app2;upd;app2;look(i);upd;ret(fn)"

#guard machineTrace idId == (runTrace idId).replace "invis;" ""
#guard machineTrace idAppId == (runTrace idAppId).replace "invis;" ""
#guard machineTrace idAppTrue == (runTrace idAppTrue).replace "invis;" ""
#guard machineTrace idAppIdMemo == (runTrace idAppIdMemo).replace "invis;" ""
#guard machineTrace caseTrue == (runTrace caseTrue).replace "invis;" ""
#guard machineTrace caseStuck == (runTrace caseStuck).replace "invis;" ""

end LK

end AbsDen
