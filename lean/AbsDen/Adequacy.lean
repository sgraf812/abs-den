import AbsDen.Productive
import AbsDen.OpSem

/-! # Adequacy: the by-need denotation weakly bisimulates the LK machine

The representation functions of the paper's `fig:eval-correctness`, by name:

* `α_Ev` is `αEvents` (OpSem.lean),
* `α_E(ρ, μ)` is `αEnv ρ μ`,
* `α_H(μ)` is `αHeap μ`,
* `α_V(σ, κ₀)` is `αValue κ₀ σ`,
* `α_S∞((σᵢ), κ₀)` is `αTraces κ₀ σ₀`, as a relation: the paper defines it
  by guarded recursion over the machine trace, and `αTraces κ₀ σ t` states that
  `t` is its image, arm for arm in `αTraces.rawStep`. `Ret (α_V(σ₀, κ₀),
  α_H μ)` at a trace of length zero is the `.ret` arm (`LK.stop` decides
  "length zero": a balanced return at `κ₀` or no transition), and `Step
  (α_Ev σ₀) ⟨α_S∞((σᵢ₊₁), κ₀)⟩` is the `.step` arm. The third arm has
  no paper equation: a silent `.invis` layer is the `▶`-administration of the
  guarded trace, invisible to the machine, which it therefore stutters,
  making the relation the *weak* bisimulation the paper's theorem statement
  means by `=` on `T`.

`need_abstracts_lk` is the paper's `thm:need-abstracts-lk`, by one Löb
induction with cases on the control expression: pushes take the matching
visible step and hand the frame's continuation to `αTraces_bind`, whose exit
obligation each frame's `αTraces_*Cont` lemma discharges at the stop the
interior run reaches. -/

open Iris Iris.BI Iris.COFE OFE

namespace AbsDen

namespace Adequacy

/-! ## Representation functions -/

export LK (αEvents)

/-- The paper's `α_E(ρ, μ)`: a bound address becomes the
    look-wrapped dereference of its cell, tagged with the variable that
    allocated it. -/
def αEnv (ρ : Env Addr) (μ : LK.Heap) : Env D := fun x =>
  (ρ.get x).bind fun a => (μ.car a).map fun yρe => D.step (.look yρe.1) (fetch a)

/-- The paper's `α_H(μ)`: the cell at `a` holds the memoized denotation of
    the stored closure. -/
def αHeap (μ : LK.Heap) : Heap D where
  car a := (μ.car a).map fun yρe => D.memo a (Later.next (eval yρe.2.2 (αEnv yρe.2.1 μ)))
  bound := μ.bound.imp fun _N hN k hk => by rw [hN k hk]; rfl

/-- The paper's `α_V(σ, κ₀)`: a lambda or constructor application back at
    the initial continuation `κ₀` is the value the balanced run returns,
    anything else is stuck. The paper's `(κ = κ₀)` test is taken on depths,
    which agrees on the stack extensions an interior run moves between
    (`Cont.Ext.eq_of_depth_le`) and keeps the test decidable. -/
def αValue (κ₀ : LK.Cont) : LK.State → Value D
  | (.lam x e, ρ, μ, κ) =>
    if κ.depth = κ₀.depth then
      Value.fn (Later.next (ofe_fun a => Domain.step .app2 (eval e (αEnv ρ μ)[x ↦ a])))
    else Value.stuck
  | (.conapp K xs, ρ, μ, κ) =>
    if κ.depth = κ₀.depth then
      ((αEnv ρ μ)[xs]?).elim Value.stuck fun ds => Value.con K (ds.map Later.next)
    else Value.stuck
  | _ => Value.stuck

/-- The heap component of a machine state. -/
abbrev heapOf (σ : LK.State) : LK.Heap := σ.2.2.1

/-- The payload of `α_S∞`'s `Ret` equation: `(α_V(σ, κ₀), α_H μ)`. -/
def αRet (κ₀ : LK.Cont) (σ : LK.State) : VH := (αValue κ₀ σ, αHeap (heapOf σ))

/-! ## Abstraction algebra

The abstraction functions commute with the machine's heap operations: both
sides allocate at the same fresh address, a fresh store extends the abstracted
environment and heap pointwise, and re-storing a cell under its original tag
changes only that cell. -/

/-- Both sides pick the same fresh address. -/
theorem nextFree_αHeap (μ : LK.Heap) : Heap.nextFree (αHeap μ) = genMapLeast μ :=
  genMapLeast_congr (αHeap μ) μ fun k => by
    show ((μ.car k).map _) = none ↔ μ.car k = none
    cases μ.car k <;> simp

/-- A store at a fresh address leaves the abstraction of a well-addressed
    environment unchanged. -/
theorem αEnv_alter_fresh {μ : LK.Heap} {ρ : Env Addr} {a : Addr}
    (hfresh : μ.car a = none) (hρ : LK.EnvWF μ ρ) (p : Var × Env Addr × Exp) :
    αEnv ρ (μ.alter a (some p)) = αEnv ρ μ := by
  funext y
  show (ρ.get y).bind _ = (ρ.get y).bind _
  cases hy : ρ.get y with
  | none => rfl
  | some b =>
    have hb : (μ.car b).isSome := hρ y b hy
    have hne : a ≠ b := fun h => by rw [← h, hfresh] at hb; exact Bool.noConfusion hb
    show ((μ.alter a (some p)).car b).map _ = ((μ.car b).map _ : Option D)
    rw [LK.Heap.car_alter, if_neg hne]

/-- Re-storing a cell under its original tag leaves the abstracted environment
    unchanged: `αEnv` reads only the tags. -/
theorem αEnv_alter_same_tag {μ : LK.Heap} {ρ : Env Addr} {a : Addr}
    {p q : Var × Env Addr × Exp} (hp : μ.car a = some p) (htag : q.1 = p.1) :
    αEnv ρ (μ.alter a (some q)) = αEnv ρ μ := by
  funext y
  show (ρ.get y).bind _ = (ρ.get y).bind _
  cases hy : ρ.get y with
  | none => rfl
  | some b =>
    show ((μ.alter a (some q)).car b).map _ = ((μ.car b).map _ : Option D)
    rw [LK.Heap.car_alter]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, hp]
      show some (D.step (.look q.1) (fetch a)) = some (D.step (.look p.1) (fetch a))
      rw [htag]
    · rw [if_neg hab]

/-- The machine's `let` allocation abstracts to the interpreter's environment
    extension. -/
theorem αEnv_let {μ : LK.Heap} {ρ : Env Addr} {x : Var} {e₁ : Exp}
    (hρ : LK.EnvWF μ ρ) :
    αEnv ρ[x ↦ genMapLeast μ]
        (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)))
      = (αEnv ρ μ)[x ↦ D.step (.look x) (fetch (genMapLeast μ))] := by
  funext y
  show ((ρ[x ↦ genMapLeast μ]).get y).bind _
      = ((αEnv ρ μ)[x ↦ D.step (.look x) (fetch (genMapLeast μ))]).get y
  by_cases hxy : y = x
  · subst hxy
    rw [Env.get_extend_self, Env.get_extend_self]
    show ((μ.alter (genMapLeast μ) (some (y, ρ[y ↦ genMapLeast μ], e₁))).car
      (genMapLeast μ)).map _ = _
    rw [LK.Heap.car_alter, if_pos rfl]
    rfl
  · rw [Env.get_extend_ne _ _ hxy, Env.get_extend_ne _ _ hxy]
    exact congrFun (αEnv_alter_fresh (genMapLeast_spec μ) hρ _) y

/-- The entry stored at an address abstracts to the memoized denotation of its
    closure. -/
theorem αHeap_car {μ : LK.Heap} {a : Addr} {p : Var × Env Addr × Exp}
    (hp : μ.car a = some p) :
    (αHeap μ).car a = some (D.memo a (Later.next (eval p.2.2 (αEnv p.2.1 μ)))) := by
  show (μ.car a).map _ = _
  rw [hp]
  rfl

/-- The machine's `let` allocation abstracts to the interpreter's heap
    extension. -/
theorem αHeap_let {μ : LK.Heap} {ρ : Env Addr} {x : Var} {e₁ : Exp}
    (hρ : LK.EnvWF μ ρ) (hμ : LK.HeapWF μ) :
    αHeap (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)))
      = Heap.set (αHeap μ) (genMapLeast μ)
          (D.memo (genMapLeast μ) (Later.next (eval e₁
            ((αEnv ρ μ)[x ↦ D.step (.look x) (fetch (genMapLeast μ))])))) := by
  apply GenMap.ext
  funext b
  rw [Heap.set_get]
  show ((μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁))).car b).map _ = _
  rw [LK.Heap.car_alter]
  by_cases hab : genMapLeast μ = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    exact congrArg (fun ρ' => some (D.memo (genMapLeast μ) (Later.next (eval e₁ ρ'))))
      (αEnv_let hρ)
  · rw [if_neg hab, if_neg hab]
    show ((μ.car b).map _ : Option (Later D)) = (μ.car b).map _
    cases hq : μ.car b with
    | none => rfl
    | some q =>
      exact congrArg (fun ρ' => some (D.memo b (Later.next (eval q.2.2 ρ'))))
        (αEnv_alter_fresh (genMapLeast_spec μ) (hμ b q hq) _)

/-- The machine's memoizing update abstracts to the interpreter's heap
    write. -/
theorem αHeap_alter_same_tag {μ : LK.Heap} {a : Addr} {p q : Var × Env Addr × Exp}
    (hp : μ.car a = some p) (htag : q.1 = p.1) :
    αHeap (μ.alter a (some q))
      = Heap.set (αHeap μ) a (D.memo a (Later.next (eval q.2.2 (αEnv q.2.1 μ)))) := by
  apply GenMap.ext
  funext b
  rw [Heap.set_get]
  show ((μ.alter a (some q)).car b).map _ = _
  rw [LK.Heap.car_alter]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    exact congrArg (fun ρ' => some (D.memo a (Later.next (eval q.2.2 ρ'))))
      (αEnv_alter_same_tag hp htag)
  · rw [if_neg hab, if_neg hab]
    show ((μ.car b).map _ : Option (Later D)) = (μ.car b).map _
    cases hq : μ.car b with
    | none => rfl
    | some r =>
      exact congrArg (fun ρ' => some (D.memo b (Later.next (eval r.2.2 ρ'))))
        (αEnv_alter_same_tag hp htag)

/-! ## Reading lookups through the abstraction

An address abstracts to the look-wrapped dereference of its cell (`αAddr`),
which mentions the heap only through the cell's tag; tag-preserving heap
evolution therefore keeps every abstraction valid across an interior run. -/

/-- `a` abstracts to `d`: the look-wrapped dereference of `a`'s cell, tagged
    with the cell's tag. -/
def αAddr (μ : LK.Heap) (a : Addr) (d : D) : Prop :=
  ∃ p, μ.car a = some p ∧ d = D.step (.look p.1) (fetch a)

/-- Tag-preserving heap evolution preserves address abstractions. -/
theorem αAddr.heapLe {μ μ' : LK.Heap} {a : Addr} {d : D} (hle : LK.Heap.Le μ μ')
    (h : αAddr μ a d) : αAddr μ' a d := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, ht⟩ := hle a p hp
  exact ⟨q, hq, by rw [ht]⟩

theorem αEnv_get_none {ρ : Env Addr} {μ : LK.Heap} {x : Var} (h : ρ.get x = none) :
    (αEnv ρ μ).get x = none := by
  show (ρ.get x).bind _ = none
  rw [h]
  rfl

theorem αEnv_get_undef {ρ : Env Addr} {μ : LK.Heap} {x : Var} {a : Addr}
    (hget : ρ.get x = some a) (hp : μ.car a = none) : (αEnv ρ μ).get x = none := by
  show (ρ.get x).bind _ = none
  rw [hget]
  show (μ.car a).map _ = none
  rw [hp]
  rfl

/-- A bound variable abstracts to the look-wrapped dereference of its cell. -/
theorem αEnv_get_eq {ρ : Env Addr} {μ : LK.Heap} {x : Var} {a : Addr}
    {p : Var × Env Addr × Exp} (hget : ρ.get x = some a) (hp : μ.car a = some p) :
    (αEnv ρ μ).get x = some (D.step (.look p.1) (fetch a)) := by
  show (ρ.get x).bind _ = _
  rw [hget]
  show (μ.car a).map _ = _
  rw [hp]
  rfl

/-- A bound variable abstracts to the abstraction of its address. -/
theorem αEnv_get_some {ρ : Env Addr} {μ : LK.Heap} {x : Var} {a : Addr}
    (hρ : LK.EnvWF μ ρ) (hget : ρ.get x = some a) :
    ∃ d, (αEnv ρ μ).get x = some d ∧ αAddr μ a d := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hρ x a hget)
  exact ⟨D.step (.look p.1) (fetch a), αEnv_get_eq hget hp, p, hp, rfl⟩

/-- A successful multi-lookup abstracts pointwise. -/
theorem αEnv_getMany_some {ρ : Env Addr} {μ : LK.Heap} (hρ : LK.EnvWF μ ρ) :
    ∀ {ys : List Var} {addrs : List Addr}, ρ[ys]? = some addrs →
      ∃ ds, (αEnv ρ μ)[ys]? = some ds ∧ List.Forall₂ (αAddr μ) addrs ds
  | [], addrs, h => by
    simp only [Env.getElem?_getMany, Env.getMany, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, .nil⟩
  | y :: ys, addrs, h => by
    simp only [Env.getElem?_getMany, Env.getMany, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨a, hy, as', has', rfl⟩ := h
    obtain ⟨d, hd, hαd⟩ := αEnv_get_some hρ hy
    obtain ⟨ds', hds', hα'⟩ := αEnv_getMany_some hρ
      (show ρ[ys]? = some as' from has')
    refine ⟨d :: ds', ?_, .cons hαd hα'⟩
    show ((αEnv ρ μ).get y).bind _ = _
    rw [hd]
    show ((αEnv ρ μ).getMany ys).map _ = _
    rw [show (αEnv ρ μ).getMany ys = some ds' from hds']
    rfl

/-- A failed multi-lookup abstracts to a failed multi-lookup. -/
theorem αEnv_getMany_none {ρ : Env Addr} {μ : LK.Heap} :
    ∀ {ys : List Var}, ρ[ys]? = none → (αEnv ρ μ)[ys]? = none
  | [], h => by simp [Env.getElem?_getMany, Env.getMany] at h
  | y :: ys, h => by
    show ((αEnv ρ μ).get y).bind _ = none
    cases hd : (αEnv ρ μ).get y with
    | none => rfl
    | some d =>
      have hy : ∃ a, ρ.get y = some a := by
        cases hy : ρ.get y with
        | none => rw [αEnv_get_none hy] at hd; exact nomatch hd
        | some a => exact ⟨a, rfl⟩
      obtain ⟨a, hy⟩ := hy
      have h' : (ρ.getMany ys).map (a :: ·) = none := by
        simpa [Env.getElem?_getMany, Env.getMany, hy] using h
      have hys : ρ[ys]? = none := Option.map_eq_none_iff.mp h'
      show ((αEnv ρ μ).getMany ys).map _ = none
      rw [show (αEnv ρ μ).getMany ys = none from αEnv_getMany_none hys]
      rfl

/-- Binding an abstracted address abstracts the machine's binding. -/
theorem αEnv_extend_αAddr {μ : LK.Heap} {ρ : Env Addr} {x : Var} {a : Addr} {d : D}
    (h : αAddr μ a d) : αEnv ρ[x ↦ a] μ = (αEnv ρ μ)[x ↦ d] := by
  obtain ⟨p, hp, rfl⟩ := h
  funext y
  by_cases hxy : y = x
  · subst hxy
    show ((ρ[y ↦ a]).get y).bind _ = ((αEnv ρ μ)[y ↦ _]).get y
    rw [Env.get_extend_self, Env.get_extend_self]
    show (μ.car a).map _ = _
    rw [hp]
    rfl
  · show ((ρ[x ↦ a]).get y).bind _ = ((αEnv ρ μ)[x ↦ _]).get y
    rw [Env.get_extend_ne _ _ hxy, Env.get_extend_ne _ _ hxy]
    rfl

/-- Binding abstracted addresses pointwise abstracts the machine's
    multi-binding. -/
theorem αEnv_extendMany_αAddr {μ : LK.Heap} :
    ∀ {vars : List Var} {addrs : List Addr} {ds : List D} {ρ : Env Addr},
      List.Forall₂ (αAddr μ) addrs ds →
      αEnv ρ[vars ↦* addrs] μ = (αEnv ρ μ)[vars ↦* ds]
  | [], _, _, ρ, h => by cases h <;> rfl
  | v :: vars, _, _, ρ, .nil => rfl
  | v :: vars, _, _, ρ, .cons hd htl => by
    show αEnv ((ρ[v ↦ _]).extendMany vars _) μ
      = ((αEnv ρ μ)[v ↦ _]).extendMany vars _
    rw [αEnv_extendMany_αAddr htl, αEnv_extend_αAddr hd]

/-- The abstraction of a well-addressed environment is stable across
    tag-preserving heap evolution. -/
theorem αEnv_heapLe {μ μ' : LK.Heap} {ρ : Env Addr} (hρ : LK.EnvWF μ ρ)
    (hle : LK.Heap.Le μ μ') : αEnv ρ μ' = αEnv ρ μ := by
  funext y
  show (ρ.get y).bind _ = (ρ.get y).bind _
  cases hy : ρ.get y with
  | none => rfl
  | some a =>
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hρ y a hy)
    obtain ⟨q, hq, ht⟩ := hle a p hp
    show (μ'.car a).map _ = (μ.car a).map _
    rw [hp, hq]
    show some (D.step (.look q.1) _) = some (D.step (.look p.1) _)
    rw [ht]

/-! ## The abstracted value off a balanced stop -/

/-- Off an answer at the matching depth, the abstracted value is `stuck`. -/
theorem αValue_eq_stuck {κ₀ : LK.Cont} {σ : LK.State}
    (h : (LK.isAnswer σ.2.1 σ.1 && ((LK.contOf σ).depth == κ₀.depth)) = false) :
    αValue κ₀ σ = Value.stuck := by
  obtain ⟨es, ρs, μs, κs⟩ := σ
  cases es with
  | lam x b =>
    have hd : ¬ κs.depth = κ₀.depth := by simpa [LK.isAnswer] using h
    simp [αValue, hd]
  | conapp K xs =>
    by_cases hd : κs.depth = κ₀.depth
    · have hxs : ρs[xs]? = none := by
        cases hxs : ρs[xs]? with
        | none => rfl
        | some _ => simp [LK.isAnswer, hxs, hd] at h
      simp [αValue, hd, αEnv_getMany_none hxs]
    · simp [αValue, hd]
  | ref x => rfl
  | app e x => rfl
  | «case» eₛ alts => rfl
  | «let» x e₁ e₂ => rfl

/-- Below the depth of its stack, a state abstracts to a stuck return. -/
theorem αRet_stuck {κ₀ : LK.Cont} {σ : LK.State} (hd : (LK.contOf σ).depth ≠ κ₀.depth) :
    αRet κ₀ σ = (Value.stuck, αHeap (heapOf σ)) := by
  show (αValue κ₀ σ, αHeap (heapOf σ)) = _
  rw [αValue_eq_stuck (by simp [hd])]

/-! ## The alternatives `eval` builds for a `case` -/

/-- The alternative `eval` builds: its tag, its arity, and the arity-guarded
    branch behind its `.case2` step. -/
def evalAlt (ρd : Env D) (alt : Alt) : ConTag × Nat × (List D -n> D) :=
  (alt.con, alt.vars.length, ofe_fun ds =>
    if ds.length = alt.vars.length then
      Domain.step .case2 (eval alt.rhs ρd[alt.vars ↦* ds])
    else Domain.stuck)

/-- `eval`'s alternative list is the pointwise `evalAlt` image (the attached
    membership only feeds `eval`'s termination argument). -/
theorem evalAlts_eq (ρd : Env D) (alts : List Alt) :
    (alts.attach.map fun alt =>
      (alt.1.con, alt.1.vars.length, ofe_fun ds =>
        if ds.length = alt.1.vars.length then
          Domain.step .case2 (eval alt.1.rhs ρd[alt.1.vars ↦* ds])
        else Domain.stuck))
    = alts.map (evalAlt ρd) := by
  rw [show (fun (alt : {x // x ∈ alts}) =>
      (alt.1.con, alt.1.vars.length, ofe_fun ds =>
        if ds.length = alt.1.vars.length then
          Domain.step .case2 (eval alt.1.rhs ρd[alt.1.vars ↦* ds])
        else Domain.stuck))
    = (evalAlt ρd) ∘ Subtype.val from rfl]
  rw [← List.map_map, List.attach_map_subtype_val]

/-- Alternative selection commutes with building the continuations. -/
theorem evalAlts_find (ρd : Env D) (alts : List Alt) (K : ConTag) :
    ((alts.map (evalAlt ρd)).find? (·.1 == K))
      = (alts.find? (·.con == K)).map (evalAlt ρd) := by
  rw [List.find?_map]
  rfl

/-! ## `eval` applied to an environment, one equation per syntactic form -/

theorem eval_ref (x : Var) (ρd : Env D) :
    eval (Exp.ref x) ρd = (ρd.get x).getD Domain.stuck := by
  simp only [eval]

theorem eval_app (e : Exp) (x : Var) (ρd : Env D) :
    eval (Exp.app e x) ρd
      = (ρd.get x).elim Domain.stuck
          (fun d => Domain.step .app1 (Domain.apply (eval e ρd) d)) := by
  simp only [eval]

theorem eval_case (eₛ : Exp) (alts : List Alt) (ρd : Env D) :
    eval (Exp.«case» eₛ alts) ρd
      = Domain.step .case1 (Domain.select (eval eₛ ρd) (alts.map (evalAlt ρd))) := by
  simp only [eval]
  rw [← evalAlts_eq ρd alts]

theorem eval_let (x : Var) (e₁ e₂ : Exp) (ρd : Env D) :
    eval (Exp.«let» x e₁ e₂) ρd
      = Domain.step .let1 (Domain.bind
          (ofe_fun d => eval e₁ ρd[x ↦ Domain.step (.look x) d])
          (ofe_fun d => eval e₂ ρd[x ↦ Domain.step (.look x) d])) := by
  simp only [eval]

/-- Internal equality against a fixed right-hand side is non-expansive in the
    left-hand side. -/
theorem internalEqD {A : Type} [OFE A] {n : Nat} {a a' : A} (b : A) (h : a ≡{n}≡ a') :
    (iprop(a ≡ b) : SiProp) ≡{n}≡ (iprop(a' ≡ b) : SiProp) :=
  NonExpansive₂.ne (f := (internalEq : A → A → SiProp)) h (OFE.dist_eqv.refl b)

/-! ## `α_S∞`, as a guarded weak bisimulation over the machine state

The paper's `α_S∞` maps a maximal machine trace to a denotational trace
by guarded recursion. Here the machine trace is generated on the fly from its
source state by `LK.step`, and the function becomes the relation `αTraces κ₀ σ`
between the source state and a trace: each arm of `αTraces.rawStep` transcribes
one of its equations. -/

/-- One unfolded trace layer matched against the machine at `σ`, one arm per
    `α_S∞` equation: a `.ret` is `Ret (α_V(σ, κ₀), α_H μ)` at a
    stopped `σ` (a machine trace of length zero), a visible `.step` is
    `Step (α_Ev σ) ⟨…⟩` with the tail related to the machine's successor,
    and an `.invis` layer is `▶`-administration without machine counterpart,
    stuttering `σ`. `rec` sits under `▷`. -/
def αTraces.rawStep (κ₀ : LK.Cont) (rec : LK.State → Trace VH -n> SiProp)
    (σ : LK.State) : TraceF VH (Trace VH) (Trace VH) -n> SiProp :=
  ⟨fun x => match x with
    | .ret vμ => if LK.stop κ₀.depth σ then iprop(vμ ≡ αRet κ₀ σ) else iprop(False)
    | .step ev tl =>
      match LK.step σ with
      | some σ' =>
        if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec σ' tl.car))
        else iprop(False)
      | none => iprop(False)
    | .invis tl => iprop(▷ (rec σ tl.car)),
   ⟨fun {n x x'} h => by
     rcases x with vμ | ⟨ev, tl⟩ | tl <;> rcases x' with vμ' | ⟨ev', tl'⟩ | tl' <;>
       try exact False.elim h
     · have hv : vμ ≡{n}≡ vμ' := h
       show (if LK.stop κ₀.depth σ then iprop(vμ ≡ αRet κ₀ σ) else iprop(False)) ≡{n}≡
         (if LK.stop κ₀.depth σ then iprop(vμ' ≡ αRet κ₀ σ) else iprop(False))
       exact iteD (internalEqD (αRet κ₀ σ) hv) (reflD _)
     · obtain ⟨rfl, htl⟩ := h
       show (match LK.step σ with
         | some σ' =>
           if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec σ' tl.car))
           else iprop(False)
         | none => iprop(False)) ≡{n}≡
        (match LK.step σ with
         | some σ' =>
           if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec σ' tl'.car))
           else iprop(False)
         | none => iprop(False))
       rcases LK.step σ with _ | σ'
       · exact reflD _
       · exact iteD (later_car_ne (P := rec σ') htl) (reflD _)
     · exact later_car_ne (P := rec σ) h⟩⟩

/-- The body of `αTraces`'s fixpoint (over the machine state): match the
    unfolded layer. Every recursive reference sits under `▷`, so the operator
    is contractive. -/
def αTraces.body (κ₀ : LK.Cont) (rec : LK.State → Trace VH -n> SiProp) :
    LK.State → Trace VH -n> SiProp :=
  fun σ => (αTraces.rawStep κ₀ rec σ).comp Trace.unfold

instance (κ₀ : LK.Cont) : OFE.Contractive (αTraces.body κ₀) where
  distLater_dist {n rec rec'} H := by
    intro σ t
    show αTraces.rawStep κ₀ rec σ (Trace.unfold t) ≡{n}≡
      αTraces.rawStep κ₀ rec' σ (Trace.unfold t)
    rcases Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · apply reflD
    · show (match LK.step σ with
        | some σ' =>
          if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec σ' tl.car))
          else iprop(False)
        | none => iprop(False)) ≡{n}≡
       (match LK.step σ with
        | some σ' =>
          if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec' σ' tl.car))
          else iprop(False)
        | none => iprop(False))
      rcases LK.step σ with _ | σ'
      · exact reflD _
      · exact iteD (later_car_distLater (fun m hm => H m hm σ') tl) (reflD _)
    · exact later_car_distLater (fun m hm => H m hm σ) tl

/-- `αTraces.body` at a returned value reduces to the abstraction of the stopped
    state, behind the stop check. -/
theorem αTraces.body_ret_eq (κ₀ : LK.Cont) (rec : LK.State → Trace VH -n> SiProp)
    (σ : LK.State) (vμ : VH) :
    αTraces.body κ₀ rec σ (Trace.ret vμ) ≡
      (if LK.stop κ₀.depth σ then iprop(vμ ≡ αRet κ₀ σ) else iprop(False)) :=
  (αTraces.rawStep κ₀ rec σ).ne.eqv (Trace.unfold_fold (.ret vμ))

/-- `αTraces.body` at a visible step reduces to the tail at the machine's
    successor under `▷`, behind the transition and event checks. -/
theorem αTraces.body_step_eq (κ₀ : LK.Cont) (rec : LK.State → Trace VH -n> SiProp)
    (σ : LK.State) (ev : Event) (tl : Later (Trace VH)) :
    αTraces.body κ₀ rec σ (Trace.step ev tl) ≡
      (match LK.step σ with
       | some σ' =>
         if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (rec σ' tl.car))
         else iprop(False)
       | none => iprop(False)) :=
  (αTraces.rawStep κ₀ rec σ).ne.eqv (Trace.unfold_fold (.step ev tl))

/-- `αTraces.body` at a silent step stutters the machine under `▷`. -/
theorem αTraces.body_invis_eq (κ₀ : LK.Cont) (rec : LK.State → Trace VH -n> SiProp)
    (σ : LK.State) (tl : Later (Trace VH)) :
    αTraces.body κ₀ rec σ (Trace.invis tl) ≡ iprop(▷ (rec σ tl.car)) :=
  (αTraces.rawStep κ₀ rec σ).ne.eqv (Trace.unfold_fold (.invis tl))

/-- `α_S∞(·, κ₀)` as a relation: the machine run from `σ` interior to
    `κ₀` weakly bisimulates the trace; the fixpoint of `αTraces.body`. -/
def αTraces (κ₀ : LK.Cont) : LK.State → Trace VH -n> SiProp :=
  (Function.toContractiveHom (αTraces.body κ₀)).fixpoint

theorem αTraces_unfold (κ₀ : LK.Cont) : αTraces κ₀ ≡ αTraces.body κ₀ (αTraces κ₀) :=
  fixpoint_unfold (Function.toContractiveHom (αTraces.body κ₀))

/-- Unfold `αTraces` on a state and a trace, as `⊣⊢`. -/
theorem αTraces_run (κ₀ : LK.Cont) (σ : LK.State) (t : Trace VH) :
    αTraces κ₀ σ t ⊣⊢ αTraces.body κ₀ (αTraces κ₀) σ t :=
  equiv_iff.mp (αTraces_unfold κ₀ σ t)

/-! ## Reduction lemmas -/

/-- A returned value at a stopped state is its abstraction. -/
theorem αTraces_ret (κ₀ : LK.Cont) {σ : LK.State} (hσ : LK.stop κ₀.depth σ) (vμ : VH) :
    αTraces κ₀ σ (Trace.ret vμ) ⊣⊢ iprop(vμ ≡ αRet κ₀ σ) := by
  refine (αTraces_run κ₀ σ (Trace.ret vμ)).trans ?_
  refine ((equiv_iff (Q := (if LK.stop κ₀.depth σ then iprop(vμ ≡ αRet κ₀ σ)
    else iprop(False)))).mp ?_).trans ?_
  · exact αTraces.body_ret_eq κ₀ (αTraces κ₀) σ vμ
  · exact .of_eq (if_pos hσ)

/-- A running state denies a returned value. -/
theorem αTraces_ret_denied (κ₀ : LK.Cont) {σ : LK.State} (hσ : ¬ LK.stop κ₀.depth σ) (vμ : VH) :
    αTraces κ₀ σ (Trace.ret vμ) ⊣⊢ (False : SiProp) := by
  refine (αTraces_run κ₀ σ (Trace.ret vμ)).trans ?_
  refine ((equiv_iff (Q := (if LK.stop κ₀.depth σ then iprop(vμ ≡ αRet κ₀ σ)
    else iprop(False)))).mp ?_).trans ?_
  · exact αTraces.body_ret_eq κ₀ (αTraces κ₀) σ vμ
  · exact .of_eq (if_neg hσ)

/-- A visible step at a running state matches the machine transition carrying
    the same event and continues at its successor under `▷`. -/
theorem αTraces_step (κ₀ : LK.Cont) {σ σ' : LK.State} (hs : LK.step σ = some σ')
    (hσ : ¬ LK.stop κ₀.depth σ) {ev : Event} (hev : αEvents σ = some ev)
    (tl : Later (Trace VH)) :
    αTraces κ₀ σ (Trace.step ev tl) ⊣⊢ iprop(▷ (αTraces κ₀ σ' tl.car)) := by
  refine (αTraces_run κ₀ σ (Trace.step ev tl)).trans ?_
  refine ((equiv_iff (Q := (match LK.step σ with
    | some σ' =>
      if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (αTraces κ₀ σ' tl.car))
      else iprop(False)
    | none => iprop(False)))).mp ?_).trans ?_
  · exact αTraces.body_step_eq κ₀ (αTraces κ₀) σ ev tl
  · rw [hs]
    exact .of_eq (if_pos ⟨hσ, hev⟩)

/-- A trace cannot take a visible step where the machine has none. -/
theorem αTraces_step_none (κ₀ : LK.Cont) {σ : LK.State} (hs : LK.step σ = none)
    (ev : Event) (tl : Later (Trace VH)) :
    αTraces κ₀ σ (Trace.step ev tl) ⊣⊢ (False : SiProp) := by
  refine (αTraces_run κ₀ σ (Trace.step ev tl)).trans ?_
  refine ((equiv_iff (Q := (match LK.step σ with
    | some σ' =>
      if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (αTraces κ₀ σ' tl.car))
      else iprop(False)
    | none => iprop(False)))).mp ?_).trans ?_
  · exact αTraces.body_step_eq κ₀ (αTraces κ₀) σ ev tl
  · rw [hs]
    exact .rfl

/-- A visible step at a stopped state, or one carrying the wrong event, is
    denied. -/
theorem αTraces_step_denied (κ₀ : LK.Cont) {σ σ' : LK.State} (hs : LK.step σ = some σ')
    {ev : Event} (h : ¬ (¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev))
    (tl : Later (Trace VH)) :
    αTraces κ₀ σ (Trace.step ev tl) ⊣⊢ (False : SiProp) := by
  refine (αTraces_run κ₀ σ (Trace.step ev tl)).trans ?_
  refine ((equiv_iff (Q := (match LK.step σ with
    | some σ' =>
      if ¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev then iprop(▷ (αTraces κ₀ σ' tl.car))
      else iprop(False)
    | none => iprop(False)))).mp ?_).trans ?_
  · exact αTraces.body_step_eq κ₀ (αTraces κ₀) σ ev tl
  · rw [hs]
    exact .of_eq (if_neg h)

/-- A silent step stutters the machine under `▷`. -/
theorem αTraces_invis (κ₀ : LK.Cont) (σ : LK.State) (tl : Later (Trace VH)) :
    αTraces κ₀ σ (Trace.invis tl) ⊣⊢ iprop(▷ (αTraces κ₀ σ tl.car)) := by
  refine (αTraces_run κ₀ σ (Trace.invis tl)).trans ?_
  refine (equiv_iff (Q := iprop(▷ (αTraces κ₀ σ tl.car)))).mp ?_
  exact αTraces.body_invis_eq κ₀ (αTraces κ₀) σ tl

/-- `αTraces` at a fixed state respects trace equivalence in its scrutinee. -/
theorem αTraces_proper (κ₀ : LK.Cont) (σ : LK.State) {t t' : Trace VH} (h : t ≡ t') :
    αTraces κ₀ σ t ⊣⊢ αTraces κ₀ σ t' :=
  equiv_iff.mp ((αTraces κ₀ σ).ne.eqv h)

/-- `αTraces` reduced through an unfolding equation at a `.ret` layer. -/
theorem αTraces_ret_of_unfold (κ₀ : LK.Cont) {σ : LK.State} (hσ : LK.stop κ₀.depth σ)
    {t : Trace VH} {vμ : VH} (hu : Trace.unfold t = .ret vμ) :
    αTraces κ₀ σ t ⊣⊢ iprop(vμ ≡ αRet κ₀ σ) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_ret κ₀ hσ vμ)

/-- `αTraces` reduced through an unfolding equation at a denied `.ret` layer. -/
theorem αTraces_ret_denied_of_unfold (κ₀ : LK.Cont) {σ : LK.State} (hσ : ¬ LK.stop κ₀.depth σ)
    {t : Trace VH} {vμ : VH} (hu : Trace.unfold t = .ret vμ) :
    αTraces κ₀ σ t ⊣⊢ (False : SiProp) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_ret_denied κ₀ hσ vμ)

/-- `αTraces` reduced through an unfolding equation at a `.step` layer. -/
theorem αTraces_step_of_unfold (κ₀ : LK.Cont) {σ σ' : LK.State} (hs : LK.step σ = some σ')
    (hσ : ¬ LK.stop κ₀.depth σ) {ev : Event} (hev : αEvents σ = some ev)
    {t : Trace VH} {tl : Later (Trace VH)} (hu : Trace.unfold t = .step ev tl) :
    αTraces κ₀ σ t ⊣⊢ iprop(▷ (αTraces κ₀ σ' tl.car)) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_step κ₀ hs hσ hev tl)

/-- `αTraces` reduced through an unfolding equation at an `.invis` layer. -/
theorem αTraces_invis_of_unfold (κ₀ : LK.Cont) (σ : LK.State)
    {t : Trace VH} {tl : Later (Trace VH)} (hu : Trace.unfold t = .invis tl) :
    αTraces κ₀ σ t ⊣⊢ iprop(▷ (αTraces κ₀ σ tl.car)) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_invis κ₀ σ tl)

/-- `αTraces` reduced through an unfolding equation at a machine-less `.step`
    layer. -/
theorem αTraces_step_none_of_unfold (κ₀ : LK.Cont) {σ : LK.State} (hs : LK.step σ = none)
    {t : Trace VH} {ev : Event} {tl : Later (Trace VH)}
    (hu : Trace.unfold t = .step ev tl) :
    αTraces κ₀ σ t ⊣⊢ (False : SiProp) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_step_none κ₀ hs ev tl)

/-- `αTraces` reduced through an unfolding equation at a denied `.step` layer. -/
theorem αTraces_step_denied_of_unfold (κ₀ : LK.Cont) {σ σ' : LK.State}
    (hs : LK.step σ = some σ') {ev : Event}
    (h : ¬ (¬ LK.stop κ₀.depth σ ∧ αEvents σ = some ev))
    {t : Trace VH} {tl : Later (Trace VH)} (hu : Trace.unfold t = .step ev tl) :
    αTraces κ₀ σ t ⊣⊢ (False : SiProp) :=
  (αTraces_proper κ₀ σ (Trace.equiv_of_unfold hu).symm).trans (αTraces_step_denied κ₀ hs h tl)

/-! ## Binding a continuation across an interior run

The paper's "`>>=` forwards `Step`s" argument: a trace that bisimulates the
interior run above the base stack `κ₁`, bound with a continuation that is
correct at every stopped state, bisimulates the run below `κ₁`. `Q` carries
whatever context the continuation's correctness needs, and `I` carries the
pure facts about machine states that survive interior steps. -/

theorem αTraces_bind (Q : SiProp) (k : VH -n> Trace VH) (κ₀ : LK.Cont) (κ₁ : LK.Cont)
    (hd : κ₀.depth < κ₁.depth) (I : LK.State → Prop)
    (hIstep : ∀ σ σ', LK.step σ = some σ' → LK.stop κ₁.depth σ = false → I σ → I σ')
    (hIext : ∀ σ, I σ → κ₁.Ext (LK.contOf σ))
    (Hk : ∀ (σ : LK.State) (vμ : VH), LK.stop κ₁.depth σ → I σ →
      iprop(Q ∧ vμ ≡ αRet κ₁ σ) ⊢ αTraces κ₀ σ (k vμ))
    (σ : LK.State) (t : Trace VH) (hI : I σ) :
    iprop(Q ∧ αTraces κ₁ σ t) ⊢ αTraces κ₀ σ (Trace.bind k t) := by
  have main : ⊢ iprop(∀ (σ : LK.State) (t : Trace VH),
      ⌜I σ⌝ → (Q ∧ αTraces κ₁ σ t) → αTraces κ₀ σ (Trace.bind k t)) := by
    refine Entails.trans ?_ loeb
    refine imp_intro ?_
    refine .trans and_elim_r ?_
    refine forall_intro fun σ => forall_intro fun t => imp_intro (imp_intro ?_)
    refine pure_elim (I σ) (and_elim_l.trans and_elim_r) fun hI => ?_
    rcases hu : Trace.unfold t with vμ | ⟨ev, tl⟩ | tl
    · -- `.ret`: the machine has stopped; splice the continuation.
      by_cases hstop : LK.stop κ₁.depth σ
      · have hR : αTraces κ₀ σ (Trace.bind k t) ⊣⊢ αTraces κ₀ σ (k vμ) :=
          αTraces_proper κ₀ σ
            (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
              (Trace.bind_ret k vμ))
        refine .trans ?_ hR.2
        refine .trans ?_ (Hk σ vμ hstop hI)
        exact and_intro (and_elim_r.trans and_elim_l)
          (and_elim_r.trans (and_elim_r.trans (αTraces_ret_of_unfold κ₁ hstop hu).1))
      · exact (and_elim_r.trans (and_elim_r.trans
          (αTraces_ret_denied_of_unfold κ₁ hstop hu).1)).trans false_elim
    · -- `.step`: both runs take the machine transition; recurse one step later.
      rcases hs : LK.step σ with _ | σ'
      · exact (and_elim_r.trans (and_elim_r.trans
          (αTraces_step_none_of_unfold κ₁ hs hu).1)).trans false_elim
      · by_cases hcond : ¬ LK.stop κ₁.depth σ ∧ αEvents σ = some ev
        · obtain ⟨hnstop, hev⟩ := hcond
          have hstopf : LK.stop κ₁.depth σ = false := by
            cases h : LK.stop κ₁.depth σ
            · rfl
            · exact absurd h hnstop
          have hnstop' : ¬ LK.stop κ₀.depth σ := by
            simp [LK.stop_eq_false hs
              (Nat.lt_of_lt_of_le hd (hIext σ hI).depth_le)]
          have hR : αTraces κ₀ σ (Trace.bind k t)
              ⊣⊢ iprop(▷ (αTraces κ₀ σ' (Trace.bind k tl.car))) :=
            (αTraces_proper κ₀ σ
              (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
                (Trace.bind_step k ev tl))).trans
              (αTraces_step κ₀ hs hnstop' hev _)
          refine .trans (and_mono .rfl (and_mono .rfl
            (αTraces_step_of_unfold κ₁ hs hnstop hev hu).1)) ?_
          refine .trans ?_ hR.2
          refine .trans (and_mono and_elim_l .rfl) ?_
          refine .trans (and_mono .rfl (and_mono later_intro .rfl)) ?_
          refine .trans (and_mono .rfl later_and.2) ?_
          refine .trans later_and.2 (later_mono ?_)
          refine .trans (and_mono ((forall_elim σ').trans (forall_elim tl.car)) .rfl) ?_
          exact (and_mono (pure_imp_elim (hIstep σ σ' hs hstopf hI)) .rfl).trans
            imp_elim_left
        · exact (and_elim_r.trans (and_elim_r.trans
            (αTraces_step_denied_of_unfold κ₁ hs hcond hu).1)).trans false_elim
    · -- `.invis`: the trace stutters; recurse at the same state.
      have hR : αTraces κ₀ σ (Trace.bind k t)
          ⊣⊢ iprop(▷ (αTraces κ₀ σ (Trace.bind k tl.car))) :=
        (αTraces_proper κ₀ σ
          (((Trace.bind k).ne.eqv (Trace.equiv_of_unfold hu).symm).trans
            (Trace.bind_invis k tl))).trans
          (αTraces_invis κ₀ σ _)
      refine .trans (and_mono .rfl (and_mono .rfl
        (αTraces_invis_of_unfold κ₁ σ hu).1)) ?_
      refine .trans ?_ hR.2
      refine .trans (and_mono and_elim_l .rfl) ?_
      refine .trans (and_mono .rfl (and_mono later_intro .rfl)) ?_
      refine .trans (and_mono .rfl later_and.2) ?_
      refine .trans later_and.2 (later_mono ?_)
      refine .trans (and_mono ((forall_elim σ).trans (forall_elim tl.car)) .rfl) ?_
      exact (and_mono (pure_imp_elim hI) .rfl).trans imp_elim_left
  refine .trans (and_intro ((LR.of_empValid main).trans
    ((forall_elim σ).trans (forall_elim t))) .rfl) ?_
  exact (and_mono (pure_imp_elim hI) .rfl).trans imp_elim_left

/-! ## The value base cases

A machine state whose control is a value at the base depth has an empty
interior run; the interpreter returns the state's abstraction immediately. -/

/-- A lambda at the base depth returns its abstraction. -/
theorem αTraces_lam (ρ : Env Addr) (μ : LK.Heap) (κ : LK.Cont) (x : Var) (e : Exp) :
    ⊢ αTraces κ (.lam x e, ρ, μ, κ)
        (D.unfold (eval (.lam x e) (αEnv ρ μ)) (αHeap μ)) := by
  have hstop : LK.stop κ.depth (.lam x e, ρ, μ, κ) := LK.stop_of_isAnswer rfl μ κ
  have htr : D.unfold (eval (.lam x e) (αEnv ρ μ)) (αHeap μ)
      ≡ Trace.ret (Value.fn (Later.next
          (ofe_fun a => Domain.step .app2 (eval e (αEnv ρ μ)[x ↦ a]))), αHeap μ) := by
    simp only [eval, domain_fn_D]
    exact D.fn_run _ _
  refine .trans ?_ (αTraces_proper κ _ htr).2
  refine .trans ?_ (αTraces_ret κ hstop _).2
  have hα : αRet κ (.lam x e, ρ, μ, κ)
      = (Value.fn (Later.next
          (ofe_fun a => Domain.step .app2 (eval e (αEnv ρ μ)[x ↦ a]))), αHeap μ) := by
    simp [αRet, αValue, heapOf]
  rw [hα]
  exact internalEq.refl

/-- A constructor application at the base depth returns its abstraction. -/
theorem αTraces_conapp (ρ : Env Addr) (μ : LK.Heap) (κ : LK.Cont) (K : ConTag)
    (xs : List Var) :
    ⊢ αTraces κ (.conapp K xs, ρ, μ, κ)
        (D.unfold (eval (.conapp K xs) (αEnv ρ μ)) (αHeap μ)) := by
  have hstop : LK.stop κ.depth (.conapp K xs, ρ, μ, κ) := LK.stop_conapp K xs ρ μ κ
  have hα : ∀ v, ((αEnv ρ μ)[xs]?).elim Value.stuck
        (fun ds => Value.con K (ds.map Later.next)) = v →
      αRet κ (.conapp K xs, ρ, μ, κ) = (v, αHeap μ) := by
    intro v hv
    simp [αRet, αValue, heapOf, hv]
  cases hds : (αEnv ρ μ)[xs]? with
  | none =>
    have htr : D.unfold (eval (.conapp K xs) (αEnv ρ μ)) (αHeap μ)
        ≡ Trace.ret (Value.stuck, αHeap μ) := by
      simp only [eval, hds, Option.elim, domain_stuck_D, D.stuck]
      exact D.ret_run _ _
    refine .trans ?_ (αTraces_proper κ _ htr).2
    refine .trans ?_ (αTraces_ret κ hstop _).2
    rw [hα Value.stuck (by rw [hds]; rfl)]
    exact internalEq.refl
  | some ds =>
    have htr : D.unfold (eval (.conapp K xs) (αEnv ρ μ)) (αHeap μ)
        ≡ Trace.ret (Value.con K (ds.map Later.next), αHeap μ) := by
      simp only [eval, hds, Option.elim, domain_con_D]
      exact D.con_run _ _ _
    refine .trans ?_ (αTraces_proper κ _ htr).2
    refine .trans ?_ (αTraces_ret κ hstop _).2
    rw [hα (Value.con K (ds.map Later.next)) (by rw [hds]; rfl)]
    exact internalEq.refl

/-! ## The main theorem's Löb statement and interior-run invariant -/

/-- The statement Löb induction recurses on: from every well-formed
    configuration, the machine weakly bisimulates the interpreter run on the
    configuration's abstraction, interior to its own stack. -/
def NeedLK : SiProp :=
  iprop(∀ (e : Exp) (ρ : Env Addr) (μ : LK.Heap) (κ : LK.Cont),
    ⌜LK.WF (e, ρ, μ, κ)⌝ →
    αTraces κ (e, ρ, μ, κ) (D.unfold (eval e (αEnv ρ μ)) (αHeap μ)))

/-- The pure facts an interior run preserves: well-addressedness, stack
    extension of the base frame, and tag-preserving evolution of the base
    heap. -/
def Inv (μ₀ : LK.Heap) (κ₁ : LK.Cont) (σ : LK.State) : Prop :=
  LK.WF σ ∧ κ₁.Ext (LK.contOf σ) ∧ LK.Heap.Le μ₀ (heapOf σ)

theorem Inv.step {μ₀ : LK.Heap} {κ₁ : LK.Cont}
    {σ σ' : LK.State} (hs : LK.step σ = some σ')
    (hstop : LK.stop κ₁.depth σ = false) (h : Inv μ₀ κ₁ σ) :
    Inv μ₀ κ₁ σ' :=
  ⟨LK.WF.step hs h.1, LK.Cont.Ext.step hs hstop h.2.1,
   h.2.2.trans (LK.step_heapLe hs)⟩

theorem Inv.init {σ : LK.State} (hWF : LK.WF σ) (κ₁ : LK.Cont)
    (h : LK.contOf σ = κ₁) : Inv (heapOf σ) κ₁ σ :=
  ⟨hWF, h ▸ .refl, LK.Heap.Le.refl _⟩

/-! ## The continuations spliced at interior stops

`αTraces_bind`'s `Hk` obligation, one lemma per stack frame. The stuck arm is
shared: the machine has halted, and every frame's continuation returns a
`stuck` value with the heap unchanged. -/

/-- At a stuck stop the continuation sees the stuck value and returns it with
    the heap unchanged; the machine has already halted. -/
theorem αTraces_kStuck (κ₀ : LK.Cont) {κ₁ : LK.Cont} {σs : LK.State} (hd : κ₀.depth < κ₁.depth)
    (hext : κ₁.Ext (LK.contOf σs)) (hsN : LK.step σs = none)
    (hbal : (LK.isAnswer σs.2.1 σs.1 && ((LK.contOf σs).depth == κ₁.depth)) = false)
    (k : VH -n> Trace VH)
    (hk : k (Value.stuck, αHeap (heapOf σs))
      ≡ Trace.ret (Value.stuck, αHeap (heapOf σs))) :
    ⊢ αTraces κ₀ σs (k (αRet κ₁ σs)) := by
  have hα : αRet κ₁ σs = (Value.stuck, αHeap (heapOf σs)) := by
    show (αValue κ₁ σs, αHeap (heapOf σs)) = _
    rw [αValue_eq_stuck hbal]
  have hstop : LK.stop κ₀.depth σs = true := by
    obtain ⟨es, ρs, μs, κs⟩ := σs
    simp [LK.stop, hsN]
  have hret : αRet κ₀ σs = (Value.stuck, αHeap (heapOf σs)) :=
    αRet_stuck (by have := hext.depth_le; omega)
  refine .trans ?_ (αTraces_proper κ₀ σs
    (show k (αRet κ₁ σs) ≡ Trace.ret (Value.stuck, αHeap (heapOf σs)) by
      rw [hα]; exact hk)).2
  refine .trans ?_ (αTraces_ret κ₀ hstop _).2
  rw [hret]
  exact internalEq.refl

/-- The balanced arm at an `upd` frame, shared by both value shapes: the
    control's eval returns its abstraction immediately, so the machine's `Upd`
    transition matches the continuation's `update` step and both sides
    memoize the same cell. -/
theorem αTraces_memoCont_val (a : Addr) (κ : LK.Cont) {es : Exp} {ρs : Env Addr}
    {μs : LK.Heap} {p : Var × Env Addr × Exp} (hp : μs.car a = some p)
    (hval : LK.isAnswer ρs es)
    (hs2 : LK.step (es, ρs, μs, .upd a κ)
      = some (es, ρs, μs.alter a (some (p.1, ρs, es)), κ))
    (hev : αEvents (es, ρs, μs, .upd a κ) = some .update)
    {v : Value D}
    (hαv : αValue (LK.Cont.upd a κ) (es, ρs, μs, .upd a κ) = v)
    (hstk : v.isStuck = false)
    (heval : eval es (αEnv ρs μs) = D.ret v)
    (hαv' : αValue κ (es, ρs, μs.alter a (some (p.1, ρs, es)), κ) = v) :
    ⊢ αTraces κ (es, ρs, μs, .upd a κ)
        (D.kCont (D.memo.cont a (D.memo a))
          (αRet (LK.Cont.upd a κ) (es, ρs, μs, .upd a κ))) := by
  have hnstop : LK.stop κ.depth (es, ρs, μs, .upd a κ) = false :=
    LK.stop_eq_false hs2 (Nat.lt_succ_self κ.depth)
  have hα : αRet (LK.Cont.upd a κ) (es, ρs, μs, .upd a κ) = (v, αHeap μs) := by
    show (αValue _ _, αHeap (heapOf _)) = _
    rw [hαv]
  rw [hα]
  refine .trans ?_ (αTraces_proper κ _
    (D.memoCont_run a (D.memo a) hstk (αHeap μs))).2
  refine .trans ?_ (αTraces_step κ hs2 (by simp [hnstop]) hev _).2
  refine .trans ?_ later_intro
  have hstop' : LK.stop κ.depth (es, ρs, μs.alter a (some (p.1, ρs, es)), κ) :=
    LK.stop_of_isAnswer hval _ κ
  refine .trans ?_ (αTraces_ret κ hstop' _).2
  have hret : αRet κ (es, ρs, μs.alter a (some (p.1, ρs, es)), κ)
      = (v, Heap.set (αHeap μs) a (D.memo a (Later.next (D.ret v)))) := by
    show (αValue _ _, αHeap (heapOf _)) = _
    rw [hαv']
    have hheap : αHeap (μs.alter a (some (p.1, ρs, es)))
        = Heap.set (αHeap μs) a (D.memo a (Later.next (eval es (αEnv ρs μs)))) :=
      αHeap_alter_same_tag hp rfl
    show (v, αHeap (μs.alter a (some (p.1, ρs, es)))) = _
    rw [hheap, heval]
  rw [hret]
  exact internalEq.refl

/-- The memo continuation matches the interior run's exit at an `upd` frame. -/
theorem αTraces_memoCont (a : Addr) (κ : LK.Cont)
    (σs : LK.State) (vμ : VH)
    (hstop : LK.stop (LK.Cont.upd a κ).depth σs)
    (hWF : LK.WF σs)
    (hext : (LK.Cont.upd a κ).Ext (LK.contOf σs)) :
    iprop(vμ ≡ αRet (LK.Cont.upd a κ) σs) ⊢
      αTraces κ σs (D.kCont (D.memo.cont a (D.memo a)) vμ) := by
  haveI hne : NonExpansive (fun w : VH =>
      αTraces κ σs (D.kCont (D.memo.cont a (D.memo a)) w)) :=
    ⟨fun {_ _ _} h => (αTraces κ σs).ne.ne
      ((D.kCont (D.memo.cont a (D.memo a))).ne.ne h)⟩
  refine internalEq.rewrite' (fun w : VH =>
      αTraces κ σs (D.kCont (D.memo.cont a (D.memo a)) w))
    internalEq.symm (LR.of_empValid ?_)
  cases hbal : (LK.isAnswer σs.2.1 σs.1 && ((LK.contOf σs).depth == (LK.Cont.upd a κ).depth)) with
  | false =>
    have hsN : LK.step σs = none := by
      obtain ⟨es, ρs, μs, κs⟩ := σs
      have h := hstop
      simp only [LK.stop, Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd h (by simp [hbal])
      · exact Option.isNone_iff_eq_none.mp h
    exact αTraces_kStuck κ (κ₁ := LK.Cont.upd a κ) (Nat.lt_succ_self κ.depth)
      hext hsN hbal _ (D.memoCont_run_stuck a (D.memo a) (αHeap (heapOf σs)))
  | true =>
    obtain ⟨es, ρs, μs, κs⟩ := σs
    obtain ⟨hval, hdep⟩ := Bool.and_eq_true_iff.mp hbal
    obtain rfl : κs = LK.Cont.upd a κ :=
      hext.eq_of_depth_le (Nat.le_of_eq (by simpa using hdep))
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hWF.2.2.1
    cases es with
    | lam x' b' =>
      have hE : αEnv ρs (μs.alter a (some (p.1, ρs, Exp.lam x' b'))) = αEnv ρs μs :=
        αEnv_alter_same_tag hp rfl
      refine αTraces_memoCont_val a κ hp rfl (by simp [LK.step, hp]) rfl
        (v := Value.fn (Later.next (ofe_fun d => Domain.step .app2
          (eval b' (αEnv ρs μs)[x' ↦ d]))))
        (by simp [αValue]) rfl ?_ ?_
      · simp only [eval, domain_fn_D]
        rfl
      · simp [αValue, hE]
    | conapp K' xs' =>
      have hE : αEnv ρs (μs.alter a (some (p.1, ρs, Exp.conapp K' xs'))) = αEnv ρs μs :=
        αEnv_alter_same_tag hp rfl
      obtain ⟨addrs, has⟩ := Option.isSome_iff_exists.mp
        (show (ρs[xs']?).isSome by simpa [LK.isAnswer] using hval)
      obtain ⟨ds, hds, _⟩ := αEnv_getMany_some hWF.1
        (show ρs[xs']? = some addrs from has)
      refine αTraces_memoCont_val a κ hp (by simp [LK.isAnswer, has])
        (by simp [LK.step, has, hp]) rfl
        (v := Value.con K' (ds.map Later.next)) ?_ rfl ?_ ?_
      · simp [αValue, hds]
      · simp only [eval, domain_con_D]
        rw [show (αEnv ρs μs)[xs']? = some ds from hds]
        rfl
      · simp [αValue, hE, hds]
    | ref x' => exact absurd hval (by simp [LK.isAnswer])
    | app e' x' => exact absurd hval (by simp [LK.isAnswer])
    | «case» eₛ' alts' => exact absurd hval (by simp [LK.isAnswer])
    | «let» x' e₁' e₂' => exact absurd hval (by simp [LK.isAnswer])

/-- The apply continuation matches the interior run's exit at an `ap` frame: a
    balanced lambda fires the machine's `App₂` into its body under the
    argument's abstraction, re-entering the recursive statement; a balanced
    constructor is stuck on both sides; a stuck stop passes through. -/
theorem αTraces_applyCont (a2 : Addr) (κ : LK.Cont)
    (dₐ : D) (σs : LK.State) (vμ : VH)
    (hstop : LK.stop (LK.Cont.ap a2 κ).depth σs)
    (hWF : LK.WF σs)
    (hext : (LK.Cont.ap a2 κ).Ext (LK.contOf σs))
    (hαa : αAddr (heapOf σs) a2 dₐ) :
    iprop(NeedLK ∧ vμ ≡ αRet (LK.Cont.ap a2 κ) σs) ⊢
      αTraces κ σs (D.kCont (D.applyCont dₐ) vμ) := by
  haveI hne : NonExpansive (fun w : VH =>
      αTraces κ σs (D.kCont (D.applyCont dₐ) w)) :=
    ⟨fun {_ _ _} h => (αTraces κ σs).ne.ne ((D.kCont (D.applyCont dₐ)).ne.ne h)⟩
  refine internalEq.rewrite' (fun w : VH =>
      αTraces κ σs (D.kCont (D.applyCont dₐ) w))
    (and_elim_r.trans internalEq.symm) (and_elim_l.trans ?_)
  cases hbal : (LK.isAnswer σs.2.1 σs.1 && ((LK.contOf σs).depth == (LK.Cont.ap a2 κ).depth)) with
  | false =>
    have hsN : LK.step σs = none := by
      obtain ⟨es, ρs, μs, κs⟩ := σs
      have h := hstop
      simp only [LK.stop, Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd h (by simp [hbal])
      · exact Option.isNone_iff_eq_none.mp h
    exact LR.of_empValid (αTraces_kStuck κ (κ₁ := LK.Cont.ap a2 κ)
      (Nat.lt_succ_self κ.depth) hext hsN hbal (D.kCont (D.applyCont dₐ))
      (D.ret_run Value.stuck _))
  | true =>
    obtain ⟨es, ρs, μs, κs⟩ := σs
    obtain ⟨hval, hdep⟩ := Bool.and_eq_true_iff.mp hbal
    obtain rfl : κs = LK.Cont.ap a2 κ :=
      hext.eq_of_depth_le (Nat.le_of_eq (by simpa using hdep))
    have hαa' : αAddr μs a2 dₐ := hαa
    cases es with
    | lam x' b' =>
      have hs2 : LK.step (Exp.lam x' b', ρs, μs, .ap a2 κ)
          = some (b', ρs[x' ↦ a2], μs, κ) := rfl
      have hev2 : αEvents (Exp.lam x' b', ρs, μs, .ap a2 κ) = some .app2 := rfl
      have hnstop : LK.stop κ.depth (Exp.lam x' b', ρs, μs, .ap a2 κ) = false :=
        LK.stop_eq_false hs2 (Nat.lt_succ_self κ.depth)
      have hα : αRet (LK.Cont.ap a2 κ) (Exp.lam x' b', ρs, μs, .ap a2 κ)
          = (Value.fn (Later.next (ofe_fun d => Domain.step .app2
              (eval b' (αEnv ρs μs)[x' ↦ d]))), αHeap μs) := by
        simp [αRet, αValue, heapOf]
      rw [hα]
      refine .trans ?_ (αTraces_proper κ _
        (D.invis_run (Later.next (Domain.step .app2
          (eval b' (αEnv ρs μs)[x' ↦ dₐ]))) (αHeap μs))).2
      refine .trans ?_ (αTraces_invis κ _ _).2
      refine .trans ?_ (later_mono ((αTraces_proper κ _
        (D.step_run .app2 (eval b' (αEnv ρs μs)[x' ↦ dₐ]) (αHeap μs))).trans
        (αTraces_step κ hs2 (by simp [hnstop]) hev2 _)).2)
      have hWF' : LK.WF (b', ρs[x' ↦ a2], μs, κ) := LK.WF.step hs2 hWF
      have hIH : (NeedLK : SiProp) ⊢ αTraces κ (b', ρs[x' ↦ a2], μs, κ)
          (D.unfold (eval b' (αEnv ρs[x' ↦ a2] μs)) (αHeap μs)) :=
        ((forall_elim b').trans ((forall_elim (ρs[x' ↦ a2])).trans
          ((forall_elim μs).trans (forall_elim κ)))).trans
          (pure_imp_elim hWF')
      rw [αEnv_extend_αAddr hαa'] at hIH
      exact hIH.trans (later_intro.trans later_intro)
    | conapp K' xs' =>
      have hsN : LK.step (Exp.conapp K' xs', ρs, μs, .ap a2 κ) = none := rfl
      have hstop2 : LK.stop κ.depth (Exp.conapp K' xs', ρs, μs, .ap a2 κ) := by
        simp [LK.stop, hsN]
      have hK : D.applyCont dₐ (αValue (LK.Cont.ap a2 κ)
          (Exp.conapp K' xs', ρs, μs, LK.Cont.ap a2 κ)) = D.stuck := by
        show D.applyCont dₐ (if (LK.Cont.ap a2 κ).depth = (LK.Cont.ap a2 κ).depth
          then ((αEnv ρs μs)[xs']?).elim Value.stuck
            (fun ds => Value.con K' (ds.map Later.next)) else Value.stuck) = D.stuck
        rw [if_pos rfl]
        cases (αEnv ρs μs)[xs']? <;> rfl
      have hret := αRet_stuck (σ := (Exp.conapp K' xs', ρs, μs, LK.Cont.ap a2 κ))
        (Nat.succ_ne_self κ.depth)
      refine LR.of_empValid ?_
      refine .trans ?_ (αTraces_proper κ _
        (show D.kCont (D.applyCont dₐ) (αRet (LK.Cont.ap a2 κ)
            (Exp.conapp K' xs', ρs, μs, LK.Cont.ap a2 κ))
            ≡ Trace.ret (Value.stuck, αHeap μs) by
          show D.unfold (D.applyCont dₐ (αValue (LK.Cont.ap a2 κ)
            (Exp.conapp K' xs', ρs, μs, LK.Cont.ap a2 κ))) (αHeap μs) ≡ _
          rw [hK]
          exact D.ret_run Value.stuck _)).2
      refine .trans ?_ (αTraces_ret κ hstop2 _).2
      rw [hret]
      exact internalEq.refl
    | ref x' => exact absurd hval (by simp [LK.isAnswer])
    | app e' x' => exact absurd hval (by simp [LK.isAnswer])
    | «case» eₛ' alts' => exact absurd hval (by simp [LK.isAnswer])
    | «let» x' e₁' e₂' => exact absurd hval (by simp [LK.isAnswer])

/-- The select continuation matches the interior run's exit at a `sel` frame:
    a balanced constructor with a matching alternative fires the machine's
    `Case₂` into the branch under the fields' abstractions, re-entering the
    recursive statement; a missing alternative, an unbound field, or a
    balanced lambda is stuck on both sides; a stuck stop passes through. -/
theorem αTraces_selCont (ρf : Env Addr) (alts : List Alt)
    (κ : LK.Cont) (ρd : Env D) (σs : LK.State) (vμ : VH)
    (hstop : LK.stop (LK.Cont.sel ρf alts κ).depth σs)
    (hWF : LK.WF σs)
    (hext : (LK.Cont.sel ρf alts κ).Ext (LK.contOf σs))
    (hρd : αEnv ρf (heapOf σs) = ρd) :
    iprop(NeedLK ∧ vμ ≡ αRet (LK.Cont.sel ρf alts κ) σs) ⊢
      αTraces κ σs (D.kCont (D.selectCont (alts.map (evalAlt ρd))) vμ) := by
  haveI hne : NonExpansive (fun w : VH =>
      αTraces κ σs (D.kCont (D.selectCont (alts.map (evalAlt ρd))) w)) :=
    ⟨fun {_ _ _} h => (αTraces κ σs).ne.ne
      ((D.kCont (D.selectCont (alts.map (evalAlt ρd)))).ne.ne h)⟩
  refine internalEq.rewrite' (fun w : VH =>
      αTraces κ σs (D.kCont (D.selectCont (alts.map (evalAlt ρd))) w))
    (and_elim_r.trans internalEq.symm) (and_elim_l.trans ?_)
  cases hbal : (LK.isAnswer σs.2.1 σs.1 && ((LK.contOf σs).depth == (LK.Cont.sel ρf alts κ).depth)) with
  | false =>
    have hsN : LK.step σs = none := by
      obtain ⟨es, ρs, μs, κs⟩ := σs
      have h := hstop
      simp only [LK.stop, Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd h (by simp [hbal])
      · exact Option.isNone_iff_eq_none.mp h
    exact LR.of_empValid (αTraces_kStuck κ (κ₁ := LK.Cont.sel ρf alts κ)
      (Nat.lt_succ_self κ.depth) hext hsN hbal
      (D.kCont (D.selectCont (alts.map (evalAlt ρd)))) (D.ret_run Value.stuck _))
  | true =>
    obtain ⟨es, ρs, μs, κs⟩ := σs
    obtain ⟨hval, hdep⟩ := Bool.and_eq_true_iff.mp hbal
    obtain rfl : κs = LK.Cont.sel ρf alts κ :=
      hext.eq_of_depth_le (Nat.le_of_eq (by simpa using hdep))
    have hρd' : αEnv ρf μs = ρd := hρd
    cases es with
    | lam x' b' =>
      have hsN : LK.step (Exp.lam x' b', ρs, μs, .sel ρf alts κ) = none := rfl
      have hstop2 : LK.stop κ.depth (Exp.lam x' b', ρs, μs, .sel ρf alts κ) := by
        simp [LK.stop, hsN]
      have hK : D.selectCont (alts.map (evalAlt ρd))
          (αValue (LK.Cont.sel ρf alts κ)
            (Exp.lam x' b', ρs, μs, LK.Cont.sel ρf alts κ)) = D.stuck := by
        show D.selectCont _ (if (LK.Cont.sel ρf alts κ).depth
            = (LK.Cont.sel ρf alts κ).depth
          then Value.fn (Later.next (ofe_fun d => Domain.step .app2
            (eval b' (αEnv ρs μs)[x' ↦ d]))) else Value.stuck) = D.stuck
        rw [if_pos rfl]
        rfl
      have hret := αRet_stuck (σ := (Exp.lam x' b', ρs, μs, LK.Cont.sel ρf alts κ))
        (Nat.succ_ne_self κ.depth)
      refine LR.of_empValid ?_
      refine .trans ?_ (αTraces_proper κ _
        (show D.kCont (D.selectCont (alts.map (evalAlt ρd)))
            (αRet (LK.Cont.sel ρf alts κ)
              (Exp.lam x' b', ρs, μs, LK.Cont.sel ρf alts κ))
            ≡ Trace.ret (Value.stuck, αHeap μs) by
          show D.unfold (D.selectCont (alts.map (evalAlt ρd))
            (αValue (LK.Cont.sel ρf alts κ)
              (Exp.lam x' b', ρs, μs, LK.Cont.sel ρf alts κ))) (αHeap μs) ≡ _
          rw [hK]
          exact D.ret_run Value.stuck _)).2
      refine .trans ?_ (αTraces_ret κ hstop2 _).2
      rw [hret]
      exact internalEq.refl
    | conapp K' xs' =>
      obtain ⟨addrs, hAs⟩ := Option.isSome_iff_exists.mp
        (show (ρs[xs']?).isSome by simpa [LK.isAnswer] using hval)
      obtain ⟨ds₂, hds₂, hF⟩ := αEnv_getMany_some hWF.1 hAs
      have hα : αRet (LK.Cont.sel ρf alts κ)
          (Exp.conapp K' xs', ρs, μs, LK.Cont.sel ρf alts κ)
          = (Value.con K' (ds₂.map Later.next), αHeap μs) := by
        simp [αRet, αValue, heapOf, hds₂]
      rw [hα]
      cases halt : alts.find? (·.con == K') with
      | none =>
        have hsN : LK.step (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ) = none := by
          simp [LK.step, halt]
        have hstop2 : LK.stop κ.depth (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ) := by
          simp [LK.stop, hsN]
        have hret := αRet_stuck
          (σ := (Exp.conapp K' xs', ρs, μs, LK.Cont.sel ρf alts κ))
          (Nat.succ_ne_self κ.depth)
        refine LR.of_empValid ?_
        refine .trans ?_ (αTraces_proper κ _
          (show D.kCont (D.selectCont (alts.map (evalAlt ρd)))
              (Value.con K' (ds₂.map Later.next), αHeap μs)
              ≡ Trace.ret (Value.stuck, αHeap μs) by
            show D.unfold (D.selectCont (alts.map (evalAlt ρd))
              (Value.con K' (ds₂.map Later.next))) (αHeap μs) ≡ _
            rw [D.selectCont_con, evalAlts_find, halt]
            exact D.ret_run Value.stuck _)).2
        refine .trans ?_ (αTraces_ret κ hstop2 _).2
        rw [hret]
        exact internalEq.refl
      | some alt =>
        have hlen2 : addrs.length = ds₂.length := forall₂_length hF
        by_cases hlen : alt.vars.length = addrs.length
        · -- matching arity: the machine's `Case₂` matches the branch's guard
          have hlenD : ds₂.length = alt.vars.length := hlen2 ▸ hlen.symm
          have hs2 : LK.step (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ)
              = some (alt.rhs, ρf[alt.vars ↦* addrs], μs, κ) := by
            simp [LK.step, halt, hAs, hlen]
          have hev2 : αEvents (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ)
              = some .case2 := rfl
          have hnstop : LK.stop κ.depth (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ)
              = false := LK.stop_eq_false hs2 (Nat.lt_succ_self κ.depth)
          refine .trans ?_ (αTraces_proper κ _
            (show D.kCont (D.selectCont (alts.map (evalAlt ρd)))
                (Value.con K' (ds₂.map Later.next), αHeap μs)
                ≡ Trace.invis (laterMap (D.runAt (αHeap μs)) (Later.next
                    (Domain.step .case2 (eval alt.rhs ρd[alt.vars ↦* ds₂])))) by
              show D.unfold (D.selectCont (alts.map (evalAlt ρd))
                (Value.con K' (ds₂.map Later.next))) (αHeap μs) ≡ _
              rw [D.selectCont_con, evalAlts_find, halt]
              show D.unfold (D.invis (Later.next ((evalAlt ρd alt).2.2 ds₂)))
                (αHeap μs) ≡ _
              rw [show (evalAlt ρd alt).2.2 ds₂
                = Domain.step .case2 (eval alt.rhs ρd[alt.vars ↦* ds₂])
                from if_pos hlenD]
              exact D.invis_run _ _)).2
          refine .trans ?_ (αTraces_invis κ _ _).2
          refine .trans ?_ (later_mono ((αTraces_proper κ _
            (D.step_run .case2 (eval alt.rhs ρd[alt.vars ↦* ds₂]) (αHeap μs))).trans
            (αTraces_step κ hs2 (by simp [hnstop]) hev2 _)).2)
          have hWF' : LK.WF (alt.rhs, ρf[alt.vars ↦* addrs], μs, κ) :=
            LK.WF.step hs2 hWF
          have hIH : (NeedLK : SiProp) ⊢
              αTraces κ (alt.rhs, ρf[alt.vars ↦* addrs], μs, κ)
                (D.unfold (eval alt.rhs (αEnv ρf[alt.vars ↦* addrs] μs)) (αHeap μs)) :=
            ((forall_elim alt.rhs).trans ((forall_elim (ρf[alt.vars ↦* addrs])).trans
              ((forall_elim μs).trans (forall_elim κ)))).trans
              (pure_imp_elim hWF')
          rw [αEnv_extendMany_αAddr hF, hρd'] at hIH
          exact hIH.trans (later_intro.trans later_intro)
        · -- arity mismatch: the branch is stuck behind its guard, and the
          -- machine's `Case₂` is denied
          have hlenD : ¬ ds₂.length = alt.vars.length :=
            fun h => hlen (h.symm.trans hlen2.symm)
          have hsN : LK.step (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ) = none := by
            simp [LK.step, halt, hAs, hlen]
          have hstop2 : LK.stop κ.depth (Exp.conapp K' xs', ρs, μs, .sel ρf alts κ) := by
            simp [LK.stop, hsN]
          have hret := αRet_stuck
            (σ := (Exp.conapp K' xs', ρs, μs, LK.Cont.sel ρf alts κ))
            (Nat.succ_ne_self κ.depth)
          refine LR.of_empValid ?_
          refine .trans ?_ (αTraces_proper κ _
            (show D.kCont (D.selectCont (alts.map (evalAlt ρd)))
                (Value.con K' (ds₂.map Later.next), αHeap μs)
                ≡ Trace.invis (laterMap (D.runAt (αHeap μs))
                    (Later.next Domain.stuck)) by
              show D.unfold (D.selectCont (alts.map (evalAlt ρd))
                (Value.con K' (ds₂.map Later.next))) (αHeap μs) ≡ _
              rw [D.selectCont_con, evalAlts_find, halt]
              show D.unfold (D.invis (Later.next ((evalAlt ρd alt).2.2 ds₂)))
                (αHeap μs) ≡ _
              rw [show (evalAlt ρd alt).2.2 ds₂ = Domain.stuck from if_neg hlenD]
              exact D.invis_run _ _)).2
          refine .trans ?_ (αTraces_invis κ _ _).2
          refine .trans ?_ later_intro
          refine .trans ?_ (αTraces_proper κ _
            (D.ret_run Value.stuck (αHeap μs))).2
          refine .trans ?_ (αTraces_ret κ hstop2 _).2
          rw [hret]
          exact internalEq.refl
    | ref x' => exact absurd hval (by simp [LK.isAnswer])
    | app e' x' => exact absurd hval (by simp [LK.isAnswer])
    | «case» eₛ' alts' => exact absurd hval (by simp [LK.isAnswer])
    | «let» x' e₁' e₂' => exact absurd hval (by simp [LK.isAnswer])

/-! ## The main theorem -/

/-- The by-need interpreter abstracts the LK machine
    (`thm:need-abstracts-lk`): from every well-addressed configuration, the
    machine's maximal interior run weakly bisimulates the interpreter run on
    the configuration's abstraction. -/
theorem need_abstracts_lk : ⊢ NeedLK := by
  refine Entails.trans ?_ loeb
  refine imp_intro ?_
  refine .trans and_elim_r ?_
  show iprop(▷ NeedLK) ⊢ NeedLK
  refine forall_intro fun e => forall_intro fun ρ => forall_intro fun μ =>
    forall_intro fun κ => imp_intro ?_
  refine pure_elim (LK.WF (e, ρ, μ, κ)) and_elim_r fun hWF => ?_
  cases e with
  | lam x b => exact LR.of_empValid (αTraces_lam ρ μ κ x b)
  | conapp K xs => exact LR.of_empValid (αTraces_conapp ρ μ κ K xs)
  | ref x =>
    cases hget : ρ.get x with
    | none =>
      have hs : LK.step (Exp.ref x, ρ, μ, κ) = none := by simp [LK.step, hget]
      have hstop : LK.stop κ.depth (Exp.ref x, ρ, μ, κ) := by simp [LK.stop, hs]
      have htr : D.unfold (eval (Exp.ref x) (αEnv ρ μ)) (αHeap μ)
          ≡ Trace.ret (Value.stuck, αHeap μ) := by
        rw [eval_ref, αEnv_get_none hget]
        exact D.ret_run _ _
      have hret : αRet κ (Exp.ref x, ρ, μ, κ) = (Value.stuck, αHeap μ) := by
        simp [αRet, αValue, heapOf]
      refine LR.of_empValid ?_
      refine .trans ?_ (αTraces_proper κ _ htr).2
      refine .trans ?_ (αTraces_ret κ hstop _).2
      rw [hret]
      exact internalEq.refl
    | some a =>
      cases hp : μ.car a with
      | none =>
        have hs : LK.step (Exp.ref x, ρ, μ, κ) = none := by simp [LK.step, hget, hp]
        have hstop : LK.stop κ.depth (Exp.ref x, ρ, μ, κ) := by simp [LK.stop, hs]
        have htr : D.unfold (eval (Exp.ref x) (αEnv ρ μ)) (αHeap μ)
            ≡ Trace.ret (Value.stuck, αHeap μ) := by
          rw [eval_ref, αEnv_get_undef hget hp]
          exact D.ret_run _ _
        have hret : αRet κ (Exp.ref x, ρ, μ, κ) = (Value.stuck, αHeap μ) := by
          simp [αRet, αValue, heapOf]
        refine LR.of_empValid ?_
        refine .trans ?_ (αTraces_proper κ _ htr).2
        refine .trans ?_ (αTraces_ret κ hstop _).2
        rw [hret]
        exact internalEq.refl
      | some p =>
        obtain ⟨y, ρ', e'⟩ := p
        have hs : LK.step (Exp.ref x, ρ, μ, κ) = some (e', ρ', μ, .upd a κ) := by
          simp [LK.step, hget, hp]
        have hev : αEvents (Exp.ref x, ρ, μ, κ) = some (.look y) := by
          simp [αEvents, hget, hp]
        have hnstop : LK.stop κ.depth (Exp.ref x, ρ, μ, κ) = false := by
          simp [LK.stop, hs, LK.isAnswer]
        have htr : D.unfold (eval (Exp.ref x) (αEnv ρ μ)) (αHeap μ)
            ≡ Trace.step (.look y)
                (laterMap (D.runAt (αHeap μ)) (Later.next (fetch a))) := by
          rw [eval_ref, αEnv_get_eq hget hp]
          exact D.step_run _ _ _
        refine .trans ?_ (αTraces_proper κ _ htr).2
        refine .trans ?_ (αTraces_step κ hs (by simp [hnstop]) hev _).2
        refine .trans and_elim_l (later_mono ?_)
        have hWF' : LK.WF (e', ρ', μ, .upd a κ) := LK.WF.step hs hWF
        have hcar : (αHeap μ).car a
            = some (D.memo a (Later.next (eval e' (αEnv ρ' μ)))) := αHeap_car hp
        refine .trans ?_ (αTraces_proper κ _ (fetch_run_some hcar)).2
        refine .trans ?_ (αTraces_invis κ _ _).2
        refine .trans later_intro (later_mono ?_)
        have hmemo : (D.memo a (Later.next (eval e' (αEnv ρ' μ)))).car
            ≡ D.bind (eval e' (αEnv ρ' μ)) (D.memo.cont a (D.memo a)) :=
          Productive.later_equiv_car
            ((D.memo_unfold a) (Later.next (eval e' (αEnv ρ' μ))))
        refine .trans ?_ (αTraces_proper κ _
          (((D.unfold.ne.eqv hmemo) (αHeap μ)).trans
            (D.bind_run (eval e' (αEnv ρ' μ)) (D.memo.cont a (D.memo a))
              (αHeap μ)))).2
        refine .trans (and_intro .rfl ?_) (αTraces_bind NeedLK
          (D.kCont (D.memo.cont a (D.memo a))) κ (LK.Cont.upd a κ)
          (Nat.lt_succ_self κ.depth) (Inv μ (LK.Cont.upd a κ))
          (fun _ _ hs' hstop' h => Inv.step hs' hstop' h)
          (fun _ h => h.2.1)
          (fun σs vμ hstop hI => and_elim_r.trans
            (αTraces_memoCont a κ σs vμ hstop hI.1 hI.2.1))
          (e', ρ', μ, LK.Cont.upd a κ)
          (D.unfold (eval e' (αEnv ρ' μ)) (αHeap μ))
          ⟨hWF', .refl, LK.Heap.Le.refl μ⟩)
        exact ((forall_elim e').trans ((forall_elim ρ').trans ((forall_elim μ).trans
          (forall_elim (LK.Cont.upd a κ))))).trans (pure_imp_elim hWF')
  | app e' x =>
    cases hget : ρ.get x with
    | none =>
      have hs : LK.step (Exp.app e' x, ρ, μ, κ) = none := by simp [LK.step, hget]
      have hstop : LK.stop κ.depth (Exp.app e' x, ρ, μ, κ) := by simp [LK.stop, hs]
      have htr : D.unfold (eval (Exp.app e' x) (αEnv ρ μ)) (αHeap μ)
          ≡ Trace.ret (Value.stuck, αHeap μ) := by
        rw [eval_app, αEnv_get_none hget]
        exact D.ret_run _ _
      have hret : αRet κ (Exp.app e' x, ρ, μ, κ) = (Value.stuck, αHeap μ) := by
        simp [αRet, αValue, heapOf]
      refine LR.of_empValid ?_
      refine .trans ?_ (αTraces_proper κ _ htr).2
      refine .trans ?_ (αTraces_ret κ hstop _).2
      rw [hret]
      exact internalEq.refl
    | some a2 =>
      obtain ⟨p2, hp2⟩ := Option.isSome_iff_exists.mp (hWF.1 x a2 hget)
      have hs : LK.step (Exp.app e' x, ρ, μ, κ) = some (e', ρ, μ, .ap a2 κ) := by
        simp [LK.step, hget]
      have hev : αEvents (Exp.app e' x, ρ, μ, κ) = some .app1 := rfl
      have hnstop : LK.stop κ.depth (Exp.app e' x, ρ, μ, κ) = false := by
        simp [LK.stop, hs, LK.isAnswer]
      have htr : D.unfold (eval (Exp.app e' x) (αEnv ρ μ)) (αHeap μ)
          ≡ Trace.step .app1 (laterMap (D.runAt (αHeap μ)) (Later.next
              (Domain.apply (eval e' (αEnv ρ μ))
                (D.step (.look p2.1) (fetch a2))))) := by
        rw [eval_app, αEnv_get_eq hget hp2]
        exact D.step_run _ _ _
      refine .trans ?_ (αTraces_proper κ _ htr).2
      refine .trans ?_ (αTraces_step κ hs (by simp [hnstop]) hev _).2
      refine .trans and_elim_l (later_mono ?_)
      have hWF' : LK.WF (e', ρ, μ, .ap a2 κ) := LK.WF.step hs hWF
      refine .trans ?_ (αTraces_proper κ _
        (D.bind_run (eval e' (αEnv ρ μ))
          (D.applyCont (D.step (.look p2.1) (fetch a2))) (αHeap μ))).2
      refine .trans (and_intro .rfl ?_) (αTraces_bind NeedLK
        (D.kCont (D.applyCont (D.step (.look p2.1) (fetch a2)))) κ
        (LK.Cont.ap a2 κ) (Nat.lt_succ_self κ.depth) (Inv μ (LK.Cont.ap a2 κ))
        (fun _ _ hs' hstop' h => Inv.step hs' hstop' h)
        (fun _ h => h.2.1)
        (fun σs vμ hstop hI => αTraces_applyCont a2 κ
          (D.step (.look p2.1) (fetch a2)) σs vμ hstop hI.1 hI.2.1
          (αAddr.heapLe hI.2.2 ⟨p2, hp2, rfl⟩))
        (e', ρ, μ, LK.Cont.ap a2 κ) (D.unfold (eval e' (αEnv ρ μ)) (αHeap μ))
        ⟨hWF', .refl, LK.Heap.Le.refl μ⟩)
      exact ((forall_elim e').trans ((forall_elim ρ).trans ((forall_elim μ).trans
        (forall_elim (LK.Cont.ap a2 κ))))).trans (pure_imp_elim hWF')
  | «case» eₛ alts =>
    have hs : LK.step (Exp.«case» eₛ alts, ρ, μ, κ) = some (eₛ, ρ, μ, .sel ρ alts κ) :=
      rfl
    have hev : αEvents (Exp.«case» eₛ alts, ρ, μ, κ) = some .case1 := rfl
    have hnstop : LK.stop κ.depth (Exp.«case» eₛ alts, ρ, μ, κ) = false := by
      simp [LK.stop, hs, LK.isAnswer]
    have htr : D.unfold (eval (Exp.«case» eₛ alts) (αEnv ρ μ)) (αHeap μ)
        ≡ Trace.step .case1 (laterMap (D.runAt (αHeap μ)) (Later.next
            (Domain.select (eval eₛ (αEnv ρ μ)) (alts.map (evalAlt (αEnv ρ μ)))))) := by
      rw [eval_case]
      exact D.step_run _ _ _
    refine .trans ?_ (αTraces_proper κ _ htr).2
    refine .trans ?_ (αTraces_step κ hs (by simp [hnstop]) hev _).2
    refine .trans and_elim_l (later_mono ?_)
    have hWF' : LK.WF (eₛ, ρ, μ, .sel ρ alts κ) := LK.WF.step hs hWF
    refine .trans ?_ (αTraces_proper κ _
      (D.bind_run (eval eₛ (αEnv ρ μ))
        (D.selectCont (alts.map (evalAlt (αEnv ρ μ)))) (αHeap μ))).2
    refine .trans (and_intro .rfl ?_) (αTraces_bind NeedLK
      (D.kCont (D.selectCont (alts.map (evalAlt (αEnv ρ μ))))) κ
      (LK.Cont.sel ρ alts κ) (Nat.lt_succ_self κ.depth)
      (Inv μ (LK.Cont.sel ρ alts κ))
      (fun _ _ hs' hstop' h => Inv.step hs' hstop' h)
      (fun _ h => h.2.1)
      (fun σs vμ hstop hI => αTraces_selCont ρ alts κ (αEnv ρ μ) σs vμ hstop
        hI.1 hI.2.1 (αEnv_heapLe hWF.1 hI.2.2))
      (eₛ, ρ, μ, LK.Cont.sel ρ alts κ) (D.unfold (eval eₛ (αEnv ρ μ)) (αHeap μ))
      ⟨hWF', .refl, LK.Heap.Le.refl μ⟩)
    exact ((forall_elim eₛ).trans ((forall_elim ρ).trans ((forall_elim μ).trans
      (forall_elim (LK.Cont.sel ρ alts κ))))).trans (pure_imp_elim hWF')
  | «let» x e₁ e₂ =>
    have hs : LK.step (Exp.«let» x e₁ e₂, ρ, μ, κ)
        = some (e₂, ρ[x ↦ genMapLeast μ],
            μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)), κ) := rfl
    have hev : αEvents (Exp.«let» x e₁ e₂, ρ, μ, κ) = some .let1 := rfl
    have hnstop : LK.stop κ.depth (Exp.«let» x e₁ e₂, ρ, μ, κ) = false := by
      simp [LK.stop, hs, LK.isAnswer]
    have htr : D.unfold (eval (Exp.«let» x e₁ e₂) (αEnv ρ μ)) (αHeap μ)
        ≡ Trace.step .let1 (laterMap (D.runAt (αHeap μ)) (Later.next
            (Domain.bind
              (ofe_fun d => eval e₁ (αEnv ρ μ)[x ↦ Domain.step (.look x) d])
              (ofe_fun d => eval e₂ (αEnv ρ μ)[x ↦ Domain.step (.look x) d])))) := by
      rw [eval_let]
      exact D.step_run _ _ _
    refine .trans ?_ (αTraces_proper κ _ htr).2
    refine .trans ?_ (αTraces_step κ hs (by simp [hnstop]) hev _).2
    refine .trans and_elim_l (later_mono ?_)
    have hWF' := LK.WF.step hs hWF
    refine .trans ?_ (αTraces_proper κ _ (D.bindLet_run
      (ofe_fun d => eval e₁ (αEnv ρ μ)[x ↦ Domain.step (.look x) d])
      (ofe_fun d => eval e₂ (αEnv ρ μ)[x ↦ Domain.step (.look x) d]) (αHeap μ))).2
    have hIH : iprop(NeedLK) ⊢ αTraces κ
        (e₂, ρ[x ↦ genMapLeast μ],
          μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)), κ)
        (D.unfold (eval e₂ (αEnv (ρ[x ↦ genMapLeast μ])
            (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)))))
          (αHeap (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁))))) :=
      ((forall_elim e₂).trans ((forall_elim (ρ[x ↦ genMapLeast μ])).trans
        ((forall_elim (μ.alter (genMapLeast μ) (some (x, ρ[x ↦ genMapLeast μ], e₁)))).trans
          (forall_elim κ)))).trans (pure_imp_elim hWF')
    rw [αEnv_let hWF.1, αHeap_let hWF.1 hWF.2.1] at hIH
    rw [show Heap.nextFree (αHeap μ) = genMapLeast μ from nextFree_αHeap μ]
    exact hIH

/-- Adequacy at a closed, arity-consistent program: from `init e`, the
    machine's maximal run weakly bisimulates `evalByNeed` on the empty
    environment and heap. -/
theorem need_abstracts_lk_init (e : Exp) :
    ⊢ αTraces LK.Cont.stop (LK.init e) (D.unfold (evalByNeed e ρ₀) μ₀) := by
  have hρ : αEnv Env.empty Iris.GenMap.empty = ρ₀ := by
    funext y
    rfl
  have hμ : αHeap Iris.GenMap.empty = μ₀ := by
    apply GenMap.ext
    funext b
    rfl
  have h := ((need_abstracts_lk).trans
    ((forall_elim e).trans ((forall_elim Env.empty).trans
      ((forall_elim Iris.GenMap.empty).trans (forall_elim LK.Cont.stop))))).trans
    (pure_imp_elim (LK.WF.init e))
  rw [hρ, hμ] at h
  exact h

end Adequacy

end AbsDen
