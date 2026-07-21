import AbsDen.Domain
import AbsDen.Semantics

open Iris Iris.COFE OFE

/-! # The ByNeed `Domain D` instance

The denotational operations of `AbsDen/ByNeed.lean` over the solved domain
`D ≅ Heap(▶D) -n> Trace (Value(▶D) × Heap(▶D))`. Each `Domain D` field is bound to
its own top-level combinator of the same name (`step`, `stuck`, `fn`, `apply`,
`con`, `select`, plus `bindLet` for the recursive `let`, since `D.bind` is the
trace-monad bind). Application is `.invis`-guarded; `let` allocates a fresh cell,
`memo`izes the rhs, and runs the body. -/

namespace AbsDen

abbrev Addr := Nat

instance : Inhabited (Later D) := ⟨Later.next default⟩

theorem laterNext_ne {α : Type _} [OFE α] {n} {a a' : α} (h : a ≡{n}≡ a') :
    Later.next a ≡{n}≡ Later.next a' := NonExpansive.ne (f := Later.next) h

/-- `Later.next` as a morphism (used to thunk constructor arguments). -/
def laterNextHom {α : Type _} [OFE α] : α -n> Later α := ⟨Later.next, inferInstance⟩

/-! ## Returning a value with the heap unchanged -/

def D.ret : Value D -n> D :=
  D.fold.comp ⟨fun v => ⟨fun μ => Trace.fold (.ret (v, μ)),
      ⟨fun {_ _ _} h => Trace.fold.ne.ne ⟨OFE.dist_eqv.refl v, h⟩⟩⟩,
    ⟨fun {_ _ _} hv => fun μ => Trace.fold.ne.ne ⟨hv, OFE.dist_eqv.refl μ⟩⟩⟩

def D.stuck : D := D.ret Value.stuck

/-- Run a thunked computation against a heap, producing a trace. -/
def D.runAt (μ : GenMap (Later D)) : D -n> Trace (ValueHeapOF D D) :=
  ⟨fun d => D.unfold d μ, ⟨fun {_ _ _} h => (D.unfold.ne.ne h) μ⟩⟩

theorem D.runAt_ne {n} {μ μ' : GenMap (Later D)} (h : μ ≡{n}≡ μ') :
    D.runAt μ ≡{n}≡ D.runAt μ' := fun d => (D.unfold d).ne.ne h

/-- Emit an event, then run the value one step later against the heap. -/
def D.step (ev : Event) : D -n> D :=
  ⟨fun d => D.fold ⟨fun μ => Trace.fold (.step ev (laterMap (D.runAt μ) (Later.next d))),
      ⟨fun {_ _ _} h => Trace.fold.ne.ne
        ⟨rfl, laterMap_ne (D.runAt_ne h) (Later.next d)⟩⟩⟩,
   ⟨fun {_ _ _} h => D.fold.ne.ne (fun μ => Trace.fold.ne.ne
      ⟨rfl, (laterMap (D.runAt μ)).ne.ne (laterNext_ne h)⟩)⟩⟩

/-- A silent `▶` step, threading the thunk against the heap. -/
def D.invis (dl : Later D) : D :=
  D.fold ⟨fun μ => Trace.fold (.invis (laterMap (D.runAt μ) dl)),
    ⟨fun {_ _ _} h => Trace.fold.ne.ne (laterMap_ne (D.runAt_ne h) dl)⟩⟩

theorem D.invis_ne {n} {dl dl' : Later D} (h : dl ≡{n}≡ dl') : D.invis dl ≡{n}≡ D.invis dl' :=
  D.fold.ne.ne (fun μ => Trace.fold.ne.ne ((laterMap (D.runAt μ)).ne.ne h))

/-! ## Value-returning operations -/

def D.fn : (D -n> D) -n> D :=
  ⟨fun f => D.ret (Value.fn (Later.next f)),
   ⟨fun {_ _ _} H => D.ret.ne.ne (ValueF.fn.ne.ne (laterNext_ne H))⟩⟩

def D.con (K : ConTag) : List D -n> D :=
  ⟨fun ds => D.ret (Value.con K (ds.map Later.next)),
   ⟨fun {_ _ _} H => D.ret.ne.ne ((ValueF.con.ne K).ne ((List.mapO laterNextHom).ne.ne H))⟩⟩

/-! ## Monadic bind (the trace+heap monad), used by `apply`/`select` -/

/-- The trace-level continuation of `bind k`: at a returned `(v, μ')`, run `k v`
    against `μ'`. -/
def D.kCont (k : Value D -n> D) : ValueHeapOF D D -n> Trace (ValueHeapOF D D) :=
  ⟨fun vμ => D.unfold (k vμ.1) vμ.2,
   ⟨fun {_ a b} h =>
      OFE.Dist.trans ((D.unfold.ne.ne (k.ne.ne h.1)) a.2) ((D.unfold (k b.1)).ne.ne h.2)⟩⟩

theorem D.kCont_ne {n} {k k' : Value D -n> D} (H : k ≡{n}≡ k') : D.kCont k ≡{n}≡ D.kCont k' :=
  fun vμ => (D.unfold.ne.ne (H vμ.1)) vμ.2

def D.bind (d : D) (k : Value D -n> D) : D :=
  D.fold ⟨fun μ => Trace.bind (D.kCont k) (D.unfold d μ),
    ⟨fun {_ _ _} h => (Trace.bind (D.kCont k)).ne.ne ((D.unfold d).ne.ne h)⟩⟩

theorem D.bind_ne_d {n} {d d' : D} (k : Value D -n> D) (h : d ≡{n}≡ d') :
    D.bind d k ≡{n}≡ D.bind d' k :=
  D.fold.ne.ne (fun μ => (Trace.bind (D.kCont k)).ne.ne ((D.unfold.ne.ne h) μ))

theorem D.bind_ne_k {n} (d : D) {k k' : Value D -n> D} (H : k ≡{n}≡ k') :
    D.bind d k ≡{n}≡ D.bind d k' :=
  D.fold.ne.ne (fun μ => Trace.bind_ne (D.kCont_ne H) (D.unfold d μ))

/-- `bind` is non-expansive in its continuation and in its scrutinee, as
    instances so `ne_solve` composes them under `ofe_fun`. -/
instance D.bind.ne_k (d : D) : NonExpansive (D.bind d) := ⟨fun {_ _ _} H => D.bind_ne_k d H⟩
instance D.bind.ne_d (k : Value D -n> D) : NonExpansive (fun d => D.bind d k) :=
  ⟨fun {_ _ _} h => D.bind_ne_d k h⟩

/-! ## Application -/

/-- Continuation of `apply da`: a function value is applied (guarded by `.invis`),
    everything else is stuck. -/
def D.applyCont (da : D) : Value D -n> D :=
  ⟨fun v => match v with
    | .stuck => D.stuck
    | .fn g => D.invis (Later.next (g.car da))
    | .con _ _ => D.stuck,
   ⟨fun {_ v v'} h => by
      cases v <;> cases v' <;> try exact False.elim h
      · exact OFE.dist_eqv.refl _
      · exact D.invis_ne (fun m hm => (h m hm) da)
      · exact OFE.dist_eqv.refl _⟩⟩

theorem D.applyCont_ne {n} {da da' : D} (h : da ≡{n}≡ da') :
    D.applyCont da ≡{n}≡ D.applyCont da' := by
  intro v
  cases v with
  | stuck => exact OFE.dist_eqv.refl _
  | fn g => exact D.invis_ne (fun m hm => g.car.ne.ne (h.lt hm))
  | con K ds => exact OFE.dist_eqv.refl _

instance D.applyCont.ne : NonExpansive D.applyCont := ⟨fun {_ _ _} h => D.applyCont_ne h⟩

def D.apply : D -n> D -n> D :=
  ofe_fun dv => ofe_fun da => D.bind dv (D.applyCont da)

/-- `n`-close thunk lists force to `m`-close value lists for every `m < n`
    (`Later` is a trivial wrapper, so forcing is `·.map (·.car)`). -/
theorem mapCar_distLater {n} {ds ds' : List (Later D)} (h : ds ≡{n}≡ ds')
    (m : Nat) (hm : m < n) : ds.map (·.car) ≡{m}≡ ds'.map (·.car) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons (hx m hm) ih

/-- `find?` with a dist-respecting predicate is non-expansive in the list. -/
theorem find?_ne {α : Type} [OFE α] {n} {p : α → Bool}
    (hp : ∀ {a b : α}, a ≡{n}≡ b → p a = p b) {l l' : List α} (h : l ≡{n}≡ l') :
    l.find? p ≡{n}≡ l'.find? p := by
  induction h with
  | nil => exact OFE.dist_eqv.refl _
  | @cons a b _ _ hab _ ih =>
      simp only [List.find?_cons, hp hab]
      split
      · exact some_dist_some.mpr hab
      · exact ih

/-- Running a matched alternative is non-expansive in both the stored arguments
    and the alternative: force the arguments (`·.map (·.car)`), apply the branch,
    and re-wrap under `.invis`. -/
theorem D.selectSome_ne {n} {ds ds' : List (Later D)} (hds : ds ≡{n}≡ ds')
    {p p' : ConTag × Nat × (List D -n> D)} (hp : p ≡{n}≡ p') :
    D.invis (Later.next (p.2.2 (ds.map (·.car)))) ≡{n}≡ D.invis (Later.next (p'.2.2 (ds'.map (·.car)))) :=
  D.invis_ne (fun m hm =>
    ofe_mor_car_ne.ne ((dist_snd (dist_snd hp)).lt hm) (mapCar_distLater hds m hm))

/-- The constructor tag carried by an alternative is discrete, so the match
    predicate `(·.1 == K)` respects `n`-equivalence of alternatives. -/
theorem altMatch_dist {n} {K : ConTag} {a b : ConTag × Nat × (List D -n> D)} (hab : a ≡{n}≡ b) :
    (a.1 == K) = (b.1 == K) := by rw [show a.1 = b.1 from dist_fst hab]

/-- Force the constructor arguments and run the matching alternative under
    `.invis`; a missing constructor is `stuck`. -/
def D.selectContFun (alts : List (ConTag × Nat × (List D -n> D))) (v : Value D) : D :=
  match v with
  | .con K ds =>
    (alts.find? (·.1 == K)).elim D.stuck
      (fun p => D.invis (Later.next (p.2.2 (ds.map (·.car)))))
  | _ => D.stuck

/-- `selectContFun` is non-expansive in the scrutinee value. -/
theorem D.selectContFun_ne_v {n} (alts : List (ConTag × Nat × (List D -n> D))) {v v' : Value D}
    (h : v ≡{n}≡ v') : D.selectContFun alts v ≡{n}≡ D.selectContFun alts v' := by
  cases v <;> cases v' <;> try exact False.elim h
  · exact OFE.dist_eqv.refl _
  · exact OFE.dist_eqv.refl _
  · obtain ⟨rfl, hds⟩ := h
    exact Option.elim_ne (· ≡{n}≡ ·) (fun _ _ hp => D.selectSome_ne hds hp)
      (OFE.dist_eqv.refl _) (OFE.dist_eqv.refl _)

/-- Run the matching alternative as a morphism in the scrutinee value. -/
def D.selectCont (alts : List (ConTag × Nat × (List D -n> D))) : Value D -n> D :=
  ⟨D.selectContFun alts, ⟨fun {_ _ _} h => D.selectContFun_ne_v alts h⟩⟩

/-- `selectCont` is non-expansive in the alternatives. -/
theorem D.selectCont_ne {n} {alts alts' : List (ConTag × Nat × (List D -n> D))} (h : alts ≡{n}≡ alts') :
    D.selectCont alts ≡{n}≡ D.selectCont alts' := by
  intro v
  show D.selectContFun alts v ≡{n}≡ D.selectContFun alts' v
  cases v with
  | stuck => exact OFE.dist_eqv.refl _
  | fn g => exact OFE.dist_eqv.refl _
  | con K ds =>
    exact Option.elim_ne (· ≡{n}≡ ·) (fun _ _ hp => D.selectSome_ne (OFE.dist_eqv.refl ds) hp)
      (OFE.dist_eqv.refl _) (find?_ne (fun hab => altMatch_dist hab) h)

instance D.selectCont.ne : NonExpansive D.selectCont := ⟨fun {_ _ _} h => D.selectCont_ne h⟩

/-- Constructor selection: force the scrutinee, then run the matching alternative. -/
def D.select : D -n> List (ConTag × Nat × (List D -n> D)) -n> D :=
  ofe_fun dv => ofe_fun alts => D.bind dv (D.selectCont alts)

/-! ## Heap operations -/

/-- The least free address; deterministic, so it agrees on `n`-close heaps. -/
def Heap.nextFree (μ : GenMap (Later D)) : Addr := genMapLeast μ

theorem Heap.nextFree_spec (μ : GenMap (Later D)) : μ.car (Heap.nextFree μ) = none :=
  genMapLeast_spec μ

theorem Heap.nextFree_eq {n} {μ μ' : GenMap (Later D)} (h : μ ≡{n}≡ μ') :
    Heap.nextFree μ = Heap.nextFree μ' :=
  genMapLeast_congr μ μ' (fun k => by
    have hk := h k
    constructor
    · intro hμ
      rcases hμ' : μ'.car k with _ | v'
      · rfl
      · rw [hμ, hμ'] at hk; exact hk.elim
    · intro hμ'
      rcases hμ : μ.car k with _ | v
      · rfl
      · rw [hμ, hμ'] at hk; exact hk.elim)

/-- Store a thunk at an address. -/
def Heap.set (μ : GenMap (Later D)) (a : Addr) (dl : Later D) : GenMap (Later D) :=
  μ.alter a (some dl)

theorem Heap.set_ne {n} (a : Addr) (dl : Later D) {μ μ' : GenMap (Later D)} (h : μ ≡{n}≡ μ') :
    Heap.set μ a dl ≡{n}≡ Heap.set μ' a dl := by
  intro k; simp only [Heap.set, GenMap.alter, Iris.alter]; split
  · exact OFE.dist_eqv.refl _
  · exact h k

theorem Heap.set_get (μ : GenMap (Later D)) (a : Addr) (dl : Later D) (k : Addr) :
    (Heap.set μ a dl).car k = if a = k then some dl else μ.car k := rfl

theorem Heap.set_ne_val {n} (μ : GenMap (Later D)) (a : Addr) {dl dl' : Later D} (h : dl ≡{n}≡ dl') :
    Heap.set μ a dl ≡{n}≡ Heap.set μ a dl' := by
  intro k; simp only [Heap.set, GenMap.alter, Iris.alter]; split
  · exact some_dist_some.mpr h
  · exact OFE.dist_eqv.refl _

/-- Look up an address: dereference the cell and run its thunk through a single
    silent step (the layer that opens the stored `▶D`), or get stuck on a free
    cell. -/
def fetch (a : Addr) : D :=
  D.fold ⟨fun μ => (μ.car a).elim (Trace.fold (.ret (Value.stuck, μ)))
      (fun dl => Trace.fold (.invis (laterMap (D.runAt μ) dl))),
    ⟨fun {n μ μ'} h => Option.elim_ne (· ≡{n}≡ ·)
      (fun dl dl' hdl => Trace.fold.ne.ne (TraceF.invis.ne.ne
        (OFE.Dist.trans (laterMap_ne (D.runAt_ne h) dl) ((laterMap (D.runAt μ')).ne.ne hdl))))
      (Trace.fold.ne.ne ⟨OFE.dist_eqv.refl Value.stuck, h⟩)
      (h a)⟩⟩

/-! ## Memoization (guarded recursion)

Faithful to the paper's `memo`: the first forcing that reaches a value emits
`update` and caches it behind a *memoized* thunk `D.memo a (▶(ret v))`, so the
recursion is genuine; a `stuck` result is passed on with the heap untouched.
The recursive `rec` sits under the outer `laterMap`'s `▶`, so the operator is
contractive and `D.memo` is its Banach fixpoint. -/

/-- The cell update a first forcing performs on reaching a value: emit `update`
    and return the value with its cell rewritten to the memoized thunk; `rec`
    is the guarded recursive `D.memo a`. -/
def D.memo.upd (a : Addr) (rec : Later D -n> Later D) (v : Value D) : D :=
  D.step .update (D.fold
    ⟨fun μ => Trace.fold (.ret (v, Heap.set μ a (rec (Later.next (D.ret v))))),
     ⟨fun {_ _ _} h => Trace.fold.ne.ne ⟨OFE.dist_eqv.refl v, Heap.set_ne a _ h⟩⟩⟩)

theorem D.memo.upd_ne_v {n} (a : Addr) (rec : Later D -n> Later D) {v v' : Value D}
    (hv : v ≡{n}≡ v') : D.memo.upd a rec v ≡{n}≡ D.memo.upd a rec v' :=
  (D.step .update).ne.ne (D.fold.ne.ne
    (fun μ => Trace.fold.ne.ne
      ⟨hv, Heap.set_ne_val μ a (rec.ne.ne (laterNext_ne (D.ret.ne.ne hv)))⟩))

theorem D.memo.upd_ne_rec {m} (a : Addr) {rec rec' : Later D -n> Later D}
    (H : rec ≡{m}≡ rec') (v : Value D) :
    D.memo.upd a rec v ≡{m}≡ D.memo.upd a rec' v :=
  (D.step .update).ne.ne (D.fold.ne.ne
    (fun μ => Trace.fold.ne.ne
      ⟨OFE.dist_eqv.refl v, Heap.set_ne_val μ a (H (Later.next (D.ret v)))⟩))

/-- The continuation a memoized thunk binds its stored computation with: a
    value updates its cell, a `stuck` result is returned with the heap
    untouched. -/
def D.memo.cont (a : Addr) (rec : Later D -n> Later D) : Value D -n> D :=
  ⟨fun v => match v with
    | .stuck => D.stuck
    | v => D.memo.upd a rec v,
   ⟨fun {_ v v'} hv => by
     cases v <;> cases v' <;> try exact False.elim hv
     · exact OFE.dist_eqv.refl _
     · exact D.memo.upd_ne_v a rec hv
     · exact D.memo.upd_ne_v a rec hv⟩⟩

theorem D.memo.cont_ne {m} (a : Addr) {rec rec' : Later D -n> Later D} (H : rec ≡{m}≡ rec') :
    D.memo.cont a rec ≡{m}≡ D.memo.cont a rec'
  | .stuck => OFE.dist_eqv.refl _
  | .fn _ => D.memo.upd_ne_rec a H _
  | .con _ _ => D.memo.upd_ne_rec a H _

/-- The contractive operator whose fixpoint is `D.memo a`: force the thunk and bind
    the cell-update, all under the outer guard. -/
def D.memo.op (a : Addr) (rec : Later D -n> Later D) : Later D -n> Later D :=
  laterMap ⟨fun dv => D.bind dv (D.memo.cont a rec),
            ⟨fun {_ _ _} hdv => D.bind_ne_d (D.memo.cont a rec) hdv⟩⟩

instance (a : Addr) : OFE.Contractive (D.memo.op a) where
  distLater_dist {_ _ _} H :=
    Trace.laterMap_contractive (fun m hm dv => D.bind_ne_k dv (D.memo.cont_ne a (H m hm)))

/-- Memoize a thunk: force once and, on reaching a value, emit `update` and
    cache it. -/
def D.memo (a : Addr) : Later D -n> Later D := (D.memo.op a).toContractiveHom.lazyFixpoint

theorem D.memo_unfold (a : Addr) : D.memo a ≡ D.memo.op a (D.memo a) :=
  fixpoint_unfold (D.memo.op a).toContractiveHom

theorem D.memo_ne {n} (a : Addr) {dl dl' : Later D} (h : dl ≡{n}≡ dl') :
    D.memo a dl ≡{n}≡ D.memo a dl' := (D.memo a).ne.ne h

/-! ## Recursive `let`: allocate, memoize the rhs, run the body -/

def D.bindLet : (D -n> D) -n> (D -n> D) -n> D :=
  ⟨fun rhs => ⟨fun body =>
      D.fold ⟨fun μ => D.unfold (body (fetch (Heap.nextFree μ)))
        (Heap.set μ (Heap.nextFree μ)
          (D.memo (Heap.nextFree μ) (Later.next (rhs (fetch (Heap.nextFree μ)))))),
        ⟨fun {_ _ _} h => by rw [Heap.nextFree_eq h]; exact (D.unfold _).ne.ne (Heap.set_ne _ _ h)⟩⟩,
      ⟨fun {_ _ _} H => D.fold.ne.ne (fun μ =>
        (D.unfold.ne.ne (H (fetch (Heap.nextFree μ))))
          (Heap.set μ (Heap.nextFree μ)
            (D.memo (Heap.nextFree μ) (Later.next (rhs (fetch (Heap.nextFree μ)))))))⟩⟩,
   ⟨fun {_ _ _} H => fun body => D.fold.ne.ne (fun μ =>
      (D.unfold (body (fetch (Heap.nextFree μ)))).ne.ne
        (Heap.set_ne_val μ (Heap.nextFree μ)
          (D.memo_ne (Heap.nextFree μ) (laterNext_ne (H (fetch (Heap.nextFree μ)))))))⟩⟩

/-! ## The `Domain D` instance -/

instance : Domain D where
  step := D.step
  stuck := D.stuck
  fn _ := D.fn
  apply := D.apply
  con := D.con
  select := D.select
  bind := D.bindLet

/-! ## Reduction lemmas (the evaluator's observable small-step behavior)

Each operation, run against a heap, unfolds to one trace layer. These are the
rules a trace-evaluation tactic would apply. -/

theorem D.unfold_fold_app (f : GenMap (Later D) -n> Trace (ValueHeapOF D D))
    (μ : GenMap (Later D)) : D.unfold (D.fold f) μ ≡ f μ := (D.unfold_fold f) μ

@[eval_simp] theorem D.ret_run (v : Value D) (μ : GenMap (Later D)) :
    D.unfold (D.ret v) μ ≡ Trace.ret (v, μ) := D.unfold_fold_app _ μ

@[eval_simp] theorem D.step_run (ev : Event) (d : D) (μ : GenMap (Later D)) :
    D.unfold (D.step ev d) μ ≡ Trace.step ev (laterMap (D.runAt μ) (Later.next d)) :=
  D.unfold_fold_app _ μ

@[eval_simp] theorem D.invis_run (dl : Later D) (μ : GenMap (Later D)) :
    D.unfold (D.invis dl) μ ≡ Trace.invis (laterMap (D.runAt μ) dl) := D.unfold_fold_app _ μ

@[eval_simp] theorem D.bind_run (d : D) (k : Value D -n> D) (μ : GenMap (Later D)) :
    D.unfold (D.bind d k) μ ≡ Trace.bind (D.kCont k) (D.unfold d μ) := D.unfold_fold_app _ μ

@[eval_simp] theorem D.fn_run (f : D -n> D) (μ : GenMap (Later D)) :
    D.unfold (D.fn f) μ ≡ Trace.ret (Value.fn (Later.next f), μ) := D.ret_run _ μ

@[eval_simp] theorem D.con_run (K : Nat) (ds : List D) (μ : GenMap (Later D)) :
    D.unfold (D.con K ds) μ ≡ Trace.ret (Value.con K (ds.map Later.next), μ) := D.ret_run _ μ

/-- Bridge the `Domain D` instance fields to the by-need combinators, so the
    `eval_simp` set carries `eval`'s output into the `_run` rules. -/
@[eval_simp] theorem domain_step_D : (Domain.step : Event → D -n> D) = D.step := rfl
@[eval_simp] theorem domain_stuck_D : (Domain.stuck : D) = D.stuck := rfl
@[eval_simp] theorem domain_fn_D (x : Var) : (Domain.fn x : (D -n> D) -n> D) = D.fn := rfl
@[eval_simp] theorem domain_apply_D : (Domain.apply : D -n> D -n> D) = D.apply := rfl
@[eval_simp] theorem domain_con_D : (Domain.con : Nat → List D -n> D) = D.con := rfl
@[eval_simp] theorem domain_bind_D :
    (Domain.bind : (D -n> D) -n> (D -n> D) -n> D) = D.bindLet := rfl
@[eval_simp] theorem domain_select_D :
    (Domain.select : D -n> List (ConTag × Nat × (List D -n> D)) -n> D) = D.select := rfl

/-- Binding an immediately-returned constructor value runs the continuation on
    that value (the `Trace.bind`/`ret` left-unit, threaded through `D`). -/
theorem D.bind_con_run (K : Nat) (ds : List D) (k : Value D -n> D) (μ : GenMap (Later D)) :
    D.unfold (D.bind (D.con K ds) k) μ ≡ D.unfold (k (Value.con K (ds.map Later.next))) μ :=
  (D.bind_run _ k μ).trans
    ((ofe_mor_car_proper OFE.Equiv.rfl (D.con_run K ds μ)).trans
      (Trace.bind_ret (D.kCont k) (Value.con K (ds.map Later.next), μ)))

/-- `selectCont` on a constructor value with stored fields: force the fields
    and run the matching branch under `.invis`; a missing constructor is
    `stuck`. -/
theorem D.selectCont_stored (alts : List (ConTag × Nat × (List D -n> D))) (K : ConTag)
    (ds : List (Later D)) :
    D.selectCont alts (Value.con K ds)
      = (alts.find? (·.1 == K)).elim D.stuck
          (fun p => D.invis (Later.next (p.2.2 (ds.map (·.car))))) := rfl

/-- `selectCont` on a constructor value: the arguments thunked by `D.con` are
    forced straight back, so the matching branch runs on the original arguments;
    a missing constructor is `stuck`. -/
theorem D.selectCont_con (alts : List (ConTag × Nat × (List D -n> D))) (K : ConTag) (ds : List D) :
    D.selectCont alts (Value.con K (ds.map Later.next))
      = (alts.find? (·.1 == K)).elim D.stuck (fun p => D.invis (Later.next (p.2.2 ds))) := by
  rw [D.selectCont_stored]
  simp only [List.map_map, Function.comp_def, List.map_id']

/-- Dereferencing an unallocated cell is a stuck return. -/
theorem fetch_run_none {μ : GenMap (Later D)} {a : Addr} (h : μ.car a = none) :
    D.unfold (fetch a) μ ≡ Trace.ret (Value.stuck, μ) := by
  refine (D.unfold_fold_app _ μ).trans ?_
  show ((μ.car a).elim (Trace.fold (.ret (Value.stuck, μ)))
    (fun dl => Trace.fold (.invis (laterMap (D.runAt μ) dl))) : Trace (ValueHeapOF D D)) ≡ _
  rw [h]
  exact OFE.equiv_dist.mpr fun _ => OFE.dist_eqv.refl _

/-- Dereferencing an allocated cell: one silent step opening the stored `▶D`. -/
theorem fetch_run_some {μ : GenMap (Later D)} {a : Addr} {dl : Later D}
    (h : μ.car a = some dl) :
    D.unfold (fetch a) μ ≡ Trace.invis (laterMap (D.runAt μ) dl) := by
  refine (D.unfold_fold_app _ μ).trans ?_
  show ((μ.car a).elim (Trace.fold (.ret (Value.stuck, μ)))
    (fun dl => Trace.fold (.invis (laterMap (D.runAt μ) dl))) : Trace (ValueHeapOF D D)) ≡ _
  rw [h]
  exact OFE.equiv_dist.mpr fun _ => OFE.dist_eqv.refl _

/-- Running the update continuation on a `stuck` result: the heap is
    untouched. -/
theorem D.memoCont_run_stuck (a : Addr) (rec : Later D -n> Later D)
    (μ : GenMap (Later D)) :
    D.unfold (D.memo.cont a rec Value.stuck) μ ≡ Trace.ret (Value.stuck, μ) :=
  D.ret_run Value.stuck μ

/-- Running the update continuation on a value: emit `update`, then return the
    value with the memoized cell written. -/
theorem D.memoCont_run (a : Addr) (rec : Later D -n> Later D) {v : Value D}
    (hv : v.isStuck = false) (μ : GenMap (Later D)) :
    D.unfold (D.memo.cont a rec v) μ
      ≡ Trace.step .update
          (Later.next (Trace.ret (v, Heap.set μ a (rec (Later.next (D.ret v)))))) := by
  have h : D.memo.cont a rec v = D.memo.upd a rec v := by
    cases v with
    | stuck => exact Bool.noConfusion hv
    | fn g => rfl
    | con K ds => rfl
  rw [h]
  refine (D.step_run .update _ μ).trans ?_
  refine OFE.equiv_dist.mpr fun n => (Trace.step.ne .update).ne ?_
  intro m _
  exact OFE.equiv_dist.mp (D.unfold_fold_app _ μ) m

/-- `bindLet` against a heap: allocate the next free cell, memoize the rhs
    there, and run the body on the thunk dereferencing that cell. -/
theorem D.bindLet_run (rhs body : D -n> D) (μ : GenMap (Later D)) :
    D.unfold (D.bindLet rhs body) μ
      ≡ D.unfold (body (fetch (Heap.nextFree μ)))
          (Heap.set μ (Heap.nextFree μ)
            (D.memo (Heap.nextFree μ)
              (Later.next (rhs (fetch (Heap.nextFree μ)))))) :=
  D.unfold_fold_app _ μ

/-! ## The by-need evaluator and examples

The domain is computable (the solver, the trace/heap functors, and `nextFree`'s
least-free-key search all avoid `Classical`), so a denotation can be run against a
heap and observed as a trace. -/

@[eval_simp] def evalByNeed (e : Exp) : Env D -n> D := eval e

def idId : Exp := .lam "x" (.ref "x")
def idAppId : Exp := .«let» "i" (.lam "x" (.ref "x")) (.app (.ref "i") "i")
def idAppTrue : Exp := .«let» "t" (.conapp 1 []) (.app (.lam "x" (.ref "x")) "t")
def idAppIdMemo : Exp :=
  .«let» "i" (.app (.lam "y" (.lam "x" (.ref "x"))) "i") (.app (.ref "i") "i")
def caseTrue : Exp := .«case» (.conapp 1 []) [⟨1, [], .conapp 2 []⟩, ⟨0, [], .conapp 3 []⟩]
def caseStuck : Exp := .«case» (.conapp 5 []) [⟨1, [], .conapp 2 []⟩, ⟨0, [], .conapp 3 []⟩]

/-! ### Running closed programs to a trace

`render` unfolds a trace one layer at a time (fuel-bounded), naming each event and
the returned value; `runTrace` runs a closed program against the empty heap. The
`#guard`s pin the observable trace, so any drift fails the build. -/

/-- Empty environment and heap for running closed programs. -/
def ρ₀ : Env D := fun _ => none
def μ₀ : GenMap (Later D) := GenMap.empty

/-- Name a returned value by its constructor. -/
def descVal : Value D → String
  | .stuck    => "stuck"
  | .fn _     => "fn"
  | .con K ds => s!"con{K}[{ds.length}]"

/-- Name a trace event; `look` records the variable it dereferences. -/
def descEv : Event → String
  | .look x => s!"look({x})" | .update => "upd" | .app1 => "app1" | .app2 => "app2"
  | .case1 => "case1" | .case2 => "case2" | .let1 => "let1"

/-- Render a trace to a `;`-separated list of events ending in `ret(value)`. -/
def render : Nat → Trace (ValueHeapOF D D) → String
  | 0,      _ => "…"
  | fuel+1, t =>
    match Trace.unfold t with
    | .ret (v, _)    => s!"ret({descVal v})"
    | .step e tl     => descEv e ++ ";" ++ render fuel tl.car
    | .invis tl      => "invis;" ++ render fuel tl.car

/-- Render the observable trace: `.invis` layers are the `▷`-bookkeeping of the
    guarded metatheory, not events, and are erased. -/
def renderObs : Nat → Trace (ValueHeapOF D D) → String
  | 0,      _ => "…"
  | fuel+1, t =>
    match Trace.unfold t with
    | .ret (v, _)    => s!"ret({descVal v})"
    | .step e tl     => descEv e ++ ";" ++ renderObs fuel tl.car
    | .invis tl      => renderObs fuel tl.car

/-- Run a closed program against the empty heap and render its trace. -/
def runTrace (e : Exp) : String := render 100 (D.unfold (evalByNeed e ρ₀) μ₀)

/-- Run a closed program and render its observable trace (the paper's). -/
def runTraceObs (e : Exp) : String := renderObs 100 (D.unfold (evalByNeed e ρ₀) μ₀)

/-! The raw traces pin the `▷`-bookkeeping: exactly one `.invis` per
    `▷`-opening, adjacent to the visible step that explains it (`look;invis` at
    a dereference, `invis;app2` at a beta, `invis;case2` at a branch entry). -/

#guard runTrace idId == "ret(fn)"
#guard runTrace idAppId ==
  "let1;app1;look(i);invis;upd;invis;app2;look(i);invis;upd;ret(fn)"
#guard runTrace idAppTrue == "let1;app1;invis;app2;look(t);invis;upd;ret(con1[0])"
#guard runTrace idAppIdMemo ==
  "let1;app1;look(i);invis;app1;invis;app2;upd;invis;app2;look(i);invis;upd;ret(fn)"
#guard runTrace caseTrue == "case1;invis;case2;ret(con2[0])"
#guard runTrace caseStuck == "case1;ret(stuck)"

/-! The observable traces are exactly the paper's `evalNeed` traces. -/

#guard runTraceObs idId == "ret(fn)"
#guard runTraceObs idAppId == "let1;app1;look(i);upd;app2;look(i);upd;ret(fn)"
#guard runTraceObs idAppTrue == "let1;app1;app2;look(t);upd;ret(con1[0])"
#guard runTraceObs idAppIdMemo ==
  "let1;app1;look(i);app1;app2;upd;app2;look(i);upd;ret(fn)"
#guard runTraceObs caseTrue == "case1;case2;ret(con2[0])"
#guard runTraceObs caseStuck == "case1;ret(stuck)"

end AbsDen
