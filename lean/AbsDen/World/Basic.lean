import Lean

/-!
# World — Step-indexed families with restriction

A `World` is a typeclass on families `Nat → Type u` providing restriction maps.
-/

universe u v

/-! ## World typeclass -/

class World (F : Nat → Type u) where
  restrictStep : {n : Nat} → F (n + 1) → F n

namespace World

def restrict {F : Nat → Type u} [World F] {n m : Nat} (x : F n) (hm : m ≤ n := by grind) : F m :=
  if h : m = n then cast (by rw [h]) x
  else match n with
    | 0 => absurd (Nat.lt_of_le_of_ne hm h) (Nat.not_lt_zero m)
    | n' + 1 => restrict (restrictStep x) (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hm h))
  termination_by n

theorem forall_le_congr {n : Nat} {P Q : (m : Nat) → m ≤ n → Type v}
    (h : ∀ m hm, P m hm = Q m hm) :
    (∀ m (hm : m ≤ n), P m hm) = (∀ m (hm : m ≤ n), Q m hm) := by
  have : P = Q := funext fun m => funext fun hm => h m hm; subst this; rfl

/-- Helper: cast through `forall_le_congr` decomposes at each level. -/
theorem cast_forall_le_congr_apply {n : Nat} {P Q : (m : Nat) → m ≤ n → Type v}
    (h : ∀ m hm, P m hm = Q m hm)
    (f : ∀ m (hm : m ≤ n), P m hm) (m : Nat) (hm : m ≤ n) :
    cast (forall_le_congr h) f m hm = cast (h m hm) (f m hm) := by
  have : P = Q := funext fun m => funext fun hm => h m hm; subst this; rfl

end World

/-! ## Combinators -/

def Later (A : Nat → Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => A n

def Later.next {F : Nat → Type u} [World F] {n : Nat} : F n → Later F n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | _ + 1 => World.restrictStep

def Later.next' {F : Nat → Type u} {n : Nat} : F (n - 1) → Later F n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | _ + 1 => id

@[inline] def Later.hmap {A B : Nat → Type u} (n : Nat)
    (f : (m : Nat) → (h : m < n) → A m → B m) : Later A n → Later B n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | m + 1 => fun a => f m (by omega) a

@[inline] def Later.map {A B : Nat → Type u} (f : (m : Nat) → A m → B m)
    (n : Nat) : Later A n → Later B n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | m + 1 => fun a => f m a

@[inline] def Later.ap {A B : Nat → Type u}
    (n : Nat) : Later (fun m => A m → B m) n → Later A n → Later B n :=
  match n with
  | 0 => fun _ _ => PUnit.unit
  | _ + 1 => fun f a => f a

theorem Later.ext (X Y : Nat → Type u) (n : Nat)
    (h : ∀ m, m < n → X m = Y m) : Later X n = Later Y n :=
  match n with | 0 => rfl | n' + 1 => h n' (Nat.lt_succ_self n')

instance {A : Nat → Type u} {n : Nat} [h : ∀ m, Inhabited (A m)] : Inhabited (Later A n) :=
  match n with
  | 0 => ⟨PUnit.unit⟩
  | m + 1 => h m

instance [World F] : World (Later F) where restrictStep := Later.next (F := F)

def World.Const (S : Type u) : Nat → Type u := fun _ => S
instance : World (World.Const S) where restrictStep := id

def World.Prod (A B : Nat → Type u) : Nat → Type u := fun n => A n × B n
instance [World A] [World B] : World (World.Prod A B) where
  restrictStep | (a, b) => (World.restrictStep a, World.restrictStep b)

def World.Sum (A B : Nat → Type u) : Nat → Type u := fun n => A n ⊕ B n
instance [World A] [World B] : World (World.Sum A B) where
  restrictStep | .inl a => .inl (World.restrictStep a) | .inr b => .inr (World.restrictStep b)

def World.Function (A B : Nat → Type u) : Nat → Type u :=
  fun n => ∀ m, m ≤ n → A m → B m
instance : World (World.Function A B) where
  restrictStep f m hm := f m (Nat.le_trans hm (Nat.le_succ _))

def World.Comp (G : Type u → Type v) [Functor G] (A : Nat → Type u) : Nat → Type v :=
  fun n => G (A n)
instance [Functor G] [World A] : World (World.Comp G A) where
  restrictStep := Functor.map World.restrictStep

/-! ## Subobject classifier and sub-presheaves -/

/-- The subobject classifier of the topos of trees: step-indexed truth values.
    `IProp n` is the type of sieves on `n`, represented as downward-closed
    `Nat → Prop` predicates clipped to `{0, …, n}`. The clipping enforces
    extensionality: two values of `IProp n` are equal iff their underlying
    predicates are pointwise iff. -/
def World.IProp (n : Nat) : Type :=
  { P : Nat → Prop // (∀ m, P (m+1) → P m) ∧ (∀ m, P m → m ≤ n) }

namespace World.IProp

/-- Pointwise iff implies equality. -/
theorem ext {n : Nat} {p q : IProp n} (h : ∀ m, p.val m ↔ q.val m) : p = q :=
  Subtype.ext (funext fun m => propext (h m))

/-- The least truth value: never true. -/
def False {n : Nat} : IProp n :=
  ⟨fun _ => _root_.False, fun _ h => h, fun _ h => h.elim⟩

/-- The greatest truth value at level `n`: true throughout `{0, …, n}`. -/
def True {n : Nat} : IProp n :=
  ⟨fun m => m ≤ n, fun _ h => Nat.le_of_succ_le h, fun _ h => h⟩

/-- Graded truth value: true on `{0, …, k}`. -/
def upTo {n : Nat} (k : Nat) (hk : k ≤ n) : IProp n :=
  ⟨fun m => m ≤ k, fun _ h => Nat.le_of_succ_le h, fun _ hm => Nat.le_trans hm hk⟩

/-- Embedding of Lean's `Prop` as a level-uniform truth value. -/
def OfProp {n : Nat} (p : Prop) : IProp n :=
  ⟨fun m => p ∧ m ≤ n,
   fun _ ⟨hp, hm⟩ => ⟨hp, Nat.le_of_succ_le hm⟩,
   fun _ ⟨_, hm⟩ => hm⟩

/-- Binary meet (intersection of sieves). -/
def And {n : Nat} (p q : IProp n) : IProp n :=
  ⟨fun m => p.val m ∧ q.val m,
   fun _ ⟨hp, hq⟩ => ⟨p.property.1 _ hp, q.property.1 _ hq⟩,
   fun _ ⟨hp, _⟩ => p.property.2 _ hp⟩

end World.IProp

instance : World World.IProp where
  restrictStep := fun {n} ⟨P, hclose, _⟩ =>
    ⟨fun m => P m ∧ m ≤ n,
     fun m ⟨hPm1, hm1⟩ => ⟨hclose m hPm1, Nat.le_of_succ_le hm1⟩,
     fun _ ⟨_, hm⟩ => hm⟩

@[simp]
theorem World.IProp.restrictStep_val {n : Nat} (p : World.IProp (n+1)) (m : Nat) :
    (World.restrictStep p).val m = (p.val m ∧ m ≤ n) := by
  obtain ⟨P, hc, hb⟩ := p; rfl

@[simp]
theorem World.restrict_self {F : Nat → Type u} [World F] {n : Nat} (x : F n) :
    World.restrict x (Nat.le_refl n) = x := by
  rw [World.restrict.eq_1, dif_pos rfl]; simp [cast_eq]

/-- One step of restriction descends one level along multi-step restriction. -/
theorem World.restrict_succ {F : Nat → Type u} [World F]
    {n m : Nat} (x : F (n+1)) (h : m ≤ n) :
    World.restrict x (Nat.le_succ_of_le h) = World.restrict (World.restrictStep x) h := by
  show World.restrict x (Nat.le_succ_of_le h) = _
  rw [World.restrict.eq_1, dif_neg (by omega : ¬ m = n+1)]

/-- A single `restrictStep` factors out of multi-step restriction. -/
theorem World.restrictStep_restrict {F : Nat → Type u} [World F]
    {n m : Nat} (x : F n) (h : m+1 ≤ n) :
    World.restrictStep (World.restrict x h) = World.restrict x (Nat.le_of_succ_le h) := by
  induction n with
  | zero => omega
  | succ n' ih =>
    by_cases hmn : m = n'
    · subst hmn
      have lhs : World.restrict x h = x := by
        rw [World.restrict.eq_1, dif_pos rfl]; simp [cast_eq]
      rw [lhs, World.restrict_succ x (Nat.le_refl m), World.restrict_self]
    · have h' : m+1 ≤ n' := by omega
      have lhs : World.restrict x h = World.restrict (World.restrictStep x) h' := by
        show World.restrict x h = _
        rw [World.restrict.eq_1, dif_neg (by omega : ¬ m+1 = n'+1)]
      rw [lhs, ih (World.restrictStep x) h']
      exact (World.restrict_succ x (Nat.le_of_succ_le h')).symm

/-- A sub-presheaf of `F`: a natural transformation `F → World.IProp`, given as
    the proper subtype of `∀ {n}, F n → World.IProp n` cut out by naturality
    against `restrictStep`. -/
def World.Pred (F : Nat → Type u) [World F] : Type u :=
  { P : ∀ {n}, F n → World.IProp n //
      ∀ {n} (x : F (n+1)), P (World.restrictStep x) = World.restrictStep (P x) }

namespace World.Pred
variable {F : Nat → Type u} [World F]

/-- Membership of `x : F n` in the sub-presheaf, given by the top-level truth
    value of its characteristic morphism. -/
def holds (p : World.Pred F) {n : Nat} (x : F n) : Prop :=
  (p.val x).val n

/-- Single-step closure: a derived consequence of naturality plus `IProp`'s
    downward closure. -/
theorem closed (p : World.Pred F) {n : Nat} (x : F (n+1))
    (hx : p.holds x) : p.holds (World.restrictStep x) := by
  show (p.val (World.restrictStep x)).val n
  rw [p.property x, World.IProp.restrictStep_val]
  exact ⟨(p.val x).property.1 n hx, Nat.le_refl _⟩

/-- Smart constructor from a predicate with single-step closure. The
    characteristic morphism at `x : F n` is the sieve of levels `m ≤ n` at
    which `World.restrict x` lies in the sub-presheaf. -/
def ofClosed
    (holds : ∀ {n}, F n → Prop)
    (closed : ∀ {n} (x : F (n+1)), holds x → holds (World.restrictStep x)) :
    World.Pred F :=
  ⟨fun {n} x =>
    ⟨fun m => ∃ (h : m ≤ n), holds (World.restrict x h),
     ⟨fun m ⟨h_succ, hP⟩ =>
        ⟨Nat.le_of_succ_le h_succ,
         by have := closed _ hP
            rwa [World.restrictStep_restrict] at this⟩,
      fun _ ⟨h, _⟩ => h⟩⟩,
   fun {n} x => by
    apply World.IProp.ext
    intro m
    constructor
    · rintro ⟨h_le_n, hP⟩
      refine ⟨⟨Nat.le_succ_of_le h_le_n, ?_⟩, h_le_n⟩
      rwa [World.restrict_succ]
    · rintro ⟨⟨_, hP⟩, h_le_n⟩
      refine ⟨h_le_n, ?_⟩
      rwa [← World.restrict_succ]⟩

end World.Pred

/-- A `World.Pred F` is callable as its membership predicate. -/
instance {F : Nat → Type u} [World F] :
    CoeFun (World.Pred F) (fun _ => ∀ {n : Nat}, F n → Prop) where
  coe p := fun {_} x => p.holds x

/-- The carrier sub-presheaf at level `n`. -/
def World.Pred.carrier {F : Nat → Type u} [World F] (p : World.Pred F) (n : Nat) :
    Type u := { x : F n // p.holds x }

instance {F : Nat → Type u} [World F] (p : World.Pred F) : World p.carrier where
  restrictStep := fun ⟨x, hx⟩ => ⟨World.restrictStep x, p.closed x hx⟩

@[simp]
theorem World.Pred.ofClosed_holds {F : Nat → Type u} [World F]
    (h : ∀ {m}, F m → Prop)
    (c : ∀ {m} (x : F (m+1)), h x → h (World.restrictStep x))
    {n : Nat} (x : F n) :
    (World.Pred.ofClosed (F := F) h c).holds x ↔ h x := by
  constructor
  · rintro ⟨_, hP⟩
    rwa [World.restrict_self] at hP
  · intro hh
    exact ⟨Nat.le_refl _, by rwa [World.restrict_self]⟩

@[simp]
theorem World.IProp.restrictStep_and {n : Nat} (a b : World.IProp (n+1)) :
    World.restrictStep (a.And b) = (World.restrictStep a).And (World.restrictStep b) := by
  apply World.IProp.ext; intro m
  rw [World.IProp.restrictStep_val]
  show ((a.val m ∧ b.val m) ∧ m ≤ n) ↔ ((restrictStep a).val m ∧ (restrictStep b).val m)
  rw [World.IProp.restrictStep_val, World.IProp.restrictStep_val]
  exact ⟨fun ⟨⟨ha, hb⟩, hm⟩ => ⟨⟨ha, hm⟩, hb, hm⟩,
         fun ⟨⟨ha, hm⟩, hb, _⟩ => ⟨⟨ha, hb⟩, hm⟩⟩

namespace World.Pred
variable {F : Nat → Type u} [World F]

/-- Binary meet of sub-presheaves: pointwise intersection of sieves. -/
def And (p q : World.Pred F) : World.Pred F :=
  ⟨fun {n} x => (p.val x).And (q.val x),
   fun {n} x => by
     show (p.val (World.restrictStep x)).And (q.val (World.restrictStep x)) =
          World.restrictStep ((p.val x).And (q.val x))
     rw [p.property x, q.property x, World.IProp.restrictStep_and]⟩

@[simp]
theorem And_holds (p q : World.Pred F) {n : Nat} (x : F n) :
    (p.And q).holds x ↔ p.holds x ∧ q.holds x := Iff.rfl

end World.Pred

/-- Underlying predicate of `laterLift`. -/
def World.Pred.laterLift_holds {F : Nat → Type u} [World F] (p : World.Pred F) :
    ∀ {n : Nat}, Later F n → Prop
  | 0, _ => True
  | _+1, d => p.holds d

private theorem World.Pred.laterLift_closed {F : Nat → Type u} [World F] (p : World.Pred F)
    {n : Nat} (x : Later F (n+1)) (hx : p.laterLift_holds x) :
    p.laterLift_holds (World.restrictStep x) := by
  cases n with
  | zero => trivial
  | succ k => exact p.closed x hx

/-- The `▹` modal lift: any sub-presheaf of `F` induces one of `Later F`. -/
def World.Pred.laterLift {F : Nat → Type u} [World F] (p : World.Pred F) :
    World.Pred (Later F) :=
  World.Pred.ofClosed p.laterLift_holds p.laterLift_closed

@[simp]
theorem World.Pred.laterLift_holds_succ {F : Nat → Type u} [World F] (p : World.Pred F)
    {n : Nat} (x : F n) :
    p.laterLift.holds (n := n+1) x ↔ p.holds x := by
  unfold World.Pred.laterLift
  rw [World.Pred.ofClosed_holds]
  rfl

class WorldFunctor (F : (Nat → Type u) → (Nat → Type u)) where
  instWorld A [World A] : World (F A)

attribute [instance] WorldFunctor.instWorld

@[inline] def Later.sequence {A : Nat → Type u} [World A]
    (n : Nat) (list : List (Later A n)) : Later (World.Comp List A) n :=
  list.foldr (Later.ap _ ∘ Later.map (fun _ a => (a :: ·)) _) (Later.next [])

/-! ## LocalFunctor -/

class LocalFunctor (F : (Nat → Type u) → (Nat → Type u)) extends WorldFunctor F where
  property : ∀ (X Y : Nat → Type u) [World X] [World Y] (n : Nat),
    (∀ m, m ≤ n → X m = Y m) → F X n = F Y n

namespace LocalFunctor

instance instConst [World P] : LocalFunctor (fun _ => P) where
  instWorld _ := inferInstance
  property _ _ _ _ _ _ := rfl

instance instId : LocalFunctor (fun X => X) where
  instWorld _ := inferInstance
  property _ _ _ _ n h := h n (Nat.le_refl n)

instance instLater : LocalFunctor Later where
  instWorld _ := inferInstance
  property _ _ _ _ n h := match n with | 0 => rfl | m + 1 => h m (Nat.le_succ m)

instance instProd [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Prod (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y _ _ n h := by simp only [World.Prod]; congr 1 <;> exact property X Y n h

instance instSum [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Sum (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y _ _ n h := by simp only [World.Sum]; congr 1 <;> exact property X Y n h

instance instComp [LocalFunctor F] [LocalFunctor G] :
    LocalFunctor (fun X => F (G X)) where
  instWorld A [World A] := inferInstance
  property X Y _ _ n h :=
    property (G X) (G Y) n fun m hm =>
      property X Y m fun k hk => h k (Nat.le_trans hk hm)

instance instWorldComp [Functor G] [LocalFunctor F] :
    LocalFunctor (fun X => World.Comp G (F X)) where
  instWorld A [World A] := inferInstance
  property X Y _ _ n h := congrArg _ (property X Y n h)

instance instFunction [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Function (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y _ _ n h := by
    simp only [World.Function]; apply World.forall_le_congr; intro m hm
    rw [property (F := F₁) X Y m (fun k hk => h k (Nat.le_trans hk hm)),
        property (F := F₂) X Y m (fun k hk => h k (Nat.le_trans hk hm))]

end LocalFunctor

/-! ## derive_local_functor tactic -/

open Lean Meta Elab Tactic in
/-- Recursively build a `LocalFunctor (fun X => body)` proof. For leaf cases uses
    synthInstance; for compound cases constructs proof terms explicitly. -/
private partial def solveLocalFunctor (xVar : Expr) (body : Expr) : MetaM Expr := do
  let xId := xVar.fvarId!
  -- Unfold only abbrevs (not World combinators which are defs)
  let body ← withReducible (whnf body)
  let lam ← mkLambdaFVars #[xVar] body
  let goalType ← mkAppM ``LocalFunctor #[lam]
  -- Leaf cases: synthInstance handles these because the lambda patterns match directly
  if !body.containsFVar xId then
    -- fun _ => P  matches instConst
    synthInstance goalType
  else if body.isFVar && body.fvarId! == xId then
    -- fun X => X  matches instId
    synthInstance goalType
  else
    let fn := body.getAppFn
    let args := body.getAppArgs
    -- Binary combinators: Sum, Prod, Function
    -- Build explicit proof: @instXxx F₁ F₂ proofA proofB
    if (fn.isConstOf ``World.Sum || fn.isConstOf ``World.Prod || fn.isConstOf ``World.Function)
       && args.size == 2 then
      let proofA ← solveLocalFunctor xVar args[0]!
      let proofB ← solveLocalFunctor xVar args[1]!
      let lamA ← mkLambdaFVars #[xVar] args[0]!
      let lamB ← mkLambdaFVars #[xVar] args[1]!
      let instName := if fn.isConstOf ``World.Sum then ``LocalFunctor.instSum
        else if fn.isConstOf ``World.Prod then ``LocalFunctor.instProd
        else ``LocalFunctor.instFunction
      -- Telescope: {F₁} {F₂} [LF F₁] [LF F₂]
      mkAppOptM instName #[some lamA, some lamB, some proofA, some proofB]
    -- Later a
    else if fn.isConstOf ``Later && args.size == 1 then
      let a := args[0]!
      if !a.containsFVar xId then
        -- fun X => Later P  where P doesn't depend on X
        synthInstance goalType
      else
        -- fun X => Later (G X)  →  instComp Later G
        let proofG ← solveLocalFunctor xVar a
        let lamG ← mkLambdaFVars #[xVar] a
        -- Telescope for instComp: {F} {G} [LF F] [LF G]
        let laterLF ← synthInstance (← mkAppM ``LocalFunctor #[mkConst ``Later])
        mkAppOptM ``LocalFunctor.instComp #[none, some lamG, some laterLF, some proofG]
    -- World.Comp G _ a  (3 args: G, Functor inst, a)
    else if fn.isConstOf ``World.Comp && args.size == 3 then
      let g := args[0]!         -- The type functor (e.g. List)
      let functorInst := args[1]!  -- The Functor instance
      let a := args[2]!         -- The inner expression
      if !a.containsFVar xId then
        synthInstance goalType
      else
        let proofA ← solveLocalFunctor xVar a
        let lamA ← mkLambdaFVars #[xVar] a
        -- Telescope for instWorldComp: {G} {F} [Functor G] [LF F]
        mkAppOptM ``LocalFunctor.instWorldComp #[some g, some lamA, some functorInst, some proofA]
    -- F a₁ ... aₖ X where last arg is X (the bound variable)
    -- F may be a known functor (inductive with derived LocalFunctor)
    -- Each aᵢ may or may not depend on X
    else if body.isApp && body.appArg!.isFVar && body.appArg!.fvarId! == xId then
      let fn := body.appFn!
      if !fn.containsFVar xId then
        -- Simple case: F X where F doesn't mention X → synthInstance
        synthInstance goalType
      else
        -- Complex case: F depends on X. Decompose F into head + args.
        -- Rebuild with each X-dependent arg replaced by its lambda abstraction.
        -- Then try to synthesize LocalFunctor for the partially-applied F.
        let headFn := fn.getAppFn
        let fnArgs := fn.getAppArgs
        -- For each arg: if it depends on X, recurse and get LocalFunctor proof;
        -- abstract over X. If not, keep as-is.
        let mut newArgs : Array Expr := #[]
        let mut subProofs : Array (Option Expr) := #[]
        for arg in fnArgs do
          if arg.containsFVar xId then
            let proof ← solveLocalFunctor xVar arg
            let lamArg ← mkLambdaFVars #[xVar] arg
            newArgs := newArgs.push lamArg
            subProofs := subProofs.push (some proof)
          else
            newArgs := newArgs.push arg
            subProofs := subProofs.push none
        -- Rebuild the functor: headFn applied to newArgs
        -- This gives a functor (Nat → Type) → (Nat → Type)
        let partialFn := mkAppN headFn newArgs
        -- Try to synthesize LocalFunctor for this functor
        -- The sub-proofs for X-dependent args should be in the local instance cache
        let mut instGoal ← mkAppM ``LocalFunctor #[partialFn]
        -- Add sub-proofs as local instances
        let mut proof ← withLocalDeclsD (subProofs.filterMap id |>.mapIdx fun i p =>
          (s!"_inst{i}".toName, fun _ => inferType p)) fun _instFVars => do
          synthInstance instGoal
        -- Substitute actual proofs for the instance fvars
        -- (This is a simplification; proper implementation would use withLocalDecl)
        return proof
    -- F (G X) where F doesn't depend on X and G X does → instComp F G
    else if body.isApp then
      let fn := body.appFn!
      let arg := body.appArg!
      if !fn.containsFVar xId && arg.containsFVar xId then
        let proofF ← synthInstance (← mkAppM ``LocalFunctor #[fn])
        let proofG ← solveLocalFunctor xVar arg
        let lamG ← mkLambdaFVars #[xVar] arg
        mkAppOptM ``LocalFunctor.instComp #[some fn, some lamG, some proofF, some proofG]
      else
        throwError "derive_local_functor: unsupported body shape: {body}"
    else
      throwError "derive_local_functor: unsupported body shape: {body}"

syntax "derive_local_functor" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| derive_local_functor) => do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let goalType ← whnf goalType
    let .app (.const ``LocalFunctor _) funExpr := goalType
      | throwError "derive_local_functor: goal is not `LocalFunctor F`, got: {goalType}"
    let funExpr ← whnf funExpr
    let .lam xName xType body bi := funExpr
      | throwError "derive_local_functor: expected lambda, got: {funExpr}"
    withLocalDecl xName bi xType fun xVar => do
      let body := body.instantiate1 xVar
      let proof ← solveLocalFunctor xVar body
      goal.assign proof

/-! ## Guarded fixpoint -/

namespace World

def Fix.chain (F : (Nat → Type u) → (Nat → Type u)) : Nat → (Nat → Type u)
  | 0 => F (World.Const PUnit)
  | n + 1 => F (Later (Fix.chain F n))

def Fix.chain_world (F : (Nat → Type u) → (Nat → Type u))
    (inst : ∀ (X : Nat → Type u), [World X] → World (F X)) :
    (k : Nat) → World (Fix.chain F k)
  | 0 => inst _
  | k + 1 =>
    letI := Fix.chain_world F inst k
    inst _

theorem Fix.chain_agree (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F]
    (n m : Nat) (h : m ≤ n) : Fix.chain F n m = Fix.chain F m m := by
  match n, m, h with
  | 0, 0, _ => rfl
  | n' + 1, 0, _ =>
    letI := Fix.chain_world F WorldFunctor.instWorld n'
    exact LocalFunctor.property _ _ _ fun k hk => by
      cases Nat.le_zero.mp hk; simp [Later, World.Const]
  | n' + 1, m' + 1, h =>
    letI := Fix.chain_world F WorldFunctor.instWorld n'
    letI := Fix.chain_world F WorldFunctor.instWorld m'
    exact LocalFunctor.property _ _ _ fun k hk =>
      Later.ext _ _ _ fun j hj =>
        have := Nat.le_of_succ_le_succ (Nat.lt_of_lt_of_le hj hk)
        (chain_agree F n' j (Nat.le_trans this (Nat.le_of_succ_le_succ h))).trans
          (chain_agree F m' j this).symm
termination_by (n, m)

theorem Fix.chain_stable (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] (n : Nat) :
    Fix.chain F (n + 1) n = Fix.chain F n n :=
  Fix.chain_agree F (n + 1) n (Nat.le_succ n)

def Fix (F : (Nat → Type u) → (Nat → Type u)) : Nat → Type u :=
  fun n => Fix.chain F n n

instance Fix.instWorld (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] : World (Fix F) where
  restrictStep {n} x :=
    letI := Fix.chain_world F WorldFunctor.instWorld (n + 1)
    cast (Fix.chain_stable F n) (World.restrictStep x)

theorem Fix.eq (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] (n : Nat) :
    Fix F n = F (Later (Fix F)) n := by
  simp only [Fix]
  cases n with
  | zero =>
    exact LocalFunctor.property _ _ 0 fun m hm => by
      cases Nat.le_zero.mp hm; simp [Later, World.Const]
  | succ n' =>
    letI := Fix.chain_world F WorldFunctor.instWorld n'
    exact LocalFunctor.property _ _ _ fun m hm =>
      Later.ext _ _ _ fun j hj =>
        Fix.chain_agree F n' j (Nat.le_of_succ_le_succ (Nat.lt_of_lt_of_le hj hm))

def Fix.fold {F : (Nat → Type u) → (Nat → Type u)} [LocalFunctor F] {n : Nat} :
    F (Later (Fix F)) n → Fix F n := cast (Fix.eq F n).symm

def Fix.unfold {F : (Nat → Type u) → (Nat → Type u)} [LocalFunctor F] {n : Nat} :
    Fix F n → F (Later (Fix F)) n := cast (Fix.eq F n)

/-- Bi-parameter chain agreement: if `F` is a `LocalFunctor` in both of its family
    arguments, then `Fix.chain (F X) k` and `Fix.chain (F Y) k` agree at any
    index `m` with `m ≤ n` and `m ≤ k`, provided `X` and `Y` agree at indices `≤ n`. -/
theorem Fix.chain_agree_param
    (F : (Nat → Type u) → (Nat → Type u) → (Nat → Type u))
    (inst₁ : ∀ X [World X], LocalFunctor (fun Y => F X Y))
    (inst₂ : ∀ Y [World Y], LocalFunctor (fun X => F X Y))
    {X Y : Nat → Type u} [World X] [World Y] (n : Nat) (h : ∀ m, m ≤ n → X m = Y m)
    (k m : Nat) (hm : m ≤ n) (hmk : m ≤ k) :
    Fix.chain (F X) k m = Fix.chain (F Y) k m := by
  induction k generalizing m with
  | zero =>
    exact (inst₂ (World.Const PUnit)).property X Y m fun j hj => h j (Nat.le_trans hj hm)
  | succ k' ih =>
    letI := Fix.chain_world (F X) WorldFunctor.instWorld k'
    letI := Fix.chain_world (F Y) WorldFunctor.instWorld k'
    exact ((inst₂ _).property X Y m fun j hj => h j (Nat.le_trans hj hm)).trans
      ((inst₁ Y).property _ _ m fun j hj =>
        Later.ext _ _ _ fun i hi =>
          ih i (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi hj) hm))
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi hj) hmk)))

instance Fix.instLocalFunctor (F : (Nat → Type u) → (Nat → Type u) → (Nat → Type u))
    (inst₁ : ∀ X [World X], LocalFunctor (fun Y => F X Y))
    (inst₂ : ∀ Y [World Y], LocalFunctor (fun X => F X Y)) :
    LocalFunctor (fun X => Fix (F X)) where
  instWorld X [World X] := inferInstance
  property _ _ _ _ n h :=
    Fix.chain_agree_param F inst₁ inst₂ n h n n (Nat.le_refl n) (Nat.le_refl n)

/-- For `World.Function`-based Fix types, `unfold` after `restrictStep` equals
    `unfold` with a weakened inequality proof. -/
theorem Fix.unfold_restrictStep_Function
    {A B : (Nat → Type u) → (Nat → Type u)} [LocalFunctor A] [LocalFunctor B]
    {n : Nat} (x : Fix (fun X => Function (A X) (B X)) (n + 1))
    (m : Nat) (hm : m ≤ n) :
    Fix.unfold (restrictStep x) m hm =
    Fix.unfold x m (Nat.le_succ_of_le hm) := by
  letI := Fix.chain_world (fun X => Function (A X) (B X)) WorldFunctor.instWorld n
  simp [World.Fix.unfold, World.restrictStep]
  rw [cast_forall_le_congr_apply, cast_forall_le_congr_apply]
  · rfl
  · intro k hk; congr 1 <;> exact LocalFunctor.property _ _ k
      (fun j hj => Later.ext _ _ j (fun i hi => Fix.chain_agree _ n i (by omega)))
  · intro k hk; congr 1 <;> exact LocalFunctor.property _ _ k
      (fun j hj => Later.ext _ _ j (fun i hi => Fix.chain_agree _ n i (by omega)))

end World

def loeb {A : Nat → Type u} [World A] {n : Nat} (f : World.Function (Later A) A n) : A n :=
  match n with
  | 0 => f 0 (by omega) PUnit.unit
  | n + 1 => f (n + 1) (by omega) (loeb (n:=n) (World.restrict f))

/-
theorem restrictStep_loeb_eq_loeb_restrictStep {A : Nat → Type u} [World A] {n : Nat} {f : World.Function (Later A) A (n + 1)} :
    World.restrictStep (loeb f) = loeb (World.restrictStep f) := by
  -- Likely needs naturality as a law of [World A]
  sorry

theorem next_loeb_eq_loeb_restrict {A : Nat → Type u} [World A] {n : Nat} {f : World.Function (Later A) A (n + 1)} :
    Later.next (loeb f) = loeb (n:=n) (World.restrict f) := by
  simp only [Later.next, World.restrict, Nat.left_eq_add, Nat.succ_ne_self, ↓reduceDIte, cast_eq]
  apply restrictStep_loeb_eq_loeb_restrictStep

theorem loeb.eq {A : Nat → Type u} [World A] {n : Nat} {f : World.Function (Later A) A n} :
    loeb f = f n (Nat.le_refl _) (Later.next (loeb f)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw[loeb]
    rw [next_loeb_eq_loeb_restrict]
-/

/-! ## Tests -/

section Tests

example : World.Const Nat 5 = Nat := rfl
example : Later (World.Const Nat) 0 = PUnit := rfl
example : Later (World.Const Nat) 3 = Nat := rfl
example : World.Prod (World.Const Nat) (World.Const Bool) 0 = (Nat × Bool) := rfl
example : World.Sum (World.Const Nat) (World.Const Bool) 0 = (Nat ⊕ Bool) := rfl

end Tests
