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
  have : P = Q := funext fun m => funext fun hm => h m hm
  subst this; rfl

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
    (h : ∀ m, m < n → X m = Y m) : Later X n = Later Y n := by
  cases n with | zero => rfl | succ n' => exact h n' (Nat.lt_succ_self n')

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

class WorldFunctor (F : (Nat → Type u) → (Nat → Type u)) where
  instWorld A [World A] : World (F A)

attribute [instance] WorldFunctor.instWorld

@[inline] def Later.sequence {A : Nat → Type u} [World A]
    (n : Nat) (list : List (Later A n)) : Later (World.Comp List A) n :=
  list.foldr (Later.ap _ ∘ Later.map (fun _ a => (a :: ·)) _) (Later.next [])

/-! ## LocalFunctor -/

class LocalFunctor (F : (Nat → Type u) → (Nat → Type u)) extends WorldFunctor F where
  property : ∀ (X Y : Nat → Type u) (n : Nat),
    (∀ m, m ≤ n → X m = Y m) → F X n = F Y n

namespace LocalFunctor

instance instConst [World P] : LocalFunctor (fun _ => P) where
  instWorld _ := inferInstance
  property _ _ _ _ := rfl

instance instId : LocalFunctor (fun X => X) where
  instWorld _ := inferInstance
  property _ _ n h := h n (Nat.le_refl n)

instance instLater : LocalFunctor Later where
  instWorld _ := inferInstance
  property X Y n h := by cases n with | zero => rfl | succ m => exact h m (Nat.le_succ m)

instance instProd [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Prod (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y n h := by simp only [World.Prod]; congr 1 <;> exact property X Y n h

instance instSum [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Sum (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y n h := by simp only [World.Sum]; congr 1 <;> exact property X Y n h

instance instComp [LocalFunctor F] [LocalFunctor G] :
    LocalFunctor (fun X => F (G X)) where
  instWorld A [World A] := inferInstance
  property X Y n h :=
    property (G X) (G Y) n fun m hm =>
      property X Y m fun k hk => h k (Nat.le_trans hk hm)

instance instWorldComp [Functor G] [LocalFunctor F] :
    LocalFunctor (fun X => World.Comp G (F X)) where
  instWorld A [World A] := inferInstance
  property X Y n h := by simp only [World.Comp]; congr 1; exact property X Y n h

instance instFunction [LocalFunctor F₁] [LocalFunctor F₂] :
    LocalFunctor (fun X => World.Function (F₁ X) (F₂ X)) where
  instWorld A [World A] := inferInstance
  property X Y n h := by
    simp only [World.Function]
    apply World.forall_le_congr
    intro m hm
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

private def Fix.chain (F : (Nat → Type u) → (Nat → Type u)) : Nat → (Nat → Type u)
  | 0 => F (World.Const PUnit)
  | n + 1 => F (Later (Fix.chain F n))

def Fix (F : (Nat → Type u) → (Nat → Type u)) : Nat → Type u :=
  fun n => Fix.chain F n n

private theorem Fix.chain_agree (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F]
    (n m : Nat) (h : m ≤ n) : Fix.chain F n m = Fix.chain F m m := by
  match n, m, h with
  | 0, 0, _ => rfl
  | n' + 1, 0, _ =>
    simp only [Fix.chain]
    exact LocalFunctor.property _ _ _ fun k hk => by cases Nat.le_zero.mp hk; simp [Later, World.Const]
  | n' + 1, m' + 1, h =>
    simp only [Fix.chain]
    exact LocalFunctor.property _ _ _ fun k hk =>
      Later.ext _ _ _ fun j hj =>
        have := Nat.le_of_succ_le_succ (Nat.lt_of_lt_of_le hj hk)
        (chain_agree F n' j (Nat.le_trans this (Nat.le_of_succ_le_succ h))).trans
          (chain_agree F m' j this).symm
termination_by (n, m)

private theorem Fix.chain_stable (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] (n : Nat) :
    Fix.chain F (n + 1) n = Fix.chain F n n :=
  Fix.chain_agree F (n + 1) n (Nat.le_succ n)

theorem Fix.eq (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] (n : Nat) :
    Fix F n = F (Later (Fix F)) n := by
  simp only [Fix]
  cases n with
  | zero =>
    exact LocalFunctor.property _ _ _ fun m hm => by
      cases Nat.le_zero.mp hm; simp [Later, World.Const]
  | succ n' =>
    exact LocalFunctor.property _ _ _ fun m hm =>
      Later.ext _ _ _ fun j hj =>
        Fix.chain_agree F n' j (Nat.le_of_succ_le_succ (Nat.lt_of_lt_of_le hj hm))

def Fix.fold {F : (Nat → Type u) → (Nat → Type u)} [LocalFunctor F] {n : Nat} :
    F (Later (Fix F)) n → Fix F n := cast (Fix.eq F n).symm

def Fix.unfold {F : (Nat → Type u) → (Nat → Type u)} [LocalFunctor F] {n : Nat} :
    Fix F n → F (Later (Fix F)) n := cast (Fix.eq F n)

private def Fix.chain_world (F : (Nat → Type u) → (Nat → Type u))
    (inst : ∀ (X : Nat → Type u), [World X] → World (F X)) :
    (k : Nat) → World (Fix.chain F k)
  | 0 => inst _
  | k + 1 =>
    letI := Fix.chain_world F inst k
    inst _

instance Fix.instWorld (F : (Nat → Type u) → (Nat → Type u)) [LocalFunctor F] : World (Fix F) where
  restrictStep {n} x :=
    letI := Fix.chain_world F WorldFunctor.instWorld (n + 1)
    cast (Fix.chain_stable F n) (World.restrictStep x)

end World

def loeb {A : Nat → Type u} [World A] {n : Nat} (f : World.Function (Later A) A n) : A n :=
  match n with
  | 0 => f 0 (by omega) PUnit.unit
  | n + 1 => f (n + 1) (by omega) (loeb (n:=n) (World.restrict f))

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

/-! ## Tests -/

section Tests

example : World.Const Nat 5 = Nat := rfl
example : Later (World.Const Nat) 0 = PUnit := rfl
example : Later (World.Const Nat) 3 = Nat := rfl
example : World.Prod (World.Const Nat) (World.Const Bool) 0 = (Nat × Bool) := rfl
example : World.Sum (World.Const Nat) (World.Const Bool) 0 = (Nat ⊕ Bool) := rfl

end Tests
