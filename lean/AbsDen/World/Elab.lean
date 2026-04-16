import AbsDen.World.Basic
import AbsDen.Env
import Lean.Elab.Term

/-!
# world(...) syntax for World family expressions

Syntax sugar for constructing step-indexed type families (`Nat → Type u`):
- `world(A ⊕ B)`      = `World.Sum world(A) world(B)`
- `world(A × B)`      = `World.Prod world(A) world(B)`
- `world(A → B)`      = `World.Function world(A) world(B)`
- `world(▹ A)`        = `Later world(A)`
- `world(γ X, body)`  = `World.Fix (fun X => world(body))`
- `world(F A)`        = `World.Comp F world(A)` when F : Type → Type
- `world(T)`          = `T` if T : Nat → Type u, else `World.Const T`
-/

/-- `▹` prefix operator for Later modality. -/
syntax:max "▹" term:max : term
macro_rules | `(▹ $a) => `(Later $a)

/-- Guarded fixpoint: `γ X, body` inside world(...). -/
syntax:max "γ" ident ", " term : term

syntax:max (name := worldSyntax) "world(" term ")" : term

open Lean Elab Term Meta in
/-- Check if an expression is a World family (has type `Nat → Type u` or similar). -/
private def isWorldFamily (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  let ty ← whnf ty
  -- Check if ty is a function type `Nat → Sort u`
  if ty.isForall then
    let .forallE _ dom _ _ := ty | return false
    return (← whnf dom).isConstOf ``Nat
  return false

open Lean Elab Term Meta in
/-- Unify the types of two world family expressions. -/
private def unifyWorldTypes (a b : Expr) : TermElabM Expr := do
  let tyA ← inferType a
  let tyB ← inferType b
  unless ← isDefEq tyA tyB do
    throwError "world: cannot unify world types {tyA} and {tyB}"
  return tyA

open Lean Elab Term Meta in
/-- Collect application spine, stopping at world-specific syntax. -/
private partial def collectAppSpine (t : Syntax) : Syntax × Array Syntax :=
  match t with
  | `(_ → _) | `(_ × _) | `(_ ⊕ _) | `(▹ $_) | `(γ $_, $_) => (t, #[])
  | `($f $a) =>
    let (head, args) := collectAppSpine f
    (head, args.push a)
  | _ => (t, #[])

open Lean Elab Term Meta in
/-- Apply a World combinator with fresh universe level metavars.
    `check` triggers universe unification. -/
private def mkWorldApp (name : Name) (args : Array Expr) : TermElabM Expr := do
  mkAppM name args

open Lean Elab Term Meta in
/-- Lift a type-level function application through World.Comp.
    Arity 1 only: `World.Comp f a`. -/
private def liftTypeApp (head : Syntax) (worldArgs : Array Expr) (worldLevel : Level) :
    TermElabM Expr := do
  let sortU := Expr.sort worldLevel
  match worldArgs.size with
  | 1 =>
    let f' ← elabTerm head (some (Expr.forallE `_ sortU sortU .default))
    mkWorldApp ``World.Comp #[f', worldArgs[0]!]
  | n =>
    throwError "world(...): lifting {n}-ary type-level functors is not supported (use Comp for unary)"

open Lean Elab Term Meta in
/-- Recursively elaborate a world expression. Returns `Nat → Type u`. -/
partial def elabWorldCore (t : Syntax) (_expectedType? : Option Expr) : TermElabM Expr := do
  match t with
  | `($a → $b) =>
    let a' ← elabWorldCore a none
    let b' ← elabWorldCore b none
    discard <| unifyWorldTypes a' b'
    mkWorldApp ``World.Function #[a', b']
  | `($a × $b) =>
    let a' ← elabWorldCore a none
    let b' ← elabWorldCore b none
    discard <| unifyWorldTypes a' b'
    mkWorldApp ``World.Prod #[a', b']
  | `($a ⊕ $b) =>
    let a' ← elabWorldCore a none
    let b' ← elabWorldCore b none
    discard <| unifyWorldTypes a' b'
    mkWorldApp ``World.Sum #[a', b']
  | `(▹ $a) =>
    let a' ← elabWorldCore a none
    mkWorldApp ``Later #[a']
  | `(γ $x:ident, $body) =>
    let xName := x.getId
    -- The variable X has type `Nat → Type u` for some u
    let u ← mkFreshLevelMVar
    let famType := Expr.forallE `n (mkConst ``Nat) (mkSort (.succ u)) .default
    withLocalDecl xName .default famType fun xVar => do
      let body' ← elabWorldCore body none
      let functor ← mkLambdaFVars #[xVar] body'
      mkWorldApp ``World.Fix #[functor]
  | `(($a)) =>
    elabWorldCore a none
  | `($f $a) =>
    let (head, argsSyn) := collectAppSpine t
    let headName := head.getId
    -- Check desugared Prod/Sum heads
    if (headName == ``Prod || headName == ``_root_.Prod) && argsSyn.size == 2 then
      let a' ← elabWorldCore argsSyn[0]! none
      let b' ← elabWorldCore argsSyn[1]! none
      discard <| unifyWorldTypes a' b'
      return ← mkWorldApp ``World.Prod #[a', b']
    if (headName == ``Sum || headName == ``_root_.Sum) && argsSyn.size == 2 then
      let a' ← elabWorldCore argsSyn[0]! none
      let b' ← elabWorldCore argsSyn[1]! none
      discard <| unifyWorldTypes a' b'
      return ← mkWorldApp ``World.Sum #[a', b']
    let worldArgs ← argsSyn.mapM (fun arg => do
      elabWorldCore arg none)
    -- Try head applied to world-family arguments directly
    let worldType ← do
      if h : worldArgs.size > 0 then inferType worldArgs[0]
      else
        let u ← mkFreshLevelMVar
        return Expr.forallE `n (mkConst ``Nat) (mkSort (.succ u)) .default
    let mut expectedHeadType := worldType
    for _ in worldArgs do
      expectedHeadType ← mkArrow worldType expectedHeadType
    let directResult? ← observing? do
      let head' ← elabTerm head (some expectedHeadType)
      let mut result := head'
      for arg in worldArgs do
        result := Expr.app result arg
      if ← isWorldFamily result then return result
      else throwError "not a World family"
    if let some e := directResult? then return e
    -- Fall back to type-level lifting (Comp)
    let worldLevel := match (← whnf worldType) with
      | .forallE _ _ (.sort u) _ => u
      | _ => Level.succ .zero
    liftTypeApp head worldArgs worldLevel
  | _ =>
    -- Base case: elaborate as term, wrap with Const if not already a World family
    -- Handle multi-arg Term.app: (Term.app head (null [arg1, arg2, ...]))
    if t.isOfKind ``Lean.Parser.Term.app then
      let head := t[0]!
      let argsNode := t[1]!
      let argsSyn := argsNode.getArgs
      -- Check desugared Prod/Sum
      let headName := head.getId
      if (headName == ``Prod || headName == ``_root_.Prod) && argsSyn.size == 2 then
        let a' ← elabWorldCore argsSyn[0]! none
        let b' ← elabWorldCore argsSyn[1]! none
        discard <| unifyWorldTypes a' b'
        return ← mkWorldApp ``World.Prod #[a', b']
      if (headName == ``Sum || headName == ``_root_.Sum) && argsSyn.size == 2 then
        let a' ← elabWorldCore argsSyn[0]! none
        let b' ← elabWorldCore argsSyn[1]! none
        discard <| unifyWorldTypes a' b'
        return ← mkWorldApp ``World.Sum #[a', b']
      -- General case: elaborate each arg through elabWorldCore
      let worldArgs ← argsSyn.mapM (fun arg => elabWorldCore arg none)
      let worldType ← do
        if h : worldArgs.size > 0 then inferType worldArgs[0]
        else
          let u ← mkFreshLevelMVar
          return Expr.forallE `n (mkConst ``Nat) (mkSort (.succ u)) .default
      let mut expectedHeadType := worldType
      for _ in worldArgs do
        expectedHeadType ← mkArrow worldType expectedHeadType
      let directResult? ← observing? do
        let head' ← elabTerm head (some expectedHeadType)
        let mut result := head'
        for arg in worldArgs do
          result := Expr.app result arg
        if ← isWorldFamily result then return result
        else throwError "not a World family"
      if let some e := directResult? then
        return e
      -- Fall back to Comp for unary
      if worldArgs.size == 1 then
        let worldLevel := match (← whnf worldType) with
          | .forallE _ _ (.sort u) _ => u
          | _ => Level.succ .zero
        return ← liftTypeApp head worldArgs worldLevel
    let e ← elabTerm t none
    if ← isWorldFamily e then
      -- Check if head is an inductive with .Rep; if so, replace with Rep
      return e
    else
      mkWorldApp ``World.Const #[e]

open Lean Elab Term Meta in
@[term_elab worldSyntax]
def elabWorld : TermElab := fun stx expectedType? =>
  match stx with
  | `(world($t)) => elabWorldCore t expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Tests -/

section Tests

-- Basic
example : Nat → Type := world(Unit × Nat)
example : Nat → Type := world(Unit ⊕ Nat)
example : Nat → Type := world(▹ Unit)

-- Comp
example (D : Nat → Type) : Nat → Type := world(List D)
example (D : Nat → Type) : Nat → Type := world(Option D)
example (D : Nat → Type) : Nat → Type := world(Env D)
example (D : Nat → Type) (n : Nat) : Type := world(D) n
example (D : Nat → Type) : Nat → Type := world(List D → D)
example (D : Nat → Type) : Nat → Type := world(D → List D)

-- World-level function application
example (F : (Nat → Type) → (Nat → Type)) (D : Nat → Type) : Nat → Type := world(F (▹D))
example (F : (Nat → Type) → (Nat → Type)) (D : Nat → Type) : Nat → Type := world(F D)

-- Universe-polymorphic (the key regression test)
example (D : Nat → Type) : Nat → Type := world(D × D)
example (D : Nat → Type) : Nat → Type := world(D ⊕ D)
example (D : Nat → Type) : Nat → Type := world(D → D)
example (D : Nat → Type) : Nat → Type := world(Nat ⊕ D × D)
example (D : Nat → Type) : Nat → Type := world(Unit ⊕ (Var × D → D) ⊕ ConTag × List (Var × D))
example (V W : Nat → Type) : Nat → Type := world(V ⊕ Event × W)
def testSig (D : Nat → Type) : Nat → Type := world(Nat ⊕ D × D)

-- Fixpoint
example : Nat → Type := world(γ X, Unit ⊕ ▹X)

end Tests
