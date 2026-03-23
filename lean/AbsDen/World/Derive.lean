import AbsDen.World.Basic
import AbsDen.World.Elab
import Lean

/-!
# Derive handlers for World and LocalFunctor

Derive handlers that generate `World` and `LocalFunctor` instances
automatically from inductive definitions of step-indexed families.
-/

/-! ## Derive handler -/

namespace GenericDeriveHandler

open Lean Elab Term Meta Command

/-- How a field type lifts to the World algebra. -/
private inductive WorldLift where
  | world (w : Expr) (name? : Option Name := none)
  | const (t : Expr)
  | recVar
  | later (inner : WorldLift)
  | prod (a b : WorldLift)
  | sum (a b : WorldLift)
  | func (dom cod : WorldLift)
  | comp (F : Expr) (inner : WorldLift)
  deriving Inhabited

namespace WorldLift

def hasRecVar : WorldLift → Bool
  | .recVar => true
  | .later l | .comp _ l => l.hasRecVar
  | .prod a b | .sum a b | .func a b => a.hasRecVar || b.hasRecVar
  | _ => false

def toSyntax (lift : WorldLift) (recName : TSyntax `term) : TermElabM (TSyntax `term) := do
  match lift with
  | .world _ (some name) => return Lean.mkIdent name
  | .world w none => PrettyPrinter.delab w
  | .const t => PrettyPrinter.delab t
  | .recVar => return recName
  | .later l => do let s ← l.toSyntax recName; `(▹ $s)
  | .prod a b => do let sa ← a.toSyntax recName; let sb ← b.toSyntax recName; `($sa × $sb)
  | .sum a b => do let sa ← a.toSyntax recName; let sb ← b.toSyntax recName; `($sa ⊕ $sb)
  | .func a b => do let sa ← a.toSyntax recName; let sb ← b.toSyntax recName; `($sa → $sb)
  | .comp F l => do let sf ← PrettyPrinter.delab F; let sl ← l.toSyntax recName; `($sf $sl)

end WorldLift

/-! ### Field type analysis -/

/-- Check if `e` is `F n` where `F : Nat → Sort u` and `n` is `nFVar`. -/
private def matchFamilyApp? (e : Expr) (nFVar : Expr) : MetaM (Option Expr) := do
  if !e.isApp then return none
  if e.appArg! != nFVar then return none
  let fn := e.appFn!
  let fnTy ← whnf (← inferType fn)
  if fnTy.isForall then
    let .forallE _ dom _ _ := fnTy | return none
    if (← whnf dom).isConstOf ``Nat then return some fn
  return none

/-- Decompose a family expression into a WorldLift by recognizing known combinators. -/
private partial def liftFamily (fn : Expr) (nFVar : Expr)
    (recFVar? : Option Expr) : MetaM WorldLift := do
  if let some r := recFVar? then
    if fn == r then return .recVar
  if fn.isFVar then return .world fn (some (← fn.fvarId!.getUserName))
  let head := fn.getAppFn
  let args := fn.getAppArgs
  match head.constName?, args.size with
  | some ``Later, 1 =>
    return .later (← liftFamily args[0]! nFVar recFVar?)
  | some ``World.Prod, 2 =>
    return .prod (← liftFamily args[0]! nFVar recFVar?)
                 (← liftFamily args[1]! nFVar recFVar?)
  | some ``World.Sum, 2 =>
    return .sum (← liftFamily args[0]! nFVar recFVar?)
                (← liftFamily args[1]! nFVar recFVar?)
  | some ``World.Function, 2 =>
    return .func (← liftFamily args[0]! nFVar recFVar?)
                 (← liftFamily args[1]! nFVar recFVar?)
  | some ``World.Const, 1 =>
    return .const args[0]!
  | some ``World.Comp, 3 =>
    return .comp args[0]! (← liftFamily args[2]! nFVar recFVar?)
  | _, _ => return .world fn

/-- Check if a type is `Nat → Sort u` (a step-indexed family type). -/
private def isFamilyParamType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  if ty.isForall then
    let .forallE _ dom body _ := ty | return false
    if !(← whnf dom).isConstOf ``Nat then return false
    return body.isSort
  return false

private partial def liftFieldType (e : Expr) (nFVar : Expr)
    (recFVar? : Option Expr) : MetaM WorldLift := do
  -- Check for F n pattern before whnf
  if let some fn ← matchFamilyApp? e nFVar then
    return ← liftFamily fn nFVar recFVar?
  let e ← whnf e
  -- Check again after whnf
  if let some fn ← matchFamilyApp? e nFVar then
    return ← liftFamily fn nFVar recFVar?
  if e.isAppOfArity ``Prod 2 then
    return .prod (← liftFieldType e.appFn!.appArg! nFVar recFVar?)
                 (← liftFieldType e.appArg! nFVar recFVar?)
  if e.isAppOfArity ``Sum 2 then
    return .sum (← liftFieldType e.appFn!.appArg! nFVar recFVar?)
                (← liftFieldType e.appArg! nFVar recFVar?)
  if e.isForall then
    let .forallE _ dom body _ := e | unreachable!
    if body.hasLooseBVars then
      throwError "World.derive: cannot lift dependent function type"
    return .func (← liftFieldType dom nFVar recFVar?) (← liftFieldType body nFVar recFVar?)
  if !e.containsFVar nFVar.fvarId! then
    return .const e
  if e.isApp then
    let args := e.getAppArgs
    let fn := e.getAppFn
    let lastIdx? := Id.run do
      let mut r : Option Nat := none
      for i in [:args.size] do
        if args[i]!.containsFVar nFVar.fvarId! then r := some i
      return r
    if let some lastIdx := lastIdx? then
      if lastIdx == args.size - 1 then
        let innerLift ← liftFieldType args[lastIdx]! nFVar recFVar?
        let head := args[:lastIdx].foldl (init := fn) Expr.app
        if (← whnf head).isConstOf ``Later then
          return .later innerLift
        return .comp head innerLift
  throwError "World.derive: cannot lift type{indentExpr e}"

/-! ### Constructor analysis -/

private def mkProdLift (fields : Array WorldLift) : WorldLift :=
  if fields.isEmpty then .const (Lean.mkConst ``Unit)
  else Id.run do
    let mut r := fields.back!
    for i in [1:fields.size] do
      r := .prod fields[fields.size - 1 - i]! r
    return r

private def mkSumLift (ctors : Array WorldLift) : WorldLift := Id.run do
  let mut r := ctors.back!
  for i in [1:ctors.size] do
    r := .sum ctors[ctors.size - 1 - i]! r
  return r

private structure CtorAnalysis where
  name : Name
  numFields : Nat
  fieldLifts : Array WorldLift
  prodLift : WorldLift

private def analyzeInductive (declName : Name) :
    TermElabM (Array CtorAnalysis × WorldLift) := do
  let indVal ← getConstInfoInduct declName
  forallTelescope indVal.type fun params _sort => do
    if params.isEmpty then
      throwError "World.derive: {declName} has no parameters"
    let nFVar := params.back!
    unless (← whnf (← inferType nFVar)).isConstOf ``Nat do
      throwError "World.derive: last parameter of {declName} must be Nat"
    let mut recFVar? : Option Expr := none
    for p in params.pop do
      if ← isFamilyParamType (← inferType p) then
        recFVar? := some p
    let ctorAnalyses ← indVal.ctors.toArray.mapM fun ctorName => do
      let ctorInfo ← getConstInfoCtor ctorName
      forallTelescope ctorInfo.type fun ctorParams _target => do
        let fields := ctorParams[indVal.numParams:].toArray
        let fieldLifts ← fields.mapM fun fp => do
          let ty := (← inferType fp).replaceFVars ctorParams[:indVal.numParams].toArray params
          liftFieldType ty nFVar recFVar?
        return { name := ctorName, numFields := fields.size,
                 fieldLifts, prodLift := mkProdLift fieldLifts : CtorAnalysis }
    return (ctorAnalyses, mkSumLift (ctorAnalyses.map (·.prodLift)))

/-! ### Syntax generation -/

/-- Analyze all parameters: binders, names, recursive param name, and string representations. -/
private def analyzeParams (indVal : InductiveVal) : TermElabM
    (TSyntaxArray `Lean.Parser.Term.funBinder × Array (TSyntax `term) ×
     TSyntax `term × String × String) := do
  forallTelescope indVal.type fun params _ => do
    let nonNatParams := params.pop
    let binders ← nonNatParams.mapM fun p => do
      let pName := Lean.mkIdent (← p.fvarId!.getUserName)
      let pTy ← PrettyPrinter.delab (← inferType p)
      `(Lean.Parser.Term.funBinder| ($pName : $pTy))
    let names ← nonNatParams.mapM fun p =>
      return (Lean.mkIdent (← p.fvarId!.getUserName) : TSyntax `term)
    let paramStr ← nonNatParams.foldlM (init := "") fun acc p => do
      return acc ++ s!"({← p.fvarId!.getUserName} : Nat → Type) "
    let paramNamesStr := names.foldl (init := "") fun acc n => acc ++ s!" {n.raw.getId}"
    -- Recursive param = last family param
    let mut recName : TSyntax `term := Lean.mkIdent `_noFamilyParam
    for p in nonNatParams.reverse do
      if ← isFamilyParamType (← inferType p) then
        recName := Lean.mkIdent (← p.fvarId!.getUserName); break
    return (binders.map TSyntax.mk, names, recName, paramStr.trimAsciiEnd.toString, paramNamesStr)

/-- Wrap a string in Sum.inl/Sum.inr for ctor at `idx` of `total`. -/
private def wrapSumStr (inner : String) (idx total : Nat) : String :=
  if total == 1 then inner
  else Id.run do
    let mut r := if idx < total - 1 then s!"Sum.inl {inner}" else inner
    for _ in [:idx] do
      r := s!"Sum.inr ({r})"
    return r

private def parseCommand (s : String) : CommandElabM Syntax := do
  IO.ofExcept <| Lean.Parser.runParserCategory (← getEnv) `command s

/-! ### deriving World -/

/-- Generate a direct `World` instance by pattern-matching on constructors. -/
def deriveWorld (declName : Name) : CommandElabM Unit := do
  let indVal ← liftTermElabM <| getConstInfoInduct declName
  let (ctorAnalyses, _sigLift) ← liftTermElabM <| analyzeInductive declName
  let (_binders, _names, _recParamName, paramStr, paramNamesStr) ←
    liftTermElabM <| analyzeParams indVal
  -- Strip current namespace to avoid double-prefixing
  let ns ← getCurrNamespace
  let relName := declName.replacePrefix ns .anonymous
  let fStr := toString relName
  -- Build World constraint string for each family param: {D : Nat → Type} → [World D]
  let worldParamStr ← liftTermElabM <| forallTelescope indVal.type fun params _ => do
    let nonNatParams := params.pop
    let mut s := ""
    for p in nonNatParams do
      let name ← p.fvarId!.getUserName
      if ← isFamilyParamType (← inferType p) then
        s := s ++ s!"\{{name} : Nat → Type} [World {name}] "
      else
        s := s ++ s!"({name} : Nat → Type) "
    return s.trimAsciiEnd.toString
  -- Build restrictStep match arms
  let mut arms := ""
  for ca in ctorAnalyses do
    let vars := (Array.range ca.numFields).map fun i => s!"x{i}"
    let ctorShort := ca.name.getString!
    let varList := vars.foldl (init := "") fun acc v => acc ++ s!" {v}"
    let mut restrictedVars : Array String := #[]
    for i in [:ca.numFields] do
      let v := vars[i]!
      let rep := ca.fieldLifts[i]!
      if rep matches .const _ then
        restrictedVars := restrictedVars.push v
      else
        restrictedVars := restrictedVars.push s!"(World.restrictStep {v})"
    let restrictedVarList := restrictedVars.foldl (init := "") fun acc v => acc ++ s!" {v}"
    arms := arms ++ s!"    | .{ctorShort}{varList} => .{ctorShort}{restrictedVarList}\n"
  let cmd := s!"instance {worldParamStr} : World ({fStr}{paramNamesStr}) where\n  restrictStep\n{arms}"
  elabCommand (← parseCommand cmd)

/-! ### deriving LocalFunctor -/

/-- Build a `LocalFunctor` proof term from a `WorldLift` tree.
    `xFVar` is the bound variable of the functor (the recursive family param).
    Returns a proof of `LocalFunctor (fun xFVar => <combinator expression>)`. -/
private partial def buildLocalFunctorProof (lift : WorldLift) (xFVar : Expr) :
    MetaM Expr := do
  match lift with
  | .recVar =>
    -- instId : LocalFunctor (fun X => X). Telescope: (no value params)
    mkAppOptM ``LocalFunctor.instId #[]
  | .const _ | .world _ _ => do
    -- instConst : {P} → LocalFunctor (fun _ => P). Telescope: {P}
    let body ← buildCombinatorExpr lift xFVar
    mkAppOptM ``LocalFunctor.instConst #[some body]
  | .sum a b => do
    -- instSum : {F₁} → {F₂} → [LF F₁] → [LF F₂] → LF (fun X => Sum (F₁ X) (F₂ X))
    let proofA ← buildLocalFunctorProof a xFVar
    let proofB ← buildLocalFunctorProof b xFVar
    let bodyA ← buildCombinatorExpr a xFVar
    let bodyB ← buildCombinatorExpr b xFVar
    let funA ← mkLambdaFVars #[xFVar] bodyA
    let funB ← mkLambdaFVars #[xFVar] bodyB
    mkAppOptM ``LocalFunctor.instSum #[some funA, some funB, some proofA, some proofB]
  | .prod a b => do
    let proofA ← buildLocalFunctorProof a xFVar
    let proofB ← buildLocalFunctorProof b xFVar
    let bodyA ← buildCombinatorExpr a xFVar
    let bodyB ← buildCombinatorExpr b xFVar
    let funA ← mkLambdaFVars #[xFVar] bodyA
    let funB ← mkLambdaFVars #[xFVar] bodyB
    mkAppOptM ``LocalFunctor.instProd #[some funA, some funB, some proofA, some proofB]
  | .func a b => do
    let proofA ← buildLocalFunctorProof a xFVar
    let proofB ← buildLocalFunctorProof b xFVar
    let bodyA ← buildCombinatorExpr a xFVar
    let bodyB ← buildCombinatorExpr b xFVar
    let funA ← mkLambdaFVars #[xFVar] bodyA
    let funB ← mkLambdaFVars #[xFVar] bodyB
    mkAppOptM ``LocalFunctor.instFunction #[some funA, some funB, some proofA, some proofB]
  | .later l => do
    -- instComp : {F} → {G} → [LF F] → [LF G] → LF (fun X => F (G X))
    -- With F = Later, G = inner functor
    let proofL ← buildLocalFunctorProof l xFVar
    let bodyL ← buildCombinatorExpr l xFVar
    let funL ← mkLambdaFVars #[xFVar] bodyL
    let laterConst ← mkConstWithFreshMVarLevels ``Later
    let laterLF ← mkConstWithFreshMVarLevels ``LocalFunctor.instLater
    mkAppOptM ``LocalFunctor.instComp #[some laterConst, some funL, some laterLF, some proofL]
  | .comp F l => do
    -- instWorldComp : {G} → {F} → [Functor G] → [LF F] → LF (fun X => Comp G (F X))
    let proofL ← buildLocalFunctorProof l xFVar
    let bodyL ← buildCombinatorExpr l xFVar
    let funL ← mkLambdaFVars #[xFVar] bodyL
    mkAppOptM ``LocalFunctor.instWorldComp #[none, some funL, none, some proofL]
where
  /-- Build the combinator expression for a WorldLift node applied to xFVar.
      Resolves `.world` names from the current local context (not stale fvars). -/
  buildCombinatorExpr (lift : WorldLift) (xFVar : Expr) : MetaM Expr := do
    match lift with
    | .recVar => return xFVar
    | .const t => mkAppM ``World.Const #[t]
    | .world _ (some name) =>
      -- Resolve the name in the current local context
      let lctx ← getLCtx
      match lctx.findFromUserName? name with
      | some decl => return .fvar decl.fvarId
      | none => throwError "buildCombinatorExpr: unknown variable '{name}'"
    | .world w none => return w
    | .sum a b =>
      let ea ← buildCombinatorExpr a xFVar
      let eb ← buildCombinatorExpr b xFVar
      mkAppM ``World.Sum #[ea, eb]
    | .prod a b =>
      let ea ← buildCombinatorExpr a xFVar
      let eb ← buildCombinatorExpr b xFVar
      mkAppM ``World.Prod #[ea, eb]
    | .func a b =>
      let ea ← buildCombinatorExpr a xFVar
      let eb ← buildCombinatorExpr b xFVar
      mkAppM ``World.Function #[ea, eb]
    | .later l =>
      let el ← buildCombinatorExpr l xFVar
      mkAppM ``Later #[el]
    | .comp F l =>
      let el ← buildCombinatorExpr l xFVar
      mkAppM ``World.Comp #[F, el]

/-- Generate rep, bijection (toRep/ofRep), and LocalFunctor instance. -/
def deriveLocalFunctor (declName : Name) : CommandElabM Unit := do
  let indVal ← liftTermElabM <| getConstInfoInduct declName
  let (ctorAnalyses, sigLift) ← liftTermElabM <| analyzeInductive declName
  let (binders, _names, recParamName, paramStr, paramNamesStr) ←
    liftTermElabM <| analyzeParams indVal
  unless sigLift.hasRecVar do
    throwError "deriving LocalFunctor: {declName} has no recursive family parameter"
  -- Strip current namespace to avoid double-prefixing
  let ns ← getCurrNamespace
  let relName := declName.replacePrefix ns .anonymous
  -- Generate rep
  let repBody ← liftTermElabM <| sigLift.toSyntax recParamName
  let repName := Lean.mkIdent (relName ++ `Rep)
  elabCommand (← `(abbrev $repName := fun $binders* => world($repBody)))
  -- Generate toRep/ofRep bijection
  let fStr := toString relName
  let repStr := toString (relName ++ `Rep)
  let mut toRepArms := ""
  let mut ofRepArms := ""
  for (ca, ctorIdx) in ctorAnalyses.zipIdx do
    let vars := (Array.range ca.numFields).map fun i => s!"x{i}"
    let ctorShort := ca.name.getString!
    let varList := vars.foldl (init := "") fun acc v => acc ++ s!" {v}"
    let prodStr := if vars.isEmpty then "()" else Id.run do
      let mut r := vars.back!
      for i in [1:vars.size] do r := s!"({vars[vars.size - 1 - i]!}, {r})"
      return r
    let sumStr := wrapSumStr prodStr ctorIdx ctorAnalyses.size
    toRepArms := toRepArms ++ s!"    | .{ctorShort}{varList} => {sumStr}\n"
    ofRepArms := ofRepArms ++ s!"    | {sumStr} => .{ctorShort}{varList}\n"
  let cmds := #[
    s!"def {relName ++ `toRep} {paramStr} \{n : Nat} (x : {fStr}{paramNamesStr} n) : ({repStr}{paramNamesStr}) n := match x with\n{toRepArms}",
    s!"def {relName ++ `ofRep} {paramStr} \{n : Nat} (x : ({repStr}{paramNamesStr}) n) : {fStr}{paramNamesStr} n := match x with\n{ofRepArms}"
  ]
  for cmd in cmds do
    elabCommand (← parseCommand cmd)
  -- Generate LocalFunctor instance via derive_local_functor tactic.
  -- The rep is composed of World combinators, so the tactic can decompose it.
  let repStr := toString (relName ++ `Rep)
  -- Build non-rec param string for the instance
  let nonRecParamStr ← liftTermElabM <| forallTelescope indVal.type fun params _ => do
    let nonNatParams := params.pop
    let mut recIdx := nonNatParams.size - 1
    for i in [:nonNatParams.size] do
      let j := nonNatParams.size - 1 - i
      if ← isFamilyParamType (← inferType nonNatParams[j]!) then
        recIdx := j; break
    let nonRecParams := (nonNatParams.toList.eraseIdx recIdx).toArray
    let mut s := ""
    for p in nonRecParams do
      let name ← p.fvarId!.getUserName
      if ← isFamilyParamType (← inferType p) then
        s := s ++ s!"({name} : Nat → Type) [World {name}] "
      else
        s := s ++ s!"({name} : Nat → Type) "
    return s.trimAsciiEnd.toString
  let nonRecNamesStr ← liftTermElabM <| forallTelescope indVal.type fun params _ => do
    let nonNatParams := params.pop
    let mut recIdx := nonNatParams.size - 1
    for i in [:nonNatParams.size] do
      let j := nonNatParams.size - 1 - i
      if ← isFamilyParamType (← inferType nonNatParams[j]!) then
        recIdx := j; break
    let nonRecParams := (nonNatParams.toList.eraseIdx recIdx).toArray
    let mut s := ""
    for p in nonRecParams do
      s := s ++ s!" {← p.fvarId!.getUserName}"
    return s
  let lfCmd := s!"instance {relName ++ `instLocalFunctor} {nonRecParamStr} : LocalFunctor ({repStr}{nonRecNamesStr}) where\n  instWorld _ := inferInstance\n  property := by exact (by derive_local_functor : LocalFunctor ({repStr}{nonRecNamesStr})).property"
  elabCommand (← parseCommand lfCmd)
  elabCommand (← parseCommand s!"attribute [instance] {relName ++ `instLocalFunctor}")

end GenericDeriveHandler

open Lean Elab in
private def mkWorldHandler : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  let declName := declNames[0]!
  unless ← Lean.isInductive declName do return false
  GenericDeriveHandler.deriveWorld declName
  return true

open Lean Elab in
private def mkLocalFunctorHandler : DerivingHandler := fun declNames => do
  if declNames.size != 1 then return false
  let declName := declNames[0]!
  unless ← Lean.isInductive declName do return false
  GenericDeriveHandler.deriveLocalFunctor declName
  return true

initialize
  Lean.Elab.registerDerivingHandler ``World mkWorldHandler
  Lean.Elab.registerDerivingHandler ``LocalFunctor mkLocalFunctorHandler
