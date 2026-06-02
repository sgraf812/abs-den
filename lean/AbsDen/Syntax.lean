/-!
# Well-scoped syntax of the language

`Exp n` is the type of expressions with `n` free variables in scope.
Variable references are de Bruijn indices (`Fin n`, with `0` = innermost binder).
Each binder also carries a `Name` annotation used only for trace events.
-/

abbrev Name := Nat
abbrev ConTag := Nat

/-! ## Events -/

/-- Trace events for recording evaluation steps. -/
inductive Event where
  | look : Name → Event
  | update : Event
  | app1 : Event
  | app2 : Event
  | case1 : Event
  | case2 : Event
  | let1 : Event
deriving Repr, BEq

mutual
  inductive Exp : Nat → Type where
    | ref    : Fin n → Exp n
    | lam    : Name → Exp (n+1) → Exp n
    | app    : Exp n → Fin n → Exp n
    | let'   : Name → Exp (n+1) → Exp (n+1) → Exp n
    | conapp : ConTag → List (Fin n) → Exp n
    | case'  : Exp n → AltList n → Exp n

  /-- A list of case alternatives, indexed by the ambient scope `n`.
      Each `cons` carries the constructor tag, the list of name annotations,
      and an rhs whose scope is `n + vars.length`. -/
  inductive AltList : Nat → Type where
    | nil  : AltList n
    | cons : (con : ConTag) → (vars : List Name) →
             Exp (n + vars.length) → AltList n → AltList n
end

namespace AltList

/-- Linear search for an alternative matching constructor tag `K`. -/
def find? : AltList n → ConTag → Option ((vars : List Name) × Exp (n + vars.length))
  | .nil, _ => none
  | .cons c vs rhs rest, K =>
    if c == K then some ⟨vs, rhs⟩ else rest.find? K

/-- Map each alternative to a value, with access to scope `n` and the rhs. -/
def foldr (f : (vars : List Name) → ConTag → Exp (n + vars.length) → β → β) (z : β) :
    AltList n → β
  | .nil => z
  | .cons c vs rhs rest => f vs c rhs (rest.foldr f z)

end AltList

/-! ## Pretty-printing -/

mutual
  def Exp.toString {n : Nat} : Exp n → String
    | .ref x => s!"ref {x.val}"
    | .lam x e => s!"λ{x}.{e.toString}"
    | .app e x => s!"({e.toString}) {x.val}"
    | .let' x e₁ e₂ => s!"let {x} = {e₁.toString} in {e₂.toString}"
    | .conapp K xs => s!"K{K}{xs.map Fin.val}"
    | .case' e alts => s!"case {e.toString} of {AltList.toString alts}"

  def AltList.toString {n : Nat} : AltList n → String
    | .nil => ""
    | .cons K vs rhs rest => s!"| K{K} {vs} → {rhs.toString}{rest.toString}"
end

instance {n : Nat} : ToString (Exp n) := ⟨Exp.toString⟩
