/-!
# Syntax of the language

Ported from Syntax.agda. A simple untyped lambda calculus with
constructors, case expressions, and let bindings.
-/

abbrev Var := Nat
abbrev Con := Nat

/-! ## Events -/

/-- Trace events for recording evaluation steps. -/
inductive Event where
  | look : Var → Event
  | update : Event
  | app1 : Event
  | app2 : Event
  | case1 : Event
  | case2 : Event
  | let1 : Event
deriving Repr, BEq

mutual
  inductive Exp where
    | ref : Var → Exp
    | lam : Var → Exp → Exp
    | app : Exp → Var → Exp
    | let' : Var → Exp → Exp → Exp
    | conapp : Con → List Var → Exp
    | case' : Exp → List Alt → Exp
  deriving Repr

  structure Alt where
    con : Con
    vars : List Var
    rhs : Exp
  deriving Repr
end

def findAlt (K : Con) : List Alt → Option (List Var × Exp)
  | [] => none
  | alt :: alts =>
    if K == alt.con then some (alt.vars, alt.rhs)
    else findAlt K alts
