/-!
# Syntax of the language

Ported from Syntax.agda. A simple untyped lambda calculus with
constructors, case expressions, and let bindings.
-/

abbrev Var := Nat
abbrev Con := Nat

inductive Exp where
  | ref : Var → Exp
  | lam : Var → Exp → Exp
  | app : Exp → Var → Exp
  | let' : Var → Exp → Exp → Exp
  | conapp : Con → List Var → Exp
  | case' : Exp → List Alt → Exp
with Alt where
  | mk : Con → List Var → Exp → Alt
deriving Repr, BEq

namespace Alt

def con : Alt → Con
  | .mk K _ _ => K

def vars : Alt → List Var
  | .mk _ vs _ => vs

def rhs : Alt → Exp
  | .mk _ _ e => e

end Alt

def findAlt (K : Con) : List Alt → Option (List Var × Exp)
  | [] => none
  | (.mk K' vs rhs) :: alts =>
    if K == K' then some (vs, rhs)
    else findAlt K alts
