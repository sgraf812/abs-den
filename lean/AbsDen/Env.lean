/-!
# Environment and partial function operations

Replaces the association-list `A ⇀ B` from `PartialFunction.agda` with
`Std.HashMap` for idiomatic Lean.
-/
import AbsDen.Syntax

abbrev Env (V : Type) := Std.HashMap Var V

namespace Env

def empty : Env V := Std.HashMap.emptyWithCapacity 16

def lookup (ρ : Env V) (x : Var) : Option V := ρ[x]?

def bind (ρ : Env V) (x : Var) (v : V) : Env V := ρ.insert x v

def bindMany (ρ : Env V) (xs : List Var) (vs : List V) : Env V :=
  (xs.zip vs).foldl (fun ρ ⟨x, v⟩ => ρ.insert x v) ρ

/-- Map a partial function over a list of keys, looking each up in the env. -/
def pmapList (ρ : Env V) (xs : List Var) : Option (List V) :=
  xs.mapM (ρ.lookup ·)

end Env
