import AbsDen.Syntax
import Std

/-!
# Environment as HashMap

Uses `Std.HashMap Var V` for O(1) lookup.
-/

def Env (V : Type) : Type := Std.HashMap Var V

instance : EmptyCollection (Env V) := ⟨(∅ : Std.HashMap Var V)⟩

instance : Functor Env where
  map f (ρ : Env _) := Std.HashMap.fold (fun acc k v => acc.insert k (f v)) ∅ ρ

namespace Env

def empty {V : Type} : Env V := ∅

def find? {V : Type} (ρ : Env V) (x : Var) : Option V :=
  Std.HashMap.get? ρ x

def bind {V : Type} (ρ : Env V) (x : Var) (v : V) : Env V :=
  Std.HashMap.insert ρ x v

def bindMany {V : Type} (ρ : Env V) (xs : List Var) (vs : List V) : Env V :=
  (xs.zip vs).foldl (fun acc (x, v) => acc.insert x v) ρ

/-- Map a partial function over a list of keys, looking each up in the env. -/
def pmapList {V : Type} (ρ : Env V) (xs : List Var) : Option (List V) :=
  xs.mapM (ρ.find? ·)

end Env
