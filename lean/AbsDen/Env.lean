import AbsDen.Syntax
import AbsDen.World.Basic

/-!
# Well-scoped step-indexed environment

`Env D m n = Fin m → D n` — a total mapping from de Bruijn indices to
denotations at step `n`. With well-scoped syntax variable lookup never fails.

Convention: index `0` is the innermost binder. `bind` extends the scope by
pushing a new innermost binding; `bindMany` binds a list whose head ends up
innermost.
-/

def Env (D : Nat → Type) (m : Nat) : Nat → Type := fun n => Fin m → D n

instance {D : Nat → Type} [World D] {m : Nat} : World (Env D m) where
  restrictStep ρ := fun i => World.restrictStep (ρ i)

namespace Env

def empty {D : Nat → Type} {n : Nat} : Env D 0 n := Fin.elim0

def lookup {D : Nat → Type} {m n : Nat} (ρ : Env D m n) (x : Fin m) : D n := ρ x

def bind {D : Nat → Type} {m n : Nat} (ρ : Env D m n) (v : D n) : Env D (m+1) n :=
  Fin.cases v ρ

def bindMany {D : Nat → Type} {m n : Nat} (ρ : Env D m n) :
    (vs : List (D n)) → Env D (m + vs.length) n
  | [] => ρ
  | v :: vs => (ρ.bindMany vs).bind v

def mapList {D : Nat → Type} {m n : Nat} (ρ : Env D m n) (xs : List (Fin m)) : List (D n) :=
  xs.map ρ

end Env
