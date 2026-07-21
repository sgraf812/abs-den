import AbsDen.NonExpansive
import AbsDen.Syntax

/-! # Environments

Mirrors `AbsDen/Env.lean`: a map from variables to domain elements. Here it is a
total function `Var → Option d` carrying the pointwise OFE, with update notation
`ρ[x ↦ a]`. -/

open Iris Iris.COFE OFE

namespace AbsDen

/-- Environment: a partial map from variables to domain elements. -/
def Env (d : Type) : Type := Var → Option d

instance [OFE d] : OFE (Env d) := inferInstanceAs (OFE (Var → Option d))

namespace Env

/-- Look up a variable. -/
def get {d : Type} (ρ : Env d) (x : Var) : Option d := ρ x

/-- The empty environment. -/
def empty {d : Type} : Env d := fun _ => none

/-- Update an environment at `x`. -/
def extend {d : Type} (ρ : Env d) (x : Var) (a : d) : Env d := fun y => if y = x then some a else ρ y

/-- `ρ[x ↦ a]` updates `ρ` at `x` (`noWs` before `[` avoids clashing with `[]`). -/
syntax:max term:max noWs "[" term " ↦ " term "]" : term
macro_rules | `($ρ[$x ↦ $a]) => `(Env.extend $ρ $x $a)

theorem get_extend_self {d : Type} (ρ : Env d) (x : Var) (a : d) :
    (ρ[x ↦ a]).get x = some a := by
  simp [Env.get, Env.extend]

theorem get_extend_ne {d : Type} (ρ : Env d) {x y : Var} (a : d) (h : y ≠ x) :
    (ρ[x ↦ a]).get y = ρ.get y := by
  simp [Env.get, Env.extend, h]

/-- Look up a list of variables, failing if any is unbound. -/
def getMany {d : Type} (ρ : Env d) : List Var → Option (List d)
  | [] => some []
  | x :: xs => (ρ.get x).bind (fun a => (ρ.getMany xs).map (a :: ·))

/-- Bind a list of variables to a list of values (used at `case` alternatives). -/
def extendMany {d : Type} (ρ : Env d) : List Var → List d → Env d
  | x :: xs, v :: vs => (ρ[x ↦ v]).extendMany xs vs
  | _, _ => ρ

/-- `ρ[xs ↦* ds]` binds the variables of `xs` pointwise to the values of `ds`. -/
syntax:max term:max noWs "[" term " ↦* " term "]" : term
macro_rules | `($ρ[$xs ↦* $ds]) => `(Env.extendMany $ρ $xs $ds)

/-- `x ∈ ρ` means `x` is bound in `ρ`. -/
instance {d : Type} : Membership Var (Env d) := ⟨fun ρ x => (ρ.get x).isSome⟩

/-- `ρ[x]?` looks `x` up (an `Option`); `ρ[x]` needs a proof that `x` is bound. -/
instance {d : Type} : GetElem? (Env d) Var d (fun ρ x => x ∈ ρ) where
  getElem ρ x h := (ρ.get x).get h
  getElem? ρ x := ρ.get x

/-- `ρ[xs]?` looks up a list of variables (an `Option`, failing if any is
    unbound); `ρ[xs]` needs a proof that the whole lookup succeeds. -/
instance {d : Type} : GetElem? (Env d) (List Var) (List d)
    (fun ρ xs => (ρ.getMany xs).isSome) where
  getElem ρ xs h := (ρ.getMany xs).get h
  getElem? ρ xs := ρ.getMany xs

/-- Unfold `ρ[xs]?` to `getMany`. -/
theorem getElem?_getMany {d : Type} (ρ : Env d) (xs : List Var) :
    ρ[xs]? = ρ.getMany xs := rfl

variable {d : Type} [OFE d]

/-- Lookup is non-expansive in the environment. -/
instance ne_get (x : Var) : NonExpansive (fun ρ : Env d => ρ.get x) := ⟨fun _ _ _ h => h x⟩

/-- Update is non-expansive in the environment. -/
instance ne_extendEnv (x : Var) (a : d) : NonExpansive (fun ρ : Env d => ρ[x ↦ a]) := by
  refine ⟨fun {_ _ _} h y => ?_⟩
  simp only [extend]; split
  · exact OFE.dist_eqv.refl _
  · exact h y

/-- Update is non-expansive in the bound value. -/
instance ne_extendVal (ρ : Env d) (x : Var) : NonExpansive (fun a : d => ρ[x ↦ a]) := by
  refine ⟨fun {_ _ _} ha y => ?_⟩
  simp only [extend]; split
  · exact some_dist_some.mpr ha
  · exact OFE.dist_eqv.refl _

theorem getMany_ne {n} {ρ ρ' : Env d} (h : ρ ≡{n}≡ ρ') :
    ∀ xs, ρ.getMany xs ≡{n}≡ ρ'.getMany xs
  | [] => OFE.dist_eqv.refl _
  | x :: xs =>
    Option.bind_ne
      (fun _ _ ha => Option.map_ne (fun _ _ hl => List.Forall₂.cons ha hl) (getMany_ne h xs))
      (h x)

/-- Multi-lookup is non-expansive in the environment. -/
instance ne_getMany (xs : List Var) : NonExpansive (fun ρ : Env d => ρ[xs]?) :=
  ⟨fun _ _ _ h => getMany_ne h xs⟩

theorem extendMany_ne {n} : ∀ (xs : List Var) {ρ ρ' : Env d} {ds ds' : List d},
    ρ ≡{n}≡ ρ' → ds ≡{n}≡ ds' → ρ[xs ↦* ds] ≡{n}≡ ρ'[xs ↦* ds']
  | [], _, _, _, _, hρ, _ => hρ
  | _ :: _, _, _, _, _, hρ, .nil => hρ
  | x :: xs, _, _, _, _, hρ, .cons hv hvs =>
      extendMany_ne xs (OFE.Dist.trans ((ne_extendEnv x _).ne hρ) ((ne_extendVal _ x).ne hv)) hvs

/-- Multi-bind is non-expansive in the environment. -/
instance ne_extendManyEnv (xs : List Var) (ds : List d) :
    NonExpansive (fun ρ : Env d => ρ[xs ↦* ds]) :=
  ⟨fun _ _ _ h => extendMany_ne xs h (OFE.dist_eqv.refl ds)⟩

/-- Multi-bind is non-expansive in the bound values. -/
instance ne_extendManyVals (ρ : Env d) (xs : List Var) :
    NonExpansive (fun ds : List d => ρ[xs ↦* ds]) :=
  ⟨fun _ _ _ h => extendMany_ne xs (OFE.dist_eqv.refl ρ) h⟩

end Env

end AbsDen
