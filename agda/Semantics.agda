{-# OPTIONS --cubical --guarded #-}
-- | This module defines the denotational interpreter and its type class
-- algebra. The by-name and by-need instances can be found in Concrete.agda.
module Semantics where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List as List
open import Data.List.Membership.Propositional
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (T)
open import Function
open import PartialFunction
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Relation.Nullary.Base

data Event : Set where
  look : Var → Event
  update : Event
  app1 : Event
  app2 : Event
  case1 : Event
  case2 : Event
  let1 : Event

record Trace (T : Set) : Set where
  field
    step : Event → ▹ T → T
open Trace {{...}} public

-- Parameterised over a predicate p characterising definable environment
-- elements.
record Domain (D : Set) (p : D → Set) : Set where
  field
    stuck : D
    fun : (Σ D p → D) → D
    apply : D → Σ D p → D
    con : Var → List (Σ D p) → D
    select : D → List (Var × (List (Σ D p) → D)) → D
open Domain {{...}} public

record HasBind (D : Set) : Set where
  field
    bind : ▹(▹ D → D) → (▹ D → D) → D
open HasBind {{...}} public

-- This is the predicate characterising elements that end up in the environment:
is-env : ∀ {D} {{trc : Trace D}} → D → Set
is-env {D} d = ∃[ x ] ∃[ d▹ ] (d ≡ step {D} (look x) d▹)

-- The following definition corresponds to the interpreter definition in
-- Haskell. Note the use of is-env and the passing of ticks.
-- Tests comparing data constructor arity are presently omitted.
𝒮⟦_⟧_ :  ∀ {D} {{_ : Trace D}} {{_ : Domain D is-env}} {{_ : HasBind D}}
         → Exp → (Var ⇀ Σ D is-env) → D
𝒮⟦_⟧_ {D} e ρ = fix sem e ρ
  where
    sem : ▹(Exp → (Var ⇀ Σ D is-env) → D) → Exp → (Var ⇀ Σ D is-env) → D
    sem recurse▹ (ref x) ρ with ρ x
    ... | nothing      = stuck
    ... | just (d , _) = d
    sem recurse▹ (lam x body) ρ =
      fun (λ d → step app2 (λ α → recurse▹ α body (ρ [ x ↦ d ])))
    sem recurse▹ (app e x) ρ with ρ x
    ... | nothing = stuck
    ... | just d  = step app1 (λ α → apply (recurse▹ α e ρ) d)
    sem recurse▹ (let' x e₁ e₂) ρ =
      bind  (λ α d₁ →
              recurse▹ α e₁ (ρ [ x ↦ (step (look x) d₁ , x , d₁ , refl) ]))
            (λ d₁ → step let1 (λ α →
              recurse▹ α e₂ (ρ [ x ↦ (step (look x) d₁ , x , d₁ , refl) ])))
    sem recurse▹ (conapp K xs) ρ with pmap ρ xs
    ... | nothing = stuck
    ... | just ds = con K ds
    sem recurse▹ (case' eₛ alts) ρ =
      step case1 (λ α → select (recurse▹ α eₛ ρ) (List.map alt alts))
        where
          alt : Con × List Var × Exp → Con × (List (Σ D is-env) → D)
          alt (k , xs , eᵣ) = (k , (λ ds →
            step  case2 (λ α → recurse▹ α eᵣ (ρ [ xs ↦* ds ]))))
