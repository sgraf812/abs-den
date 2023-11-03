{-# OPTIONS --cubical --guarded --rewriting #-}
module Semantics where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List as List hiding (lookup)
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

-- Type classes

data Event : Set where
  lookup : Var → Event
  update : Event
  app1 : Event
  app2 : Event
  case1 : Event
  case2 : Event
  let1 : Event

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A} {B} → M A → (A → M B) → M B
  _>>_ : ∀ {A} {B} → M A → M B → M B
  l >> r = l >>= (λ _ → r)
open Monad {{...}}

record Trace (T : Set → Set) : Set₁ where
  field
    {{monad}} : Monad T
    step : ∀ {V} → Event → ▹ (T V) → T V
open Trace {{...}}

record Domain (D : Set) (p : D → Set) : Set where
  field
    stuck : D
    fun : (Σ D p → D) → D
    apply : D → Σ D p → D
    con : Var → List (Σ D p) → D
    select : D → List (Var × (List (Σ D p) → D)) → D
open Domain {{...}}

record HasBind (D : Set) : Set where
  field
    bind : ▹(▹ D → D) → (▹ D → D) → D
open HasBind {{...}}

-- | This characterises the subtype of `τ v` that we pass around in `fun` and `apply`
is-look : ∀ {τ} {v} {{trc : Trace τ}} → τ v → Set
is-look {τ} d = ∃[ x ] ∃[ d▹ ] (d ≡ step {τ} (lookup x) d▹)

S⟦_⟧_ : ∀ {τ} {v} {{_ : Trace τ}} {{_ : Domain (τ v) is-look}} {{_ : HasBind (τ v)}}
      → Exp → (Var ⇀ Σ (τ v) is-look) → τ v
S⟦_⟧_ {τ} {v} e ρ = fix sem' e ρ
  where
    sem' : ▹(Exp → (Var ⇀ Σ (τ v) is-look) → τ v) → Exp → (Var ⇀ Σ (τ v) is-look) → τ v
    sem' recurse▹ (ref x) ρ with ρ x
    ... | nothing      = stuck
    ... | just (d , _) = d
    sem' recurse▹ (lam x body) ρ = fun (λ d → step app2 (λ α → recurse▹ α body (ρ [ x ↦ d ])))
    sem' recurse▹ (app e x) ρ with ρ x
    ... | nothing = stuck
    ... | just d  = step app1 (λ α → apply (recurse▹ α e ρ) d)
    sem' recurse▹ (let' x e₁ e₂) ρ =
      bind (λ α d₁ → recurse▹ α e₁ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ]))
           (λ d₁ → step let1 (λ α → recurse▹ α e₂ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ])))
    sem' recurse▹ (conapp K xs) ρ with pmap ρ xs
    ... | nothing = stuck
    ... | just ds = con K ds -- lacking test that length xs matches the arity of K
    sem' recurse▹ (case' eₛ alts) ρ =
      step case1 (λ α → select (recurse▹ α eₛ ρ) (List.map alt alts))
        where
          alt : Con × List Var × Exp → Con × (List (Σ (τ v) is-look) → τ v)
          alt (k , xs , eᵣ) = (k , (λ ds → step case2 (λ α → recurse▹ α eᵣ (ρ [ xs ↦* ds ]))))
