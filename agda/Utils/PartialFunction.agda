{-# OPTIONS --cubical --guarded #-}
module Utils.PartialFunction where

open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Relation.Nullary.Base
open import Data.Maybe
open import Data.List 
open import Data.Product

_⇀_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ⇀ B = A → Maybe B
infix 1 _⇀_

_[_↦_] : ∀{A B : Set} {{dec : {x y : A} → Dec (x ≡ y)}} → (A ⇀ B) → A → B → (A ⇀ B)
_[_↦_] {{dec}} ρ x b y with dec {x} {y}
... | yes _ = just b
... | no  _ = ρ y

_[_↦*_] : ∀{A B : Set} {{dec : {x y : A} → Dec (x ≡ y)}} → (A ⇀ B) → List A → List B → (A ⇀ B)
_[_↦*_] {A} {B} {{dec}} ρ xs as = aux (Data.List.zip xs as)
  where
    aux : List (A × B) → (A ⇀ B)
    aux []             y = ρ y
    aux ((x , b) ∷ xs) y with dec {x} {y}
    ... | yes _ = just b
    ... | no  _ = aux xs y

pmap : ∀ {A B : Set} → (A ⇀ B) → List A ⇀ List B
pmap f [] = just []
pmap {_} {B} f (a ∷ as) with f a 
... | nothing = nothing
... | just b  = aux b (pmap f as)
  where
    aux : B → Maybe (List B) → Maybe (List B)
    aux b nothing = nothing
    aux b (just bs) = just (b ∷ bs)

