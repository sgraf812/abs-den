{-# OPTIONS --cubical --guarded #-}
module Usage where

open import Later
open import Syntax
open import Stateless
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

data EnumerableMultiSet : Set -> Set₁ where
  empty : ∀{A : Set} -> EnumerableMultiSet A
  yield : ∀{A : Set} -> A -> ▹ EnumerableMultiSet A -> EnumerableMultiSet A
  skip : ∀{A : Set} -> ▹ EnumerableMultiSet A -> EnumerableMultiSet A

enumLook : T∞ -> EnumerableMultiSet Addr
enumLook (ok _)    = empty
enumLook stuck     = empty
enumLook (a :: τ▹) = skip (λ α -> aux (a α) (enumLook (τ▹ α)))
  where
    aux : Act -> EnumerableMultiSet Addr -> EnumerableMultiSet Addr
    aux (look a) s = yield a (next s) 
    aux _        s = s

-- remove : ∀{A : Set} {eq? : Dec (A -> A -> EnumerableMultiSet A -> EnumerableMultiSet A

-- subseteq : ∀{A : Set} -> EnumerableMultiSet A -> EnumerableMultiSet A -> Set 
-- subseteq  