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

data Card : Set where
  C0 : Card
  C1 : Card
  Cω : Card


defs : T* -> Addr -> Maybe Var
defs []                   = Nothing
defs (bind x a _d ∷ as) y = if x == y then just a else defs as
defs (_ ∷ as) _           = defs as

