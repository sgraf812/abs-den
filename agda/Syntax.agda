{-# OPTIONS --cubical #-}
module Syntax where

open import Data.Nat
open import Data.String
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Bool

Var = String
Addr = ℕ
Con = ℕ
data Exp : Set where
  ref : Var -> Exp
  lam : Var -> Exp -> Exp
  app : Exp -> Var -> Exp
  let' : Var -> Exp -> Exp -> Exp
  conapp : Con -> List Var -> Exp
  case' : Exp -> List (Con × List Var × Exp) -> Exp

findAlt : Con -> List (Con × List Var × Exp) -> Maybe (List Var × Exp)
findAlt _ [] = nothing
findAlt K ((K' , vs , rhs) ∷ xs) = if K ≡ᵇ K' then just (vs , rhs) else findAlt K xs

  