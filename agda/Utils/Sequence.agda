{-# OPTIONS --cubical --guarded #-}
module Utils.Sequence where

open import Agda.Primitive
open import Utils.Later
open import Data.Nat

private variable
  l : Level

data ℕω : Set where
  Z : ℕω
  S : ▹ ℕω → ℕω

Sequence = ∀ {A : Set} → ℕω → A 

ones : Sequence ℕ
ones = fix aux
  where
    aux : (▹ Sequence ℕ -> Sequence ℕ) -> Sequence ℕ
    aux rec Z = 1
    aux rec (S ▹n) = rec ⊛ ▹n