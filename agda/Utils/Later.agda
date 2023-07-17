{-# OPTIONS --cubical --guarded #-}
module Utils.Later where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private variable
  l : Level
  A B : Set l

postulate Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹ A = (@tick x : Tick) -> A

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)
infixl 21 _⊛_ 

postulate fix : ∀ {l} {A : Set l} → (▹ A → A) → A
