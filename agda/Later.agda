{-# OPTIONS --guarded --cubical #-}
-- | The following module is copied from the ``example'' at
-- https://github.com/agda/agda/blob/1c449e23b/test/Succeed/LaterPrims.agda
-- linked from the Agda user's guide on Guarded Cubical.
-- It can be considered part of the builtins or ``runtime system'' of Guarded
-- Cubical Agda; we had no part in defining it.
module Later where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Agda.Primitive.Cubical

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)
infixr 21 _⊛_

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = primTransp (\ i → A i a) i0 (u0 a)

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)
