\subsection*{Guarded Cubical Agda Prelude}
The following module is copied from the
``example''%
\footnote{https://github.com/agda/agda/blob/master/test/Succeed/LaterPrims.agda}
linked from the Agda user's guide on Guarded Cubical.%
\footnote{\url{https://agda.readthedocs.io/en/v2.6.2.2/language/guarded-cubical.html}}
It can be considered part of the builtins or ``runtime system'' of Guarded
Cubical Agda; I had no part in defining it.

\hfuzz=2em
\begin{code}
{-# OPTIONS --guarded --cubical --rewriting #-}
module Later where

open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

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
▹_ A = (@tick x : Tick) -> A  -- NB: x not free in A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x -- NB: x occurs in A

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)
infixr 21 _⊛_

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

postulate
  dfix : ∀ {l} {A : Set l} → (f : ▹ A → A) → I → ▹ A
  dfix-beta : ∀ {l} {A : Set l} → (f : ▹ A → A) → dfix f i1 ≣ next (f (dfix f i0))

{-# REWRITE dfix-beta #-}

pfix : ∀ {l} {A : Set l} → (f : ▹ A → A) → dfix f i0 ≡ next (f (dfix f i0))
pfix f i = dfix f i

abstract
  fix : ∀ {l} {A : Set l} → (f : ▹ A → A) → A
  fix f = f (pfix f i0)

  fix-eq : ∀ {l} {A : Set l} → (f : ▹ A → A) → fix f ≡ f (next (fix f))
  fix-eq f = cong f (pfix f)

later-ext : ∀ {A : ▹ Set} → {f g : ▸ A} → (▸ \ a → f a ≡ g a) → f ≡ g
later-ext eq i a = eq a i

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = transp (\ i → A i a) i0 (u0 a)

hcompLater :  ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A))
              → (u0 : ▸ A [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 a = hcomp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)
\end{code}
