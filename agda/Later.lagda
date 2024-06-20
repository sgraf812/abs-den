\subsection*{Guarded Cubical Agda Prelude}
The following module is copied from the
``example''%
\footnote{https://github.com/agda/agda/blob/1c449e23b/test/Succeed/LaterPrims.agda}
linked from the Agda user's guide on Guarded Cubical.%
\footnote{\url{https://agda.readthedocs.io/en/v2.6.4/language/guarded-cubical.html}}
It can be considered part of the builtins or ``runtime system'' of Guarded
Cubical Agda; I had no part in defining it.

Note the definition of the \emph{later} modality $▹$ in terms of a \emph{tick
abstraction}.
This definition can be thought of as the \AgdaDatatype{Reader Tick} monad,
only that the monad instance is impossible to define with tick abstraction
because it would lead to an unsound system.
We will however use it mostly as if $▹ A$ were just an ordinary function
returning $A$.

\hfuzz=2em
\begin{code}
{-# OPTIONS --guarded --cubical #-}
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

-- pfix' : ∀ {l} {A : Set l} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
-- pfix' f α i = pfix f i α

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)
\end{code}