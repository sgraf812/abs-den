{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.String
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Function
open import Cubical.Relation.Nullary
open import Cubical.Data.Fin
open import Cubical.Data.Empty
import Semantics.Eventful as Sem
open module Eventful = Sem finAddrs

module Semantics.RunEventful where

data FinTrc (n : ℕ) : Set where
  ret : Val n → Heap n → FinTrc n
  stuck : FinTrc n
  _::_ : ∀ {m} → (Act n m) → FinTrc m → FinTrc n
  more : Trc n → FinTrc n
infixr 20 _::_ 

take : ∀ {n} → ℕ → Trc n → FinTrc n 
take zero    τ = more τ
take (suc _) (Sem.ret v μ) = ret v μ
take (suc _) Sem.stuck = stuck
take (suc l) (a Sem.:: τ) = a unsafe⋄ :: take l (τ unsafe⋄)

run : ℕ → Exp → FinTrc 0 
run n e = take n (Sₑ⟦ e ⟧ empty-pfun 0 ℕ.≤-refl (λ a → rec (¬Fin0 a)))

ex₁ : FinTrc 0
ex₁ = run 10 (let' vi (lam vx (ref vx)) (app (ref vi) vi))
