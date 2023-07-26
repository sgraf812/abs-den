{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.List as L
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude using (_≡_)

module Theory.Forcing (as : Addrs) where
open Addrs as
import Semantics.Eventful
open module Sem = Semantics.Eventful as

_∼[_]↝_ : ∀ {n m} → {n ℕ.≤ m} → Heap n → Addr n → Heap m → Set
_∼[_]↝_ {n} {m} {n≤m} μ₁ a μ₂ = 
  let aₘ = ι-≤ n≤m a in
  let unwrap! = λ {n} (ld : LDom n) → LDom.thed ld unsafe⋄ in
  Σ[ n' ∈ ℕ ] Σ[ n'≤m ∈ n' ℕ.≤ m ] Σ[ v ∈ Val n' ] Σ[ μ₁' ∈ Heap n' ] ((unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁') × (unwrap! (μ₂ aₘ) ≡ memo aₘ (gret (ι-Val n'≤m v))))

_↝_ : ∀ {n m} → Heap n → Heap m → Set
_↝_ {n} {m} μ₁ μ₂ = Σ[ n≤m ∈ n ℕ.≤ m ] ((a : Addr n) → 
    (ι-LDom n≤m (μ₁ a)) ≡ μ₂ (ι-≤ n≤m a)
  ⊎ μ₁ ∼[ a ]↝ μ₂)
