{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Properties as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Empty as ⊥
open import Cubical.Data.List.Properties as L
open import Cubical.Data.List as L
open import Data.Maybe
open import Cubical.Data.Prod
open import Data.Sum
open import Function
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude hiding (_[_↦_])

module Theory.Forcing (as : Addrs) where
open Addrs as
import Semantics.Eventful
open module Sem = Semantics.Eventful as

variable 
  n m : ℕ
  μ₁ : Heap n
  μ₂ : Heap m

unwrap! : LDom n → GDom n
unwrap! ld = LDom.thed ld unsafe⋄

infix 25 _at_
_at_  : Heap n → Addr n → GDom n
μ at a = unwrap! (μ a)

data ForcesPoint (μ₂ : Heap m) : Addr n → Heap n → Set 

-- Definition 18
_↝_ : Heap n → Heap m → Set
_↝_ μ₁ μ₂ = ∀ a → ForcesPoint μ₂ a μ₁

data ForcesPoint {m} μ₂ where
  equal : ∀ {n a μ₁} 
       → (n≤m : n ℕ.≤ m)
       → (ι-LDom n≤m (μ₁ a) ≡ μ₂ (ι-≤ n≤m a)) 
       ---------------------------------------
       → ForcesPoint  {m} μ₂ {n} a μ₁
  forces-one : ∀ {n n' a μ₁ μ₁' v} 
       → (n≤m : n ℕ.≤ m)
       → (n'≤m : n' ℕ.≤ m)
       → (step : μ₁ at a , μ₁ ⇓ v , μ₁')
       → let aₘ = ι-≤ n≤m a in
          (same-val : μ₂ at aₘ ≡ memo aₘ (gret (ι-Val n'≤m v)))
       → μ₁' ↝ μ₂ 
       → ForcesPoint {m} μ₂ {n} a μ₁

↝-≤ : ∀ {n m} {μ₁ : Heap n} {μ₂ : Heap m} → μ₁ ↝ μ₂ → n ℕ.≤ m
↝-≤ {zero} _ = ℕ.zero-≤
↝-≤ {suc n} f with f (fresh n)
... | equal n≤m _       = n≤m
... | forces-one n≤m _ _ _ _ = n≤m

-- Lemma 19
↝-val-idem : 
  ∀ {a v} 
  → (frc : μ₁ ↝ μ₂)
  → μ₁ at a ≡ memo a (gret v)
  → let n≤m = ↝-≤ frc in
     let aₘ = ι-≤ n≤m a in
     μ₂ at aₘ ≡ memo aₘ (gret (ι-Val n≤m v))
↝-val-idem {μ₁ = μ₁} {μ₂ = μ₂} {a} {v} frc is-val with frc a 
... | equal n≤m₂ a≡aₘ₂ = 
  let n≤m = ↝-≤ frc in
  let n≤m≡n≤m₂ = ℕ.m≤n-isProp n≤m n≤m₂ in
  let aₘ = ι-≤ n≤m a in
  let aₘ₂ = ι-≤ n≤m₂ a in
    μ₂ at aₘ
  ≡⟨ refl ⟩
    unwrap! (μ₂ aₘ)
  ≡⟨ cong (λ n≤m → unwrap! (μ₂ (ι-≤ n≤m a))) n≤m≡n≤m₂ ⟩
    unwrap! (μ₂ aₘ₂)
  ≡⟨ cong unwrap! (sym a≡aₘ₂) ⟩
    unwrap! (ι-LDom n≤m₂ (μ₁ a))
  ≡⟨ cong (λ n≤m → unwrap! (ι-LDom n≤m (μ₁ a))) (sym n≤m≡n≤m₂) ⟩
    unwrap! (ι-LDom n≤m (μ₁ a))
  ≡⟨ refl ⟩
    ι-GDom n≤m (μ₁ at a)
  ≡⟨ cong (ι-GDom n≤m) is-val ⟩
    ι-GDom n≤m (memo a (gret v))
  ≡⟨ {!   !} ⟩
    memo aₘ (gret (ι-Val n≤m v))
  ∎
-- (cong unwrap! a≡aₘ)
... | forces-one _ _ _ _ _ = {!   !}

 