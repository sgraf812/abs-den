{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Properties as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Empty as ⊥
open import Data.List as L
open import Data.Maybe
open import Cubical.Data.Prod
open import Data.Sum
open import Function
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Induction.WellFounded

module Theory.Forcing (as : Addrs) where
open Addrs as
import Semantics.Eventful
open module Sem = Semantics.Eventful as

module ℕ-WellFounded = WFI (ℕ.<-wellfounded)

≤∧≢⇒< : ∀ {m n} → m ℕ.≤ n → ¬ m ≡ n → m ℕ.< n
≤∧≢⇒< {m} {n} (zero , m≡n) m≢n = ⊥.elim (m≢n m≡n)
≤∧≢⇒< {m} {n} (suc k , 1+k+m≡n) m≢n = {!   !}
-- ≤∧≢⇒< {_} {zero}  m       m≢n     = m≢n refl
-- ≤∧≢⇒< {_} {suc n} z≤n       m≢n     = ℕ.zero-≤
-- ≤∧≢⇒< {_} {suc n} (s≤s m≤n) 1+m≢1+n =
--   ℕ.suc-≤ (≤∧≢⇒< m≤n (1+m≢1+n ∘ cong suc))

unwrap! : ∀ {n} → LDom n → GDom n
unwrap! {n} ld = LDom.thed ld unsafe⋄

blub : ∀ {n m} → m ℕ.≤ n → ¬ m ≡ 0 → n ℕ.∸ m ℕ.< n
blub     {m = zero}  m≤n m≢0 = ⊥.elim (m≢0 refl)
blub {n} {m = suc m} m≤n _   = ℕ.≤-∸-suc m≤n (ℕ.∸-≤ n m)

forces-to : ∀ k n → Heap n → Heap (k ℕ.+ n) → Set
forces-entry-strict : ∀ k n → Heap n → Addr n → Heap (k ℕ.+ n) → Set
forces-entry-strict zero n μ₁ a μ₂ =  
  Σ[ v ∈ Val n ] 
  Σ[ μ₁' ∈ Heap n ] 
  Σ[ step ∈ (unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁') ] 
  unwrap! (μ₂ a) ≡ memo a (gret (ι-Val (zero , refl) v))
forces-entry-strict = ℕ-WellFounded.induction λ k ind-< n μ₁ a μ₂ → 
  let n≤m = (k , refl) in
  let aₘ = ι-≤ n≤m a in
  Σ[ k' ∈ ℕ ] 
  Σ[ k'≤k ∈ k' ℕ.≤ k ] 
  Σ[ v ∈ Val (k' ℕ.+ n) ]
  Σ[ μ₁' ∈ Heap (k' ℕ.+ n) ] 
  Σ[ step ∈ (unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁') ] 
    (unwrap! (μ₂ aₘ) ≡ memo aₘ (gret (ι-Val (ℕ.≤-+k k'≤k) v)))
  × (∀ (k'≢0 : ¬ k' ≡ 0) → 
      let k-k' = k ℕ.∸ k' in
      let k-k'<k = {!   !} in -- ≤∧≢⇒< k'≤k k'≢k in
      let k-k' = fst k'≤k in
      let k-k'+k'+n≡k+n = {!   !} in
      ind-< k-k' k-k'<k (k' ℕ.+ n) μ₁' (ι-≤ (k' , refl) a) (transport (cong Heap k-k'+k'+n≡k+n) μ₂) )

forces-to k n μ₁ μ₂ = ((a : Addr n) → 
  let n≤m = (k , refl) in
  (ι-LDom n≤m (μ₁ a)) ≡ μ₂ (ι-≤ n≤m a) ⊎ forces-entry-strict k n μ₁ a μ₂)

_↝_ : ∀ {n m} → Heap n → Heap m → Set
_↝_ {n} {m} μ₁ μ₂ = 
  Σ[ n≤m ∈ n ℕ.≤ m ] 
  forces-to (m ℕ.∸ n) n  μ₁ (transport (cong Heap (sym (ℕ.≤-∸-+-cancel n≤m))) μ₂)

