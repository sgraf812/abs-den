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
open import Cubical.Induction.WellFounded

module Theory.Forcing (as : Addrs) where
open Addrs as
import Semantics.Eventful
open module Sem = Semantics.Eventful as

module ℕ-WellFounded = WFI (ℕ.<-wellfounded)

-- ≤∧≢⇒< : ∀ {m n} → m ℕ.≤ n → ¬ m ≡ n → m ℕ.< n
-- ≤∧≢⇒< {m} {n} (zero , m≡n) m≢n = ⊥.elim (m≢n m≡n)
-- ≤∧≢⇒< {m} {n} (suc k , 1+k+m≡n) m≢n = {!   !}
-- -- ≤∧≢⇒< {_} {zero}  m       m≢n     = m≢n refl
-- -- ≤∧≢⇒< {_} {suc n} z≤n       m≢n     = ℕ.zero-≤
-- -- ≤∧≢⇒< {_} {suc n} (s≤s m≤n) 1+m≢1+n =
-- --   ℕ.suc-≤ (≤∧≢⇒< m≤n (1+m≢1+n ∘ cong suc))
-- 
unwrap! : ∀ {n} → LDom n → GDom n
unwrap! {n} ld = LDom.thed ld unsafe⋄
-- 
-- Heap-measure : ∀{n} → Heap n → ℕ
-- Heap-measure μ = ?
-- 
-- less-forced-at : ∀ {n} → Addr n → Heap n → Heap n → Set 
-- less-forced-at {n} a μ₁ μ₂ = 
--   Σ[ v ∈ Val n ] (¬ unwrap! (μ₁ a) ≡ memo a (gret v)) × (unwrap! (μ₂ a) ≡ memo a (gret v))
-- 
-- data Termination (n : ℕ) (μ₁ μ₂ : Heap n) : List (Addr n) → Set where
--   base : Termination n μ₁ μ₂ enum
--   onemore : ∀ {as} → (a : Addr n) → (less-forced-at a μ₁ μ₂) → Termination n μ₁ μ₂ as → Termination n μ₁ μ₂ (a ∷ as)
-- 
-- _≤-Heap_ : ∀ {n} → Heap n → Heap n → Set 
-- _≤-Heap_ {n} μ₁ μ₂ = 
--   ∀ (a : Addr n) (v : Val n) (_ : unwrap! (μ₁ a) ≡ memo a (gret v)) →
--     unwrap! (μ₂ a) ≡ memo a (gret v)
-- 
-- _<-Heap_ : ∀ {n} → Heap n → Heap n → Set 
-- _<-Heap_ {n} μ₁ μ₂ = 
--     (μ₁ ≤-Heap μ₂ )
--   × (Σ[ a ∈ Addr n ] Σ[ v ∈ Val n ] 
--     ((unwrap! (μ₂ a) ≡ memo a (gret v)) × (¬ unwrap! (μ₁ a) ≡ memo a (gret v))))
-- 
-- Heap-zero : Heap 0
-- Heap-zero a = ⊥.rec (¬Addr0 a)
-- 
-- isProp-Heap-zero : isProp (Heap 0)
-- isProp-Heap-zero = {!   !}
-- 
-- ¬-<-Heap-zero : ∀ {μ} → ¬ μ <-Heap Heap-zero
-- ¬-<-Heap-zero {μ} (_ , a , _) = ⊥.elim (¬Addr0 a)
-- 
-- -- private
--   -- acc-suc : Acc _<_ n → Acc _<_ (suc n)
--   -- acc-suc a
--     -- = acc λ y y<sn
--     -- → case <-split y<sn of λ
--     -- { (inl y<n) → access a y y<n
--     -- ; (inr y≡n) → subst _ (sym y≡n) a
--     -- }
-- -- 
-- <-Heap-wellfounded : ∀ {n} → WellFounded (_<-Heap_ {n})
-- <-Heap-wellfounded {zero} μ = acc λ μ' μ'<μ → ⊥.rec (¬-<-Heap-zero (transport (cong (λ μ → μ' <-Heap μ) (isProp-Heap-zero μ Heap-zero)) μ'<μ))
-- <-Heap-wellfounded
-- -- <-Heap-wellfounded zero = acc λ _ → ⊥.rec ∘ ¬-<-zero
-- -- <-Heap-wellfounded (suc n) = acc-suc (<-wellfounded n)

data Blub : ∀ {n m} → Addr n → Heap n → Heap m → Set 

forces-to : ∀ n m → Heap n → Heap m → Set
forces-to k n μ₁ μ₂ = ∀ a → Blub a μ₁ μ₂

data Blub where
  bleh : ∀ {n m a μ₁ μ₂} 
       → (n≤m : n ℕ.≤ m)
       → (ι-LDom n≤m (μ₁ a) ≡ μ₂ (ι-≤ n≤m a)) 
       ---------------------------------------
       → Blub {n} {m} a μ₁ μ₂
  bleu : ∀ {n n' m a μ₁ μ₁' μ₂ v} 
       → (n≤m : n ℕ.≤ m)
       → (n'≤m : n' ℕ.≤ m)
       → (step : unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁')
       → let aₘ = ι-≤ n≤m a in
          (same-val : unwrap! (μ₂ aₘ) ≡ memo aₘ (gret (ι-Val n'≤m v)))
       → forces-to n' m μ₁' μ₂ 
       → Blub {n} {m} a μ₁ μ₂


-- forces-entry-strict : ∀ k n → Heap n → Addr n → Heap (k ℕ.+ n) → Set
-- forces-entry-strict zero n μ₁ a μ₂ =  
--   Σ[ v ∈ Val n ] 
--   Σ[ μ₁' ∈ Heap n ] 
--   Σ[ step ∈ (unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁') ] 
--   unwrap! (μ₂ a) ≡ memo a (gret (ι-Val (zero , refl) v))
-- forces-entry-strict = ℕ-WellFounded.induction λ k ind-< n μ₁ a μ₂ → 
--   let n≤m = (k , refl) in
--   let aₘ = ι-≤ n≤m a in
--   Σ[ k' ∈ ℕ ] 
--   Σ[ k'≤k ∈ k' ℕ.≤ k ] 
--   Σ[ v ∈ Val (k' ℕ.+ n) ]
--   Σ[ μ₁' ∈ Heap (k' ℕ.+ n) ] 
--   Σ[ step ∈ (unwrap! (μ₁ a) , μ₁ ⇓ v , μ₁') ] 
--     (unwrap! (μ₂ aₘ) ≡ memo aₘ (gret (ι-Val (ℕ.≤-+k k'≤k) v)))
--   × (∀ (k'≢0 : ¬ k' ≡ 0) → 
--       let k-k' = k ℕ.∸ k' in
--       let k-k'<k = {!   !} in -- ≤∧≢⇒< k'≤k k'≢k in
--       let k-k' = fst k'≤k in
--       let k-k'+k'+n≡k+n = {!   !} in
--       ind-< k-k' k-k'<k (k' ℕ.+ n) μ₁' (ι-≤ (k' , refl) a) (transport (cong Heap k-k'+k'+n≡k+n) μ₂) )
-- 
-- forces-to k n μ₁ μ₂ = ((a : Addr n) → 
--   let n≤m = (k , refl) in
--   (ι-LDom n≤m (μ₁ a)) ≡ μ₂ (ι-≤ n≤m a) ⊎ forces-entry-strict k n μ₁ a μ₂)

_↝_ : ∀ {n m} → Heap n → Heap m → Set
_↝_ {n} {m} μ₁ μ₂ = forces-to n m μ₁ μ₂

