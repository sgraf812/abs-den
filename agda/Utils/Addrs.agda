{-# OPTIONS --cubical #-}
module Utils.Addrs where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty.Base
open import Data.Nat

record Addrs : Set₁ where
  field
    Addr : ℕ → Set
    decAddr : ∀ {n} (x y : Addr n) → Dec (x ≡ y)
    fresh : (n : ℕ) → Addr (suc n)
    down : ∀ {n} (k : Addr (suc n)) → (k ≡ fresh n → ⊥) → Addr n
    down-inj : ∀ {n} (k k' : Addr (suc n)) → (p : k ≡ fresh n → ⊥) (p' : (k' ≡ fresh n → ⊥)) → down k p ≡ down k' p' → k ≡ k'
    ι : ∀ {n} → Addr n → Addr (suc n)
    ι-inj : ∀ {n} x y → ι {n} x ≡ ι y → x ≡ y
--    enum : ∀ {n} → P∞ (Addr n)
    fresh-ι : ∀ {n} {v : Addr n} → ι v ≡ fresh n → ⊥
    down-ι : ∀ {n} {v : Addr n} (¬p : ι v ≡ fresh n → ⊥) → down (ι v) ¬p ≡ v
    ι-down : ∀ {n} {v : Addr (suc n)} (¬p : v ≡ fresh _ → ⊥) → ι (down v ¬p) ≡ v
--    enum-eq : ∀ {n} (x : P∞ (Addr n)) → enum {n} ≡ x ∪ enum {n}
--    enum-fin : ∀ {n} → FinitelyPresented (enum {n})

