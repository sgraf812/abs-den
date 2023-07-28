{-# OPTIONS --cubical #-}
module Utils.Addrs where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.List as L

record Addrs : Set₁ where
  field
    Addr : ℕ → Set
    decAddr : ∀ {n} (x y : Addr n) → Dec (x ≡ y)
    fresh : (n : ℕ) → Addr (suc n)
    ¬Addr0 : ¬ Addr 0
    down : ∀ {n} (k : Addr (suc n)) → (k ≡ fresh n → ⊥) → Addr n
--    down-inj : ∀ {n} (k k' : Addr (suc n)) → (p : k ≡ fresh n → ⊥) (p' : (k' ≡ fresh n → ⊥)) → down k p ≡ down k' p' → k ≡ k'
    ι : ∀ {n} → Addr n → Addr (suc n)
    ι-inj : ∀ {n} x y → ι {n} x ≡ ι y → x ≡ y
    enum : ∀ {n} → List (Addr n)
--    fresh-ι : ∀ {n} {v : Addr n} → ι v ≡ fresh n → ⊥
--    down-ι : ∀ {n} {v : Addr n} (¬p : ι v ≡ fresh n → ⊥) → down (ι v) ¬p ≡ v
--    ι-down : ∀ {n} {v : Addr (suc n)} (¬p : v ≡ fresh _ → ⊥) → ι (down v ¬p) ≡ v
--    enum-eq : ∀ {n} (x : P∞ (Addr n)) → enum {n} ≡ x ∪ enum {n}
--    enum-fin : ∀ {n} → FinitelyPresented (enum {n})

  open import Cubical.Data.Sum
  open import Cubical.Data.Fin
  open import Function

  -- vendored from more recent verison of cubical:

  ≤-split : ∀{m n} → m ≤ n → (m < n) ⊎ (m ≡ n)
  ≤-split p = <-split (suc-≤-suc p)

  ≤→< : ∀{m n} → m ≤ n → ¬ m ≡ n → m < n
  ≤→< p q with ≤-split p
  ... | inl r = r
  ... | inr r = Cubical.Data.Empty.rec (q r)
      
  ≤-suc-≢ : ∀{m n} → m ≤ suc n → (m ≡ suc n → ⊥ ) → m ≤ n
  ≤-suc-≢ p ¬q = pred-≤-pred (≤→< p ¬q)

  enumFin : (n : ℕ) → List (Fin n)
  enumFin zero    = []
  enumFin (suc n) = (n , suc-≤-suc ≤-refl) ∷ L.map (inject< ≤-refl) (enumFin n)

  finAddrs : Addrs
  finAddrs = record  {
    Addr = Fin ;
    decAddr = discreteFin ;
    fresh = λ n → n , suc-≤-suc ≤-refl ;
    ¬Addr0 = ¬Fin0 ;
    down = λ { (k , p) ¬fresh → (k , ≤-suc-≢  p (λ sk≡sn → ¬fresh (Fin-fst-≡ (injSuc sk≡sn)))) } ;
    ι = inject< ≤-refl ;
    ι-inj = λ x y → toℕ-injective ∘ cong toℕ ;
    enum = enumFin _
   }
