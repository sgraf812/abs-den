{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Properties as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Data.List as L using (List; _∷_; [])
open import Data.Maybe
open import Cubical.Data.Prod
open import Function
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude hiding (_[_↦_])

module Semantics.Eventful (as : Addrs) where
open Addrs as

-- The Domain

Dom : ℕ → Set
GDom : ℕ → Set

{-# NO_POSITIVITY_CHECK #-}
record LDom (n : ℕ) : Set where
  inductive
  constructor ldom
  field 
    thed : ▹ (GDom n)

Heap : ℕ → Set
Heap n = Addr n → LDom n

data Val (n : ℕ) : Set

data Act (n : ℕ) : ℕ → Set where
  bind : Var → Addr (suc n) → GDom (suc n) → Act n (suc n)
  look : Addr n → Act n n
  upd : Addr n → Val n → Act n n
  app1 : Addr n → Act n n
  app2 : Var → Addr n → Act n n
  case1 : GDom n → Act n n
  case2 : Con → List (Var × Addr n) → Act n n

data Trc (n : ℕ) : Set where
  ret : Val n → Heap n → Trc n
  stuck : Trc n
  _::_ : ∀ {m} → ▹ (Act n m) → ▹ Trc m → Trc n
infixr 20 _::_ 

Dom n = Heap n → Trc n
GDom n = ∀ m → n ℕ.≤ m → Dom m

data Val n where
  fun : (∀ m → n ℕ.≤ m → Addr m → Dom m) → Val n
  con : Con → List (Addr n) → Val n

-- Domain combinators
suc-≤ : ∀ {n m} → suc m ℕ.≤ n → m ℕ.≤ n
suc-≤ p = ℕ.pred-≤-pred (ℕ.≤-suc p)
 
ι-≤ : ∀ {n m} → n ℕ.≤ m → Addr n → Addr m
ι-≤ {m = m} (k , k+n≡m) a = ind k k+n≡m a
  where
    ind : ∀ {n} → (k : ℕ) → k ℕ.+ n ≡ m → Addr n → Addr m
    ind zero    n≡m     a = transport (cong Addr n≡m) a
    ind {n} (suc k) 1+k+n≡m a = ind k (ℕ.+-suc k n ∙ 1+k+n≡m) (ι a)

ι-Val : ∀ {n m} → n ℕ.≤ m → Val n → Val m
ι-Val n≤m (fun f) = fun (λ k m≤k a → f k (ℕ.≤-trans n≤m m≤k) a)
ι-Val n≤m (con K xas) = con K (L.map (ι-≤ n≤m) xas)

ι-GDom : ∀ {n m} → n ℕ.≤ m → GDom n → GDom m
ι-GDom n≤m d k m≤k μ = d k (ℕ.≤-trans n≤m m≤k) μ

ι-LDom : ∀ {n m} → n ℕ.≤ m → LDom n → LDom m
ι-LDom n≤m ld = ldom (λ α → ι-GDom n≤m (LDom.thed ld α))

ι-Env : ∀ {n m} → n ℕ.≤ m → (Var ⇀ Addr n) → (Var ⇀ Addr m)
ι-Env n≤m ρ = Data.Maybe.map (ι-≤ n≤m) ∘ ρ

≤-Act : ∀ {n m} → Act n m → n ℕ.≤ m
≤-Act {n} (bind x x₁ x₂) = ℕ.≤-+k ℕ.zero-≤
≤-Act {n} {n} (look x) = ℕ.≤-refl
≤-Act {n} (upd x x₁) = ℕ.≤-refl
≤-Act {n} (app1 x) = ℕ.≤-refl
≤-Act {n} (app2 x x₁) = ℕ.≤-refl
≤-Act {n} (case1 x) = ℕ.≤-refl
≤-Act {n} (case2 x x₁) = ℕ.≤-refl

update : ∀ {n} → Heap n → Addr n → GDom n → Heap n
update μ a d a' with decAddr a a' 
... | yes _ = ldom (next d) 
... | no _  = μ a'

extend : ∀ {n} → Heap n → GDom (suc n) → Heap (suc n)
extend {n} μ d a' with decAddr a' (fresh n) 
... | yes _ = ldom (next (λ n≤m → d n≤m)) 
... | no np = ι-LDom (ℕ.≤-+k ℕ.zero-≤) (μ (down a' np))

private
  >>β=-loop : ∀ {n} → (∀ m → n ℕ.≤ m → Val m ⇀ Dom m) 
            → ▹ (∀ {m} → n ℕ.≤ m → Trc m → Trc m) 
            → ∀ {m} → n ℕ.≤ m → Trc m → Trc m
  >>β=-loop f recurse▹ n≤m (a▹ :: τ▹) = a▹ :: (λ α → recurse▹ α (ℕ.≤-trans n≤m (≤-Act (a▹ α))) (τ▹ α))
  >>β=-loop f recurse▹ n≤m (ret v μ) with f _ n≤m v
  ... | just d  = d μ
  ... | nothing = stuck
  >>β=-loop _ _ _ _ = stuck

_>>β=_ : ∀ {n} → Dom n → (∀ m → n ℕ.≤ m → Val m ⇀ Dom m) → Dom n
_>>β=_ d f μ = fix (>>β=-loop f) ℕ.≤-refl (d μ)

gret : ∀ {n} → Val n → GDom n
gret v m n≤m μ = ret (ι-Val n≤m v) μ 

private
  memo-cont : ∀ {m} → Addr m → ∀ k → m ℕ.≤ k → Val k ⇀ Dom k
  memo-cont a k m≤k v = 
    just (λ μ → 
      let a' = ι-≤ m≤k a in
      next (upd a' v) :: next (ret v (update μ a' (gret v))))

memo : ∀ {n} → Addr n → GDom n → GDom n
memo {n} a d m n≤m = d m n≤m >>β= memo-cont (ι-≤ n≤m a)

apply : ∀ {n} → Dom n → Addr n → Dom n
apply {n} dₑ a = dₑ >>β= aux 
  where
    aux : ∀ m → n ℕ.≤ m → Val m ⇀ Dom m 
    aux _ n≤m (fun f) = just (f _ ℕ.≤-refl (ι-≤ n≤m a))
    aux _ _   _       = nothing
    
select : ∀ {n} → Dom n → (∀ m → n ℕ.≤ m → Con → List (Addr m) ⇀ Dom m) → Dom n
select {n} dₑ f = dₑ >>β= aux 
  where
    aux : ∀ m → n ℕ.≤ m → Val m ⇀ Dom m
    aux m n≤m (con K as) = f m n≤m K as
    aux _ _   _          = nothing
    
-- And finally the semantics

-- | This function captures that any semantics function
-- taking an Env and returning a Dom can be generalised 
-- to return a GDom, thus asserting that it can cope with
-- arbitrary enlarged heaps.
generalise : (∀ {n} → (Var ⇀ Addr n) → Dom n)
            → ∀ {n} → (Var ⇀ Addr n) → GDom n
generalise sem ρ _ n≤m = sem (ι-Env n≤m ρ)

Sₑ⟦_⟧ : ∀ {n} → Exp → (Var ⇀ Addr n) → GDom n
Sₑ⟦ e ⟧ ρ = generalise (fix sem' e) ρ 
  where
    sem' : ▹(∀ {n} → Exp → (Var ⇀ Addr n) → Dom n) 
           → ∀ {n} → Exp → (Var ⇀ Addr n) → Dom n
    sem' recurse▹ (ref x) ρ μ with ρ x
    ... | nothing = stuck
    ... | just a  = next (look a) :: (λ α → LDom.thed (μ a) α _ ℕ.≤-refl μ)
    sem' recurse▹ (lam x e) ρ = 
      ret (fun (λ m n≤m a μ → 
                   let ρ' = ι-Env n≤m ρ [ x ↦ a ] in
                   next (app2 x a) :: (λ α → recurse▹ α e ρ' μ)))
    sem' recurse▹ (app e x) ρ μ with ρ x 
    ... | nothing = stuck 
    ... | just a  = let dₑ▹ = λ (α : Tick) → recurse▹ α e ρ in
                    next (app1 a) :: (λ α → apply (dₑ▹ α) a μ)
    sem' recurse▹ {n} (let' x e₁ e₂) ρ μ =
      let a = fresh n in
      let ρ' = ι-Env (ℕ.≤-+k ℕ.zero-≤) ρ [ x ↦ a ] in
      let d₁▹ = λ (α : Tick) → generalise (recurse▹ α e₁) ρ' in
      let μ'▹ = λ (α : Tick) → extend μ (memo a (d₁▹ α)) in
      (λ α → bind x a (d₁▹ α)) :: (λ α → recurse▹ α e₂ ρ' (μ'▹ α))
    sem' recurse▹ (conapp K xs) ρ with pmap ρ xs
    ... | nothing = λ _ → stuck
    ... | just as = ret (con K as)
    sem' recurse▹ {n} (case' eₛ alts) ρ μ = 
      let dₛ▹ = λ (α : Tick) → generalise (recurse▹ α eₛ) ρ in
      (λ α → case1 (dₛ▹ α)) :: (λ α → select {n} (dₛ▹ α _ ℕ.≤-refl) f μ)
        where
          f : ∀ m → n ℕ.≤ m → Con → List (Addr m) ⇀ Dom m
          f _ n≤m K as with findAlt K alts
          ... | nothing         =  nothing
          ... | just (xs , rhs) = 
            let ρ' = ι-Env n≤m ρ [ xs ↦* as ] in
            just (λ μ → next (case2 K (L.zipWith (_,_) xs as)) :: (λ α → recurse▹ α rhs ρ' μ))

drop : ∀ {n} → ℕ → Trc n → Σ[ m ∈ ℕ ] ((n ℕ.≤ m) × Trc m)
drop {n} zero    τ         = n , ℕ.≤-refl , τ
drop {n} _       (ret v μ) = n , ℕ.≤-refl , ret v μ
drop {n} _       stuck     = n , ℕ.≤-refl , stuck
drop {n} (suc l) (a :: τ) with ≤-Act (a  unsafe⋄) | drop l (τ unsafe⋄)
... | n≤k | m , k≤m , τ' = m , ℕ.≤-trans n≤k k≤m , τ' 

_,_⇓_,_ : ∀ {n m} → GDom n → Heap n → Val m → Heap m → Set
_,_⇓_,_ {n} {m} d μ v μ' = Σ[ l ∈ ℕ ] Σ[ n≤m ∈ n ℕ.≤ m ] (drop l (d n ℕ.≤-refl μ) ≡ (m , n≤m , ret v μ'))

≤-Bigstep : ∀ {n m} → {d : GDom n} → {μ : Heap n} → {v : Val m} → {μ' : Heap m} → d , μ ⇓ v , μ' → n ℕ.≤ m 
≤-Bigstep (_ , n≤m , _) = n≤m 

-- module Bigstep where
--   variable
--     n m : ℕ
--   variable
--     d : GDom n
--     μ : Heap n
--     v : Val m
--     μ' : Heap m
--   ≤-Bigstep : d , μ ⇓ v , μ' → n ℕ.≤ m 
--   ≤-Bigstep (_ , n≤m , _) = n≤m 

≤-memo : ∀ {n m} {n≤m : n ℕ.≤ m} {a v} → ι-GDom n≤m (memo a (gret v)) ≡ memo (ι-≤ n≤m a) (gret (ι-Val n≤m v)) 
≤-memo {n} {m} {n≤m} {a} {v} = 
    ι-GDom n≤m (memo a (gret v))
  ≡⟨ refl ⟩
    (λ k m≤k → (memo a (gret v)) k (ℕ.≤-trans n≤m m≤k))
  ≡⟨ refl ⟩
    (λ k m≤k → (gret v) k (ℕ.≤-trans n≤m m≤k) >>β= memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a))
  ≡⟨ refl ⟩
    (λ k m≤k μ → ((λ μ' → (ret (ι-Val (ℕ.≤-trans n≤m m≤k) v) μ')) >>β= memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a)) μ)
  ≡⟨ refl ⟩
    (λ k m≤k μ → subst (fix-eq (>>β=-loop (memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a)))) ℕ.≤-refl (ret (ι-Val (ℕ.≤-trans n≤m m≤k) v) μ))
  ≡⟨ cong (λ expr → (λ k m≤k μ → fix (>>β=-loop (memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a))) ℕ.≤-refl (ret (ι-Val (ℕ.≤-trans n≤m m≤k) v) μ))) (fix-eq (>>β=-loop (memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a)))) ⟩
    {!   !}
--    (λ k m≤k μ → >>β=-loop (memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a)) (next (fix (>>β=-loop (memo-cont (ι-≤ (ℕ.≤-trans n≤m m≤k) a))))) ℕ.≤-refl (ret (ι-Val (ℕ.≤-trans n≤m m≤k) v) μ))
  ≡⟨ {!   !} ⟩
    memo (ι-≤ n≤m a) (gret (ι-Val n≤m v))  
  ∎