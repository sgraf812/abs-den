{-# OPTIONS --cubical --guarded --rewriting #-}

open import Utils.Later
open import Utils.PartialFunction
open import Utils.Addrs
open import Syntax hiding (Val)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.String
open import Data.List as L
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Cubical.Relation.Nullary

module Semantics.Eventful (as : Addrs) where
open Addrs as

-- The Domain

Dom : ℕ → Set

{-# NO_POSITIVITY_CHECK #-}
record LDom (n : ℕ) : Set where
  inductive
  constructor ldom
  field 
    thed : ▹ (Dom n)

Heap : ℕ → Set
Heap n = Addr n → LDom n

data Val (n : ℕ) : Set

data Act (n : ℕ) : ℕ → Set where
  bind : Var → Addr (suc n) → Dom (suc n) → Act n (suc n)
  look : Addr n → Act n n
  upd : Addr n → Val n → Act n n
  app1 : Addr n → Act n n
  app2 : Var → Addr n → Act n n
  case1 : Dom n → Act n n
  case2 : Con → List (Var × Addr n) → Act n n

data Trc (n : ℕ) : Set where
  ret : Val n → Heap n → Trc n
  stuck : Trc n
  _::_ : ∀ {m} → ▹ (Act n m) → ▹ Trc m → Trc n
infixr 20 _::_ 

Dom n = ∀ {m} → n ℕ.≤ m → Heap m → Trc m

data Val n where
  fun : (∀ {m} → n ℕ.≤ m → Addr m → Dom m) → Val n
  con : Con → List (Addr n) → Val n

-- Domain combinators

ι-≤′ : ∀ {n m} → n ℕ.≤′ m → Addr n → Addr m
ι-≤′ ℕ.≤′-refl     a = a
ι-≤′ (ℕ.≤′-step x) a = ι (ι-≤′ x a)

ι-≤ : ∀ {n m} → n ℕ.≤ m → Addr n → Addr m
ι-≤ p a = ι-≤′ (ℕ.≤⇒≤′ p) a

ι-Val : ∀ {n m} → n ℕ.≤ m → Val n → Val m
ι-Val n≤m (fun f) = fun (λ {k} m≤k a → f {k} (ℕ.≤-trans n≤m m≤k) a)
ι-Val n≤m (con K xas) = con K (L.map (ι-≤ n≤m) xas)

ι-Dom : ∀ {n m} → n ℕ.≤ m → Dom n → Dom m
ι-Dom n≤m d m≤k μ = d (ℕ.≤-trans n≤m m≤k) μ

ι-LDom : ∀ {n m} → n ℕ.≤ m → LDom n → LDom m
ι-LDom n≤m ld = ldom (λ α → ι-Dom n≤m (LDom.thed ld α))

ι-Env : ∀ {n m} → n ℕ.≤ m → (Var ⇀ Addr n) → (Var ⇀ Addr m)
ι-Env x = {!   !}

ι-Trc : ∀ {n m} → n ℕ.≤ m → Trc n → Trc m
ι-Trc x = {!   !}

ι-Act : ∀ {n m} → n ℕ.≤ m → Act n n → Act n m
ι-Act x = {!   !}

update : ∀ {n} → Heap n → Addr n → Dom n → Heap n
update μ a d a' with decAddr a a' 
... | yes _ = ldom (next (λ {m} → d {m})) 
... | no _  = μ a'

extend : ∀ {n} → Heap n → Dom (suc n) → Heap (suc n)
extend {n} μ d a' with decAddr a' (fresh n) 
... | yes _ = ldom (next (λ n≤m → d n≤m)) 
... | no np = ι-LDom (ℕ.n≤1+n n) (μ (down a' np))

_>>β=_ : ∀ {n} → Dom n → (∀ {m} → n ℕ.≤ m → Val m ⇀ Dom m) → Dom n
_>>β=_ {n} d f {m} n≤m μ = fix go {m} n≤m (d n≤m μ)
  where
    go : ▹ (∀ {m} → n ℕ.≤ m → Trc m → Trc m) → ∀ {m} → n ℕ.≤ m → Trc m → Trc m
    go recurse▹ n≤m (a▹ :: τ▹) = a▹ :: (λ α → recurse▹ α _ (τ▹ α))
    go recurse▹ n≤m (ret v μ) with f n≤m v
    ... | just d  = d (ℕ.≤-reflexive _) μ
    ... | nothing = stuck
    go _ _ _ = stuck

_::>_ : ∀ {n} → ▹ (Act n n) → ▹ (Dom n) → Dom n
(a▹ ::> d▹) n≤m μ = (λ α → ? ι-Act n≤m (a▹ α)) :: (λ α → d▹ α n≤m μ)
infixr 20 _::>_ 

ret' : ∀ {n} → Val n → Dom n
ret' v n≤m μ = ret (ι-Val n≤m v) μ  

memo : ∀ {n} → Addr n → Dom n → Dom n
memo {n} a d = d >>β= aux
  where
    aux : ∀ {m} → n ℕ.≤ m → Val m ⇀ Dom m
    aux {_} n≤m v = 
      just (λ {k} m≤k μ → 
        let n≤k = ℕ.≤-trans n≤m m≤k in
        let a' = ι-≤ n≤k a in
        let v' = ι-Val m≤k v in
        next (upd a' v') :: next (ret v' (update μ a' (ret' v'))))

apply : ∀ {n} → Dom n → Addr n → Dom n
apply {n} dₑ a = dₑ >>β= aux 
  where
    aux : ∀ {m} → n ℕ.≤ m → Val m ⇀ Dom m 
    aux {_} n≤m (fun f) = just (f (ℕ.≤-reflexive _) (ι-≤ n≤m a))
    aux     _   _       = nothing
    
select : ∀ {n} → Dom n → (∀ {m} → {n ℕ.≤ m} → Con → List (Addr m) ⇀ Dom m) → Dom n
select {n} dₑ f = dₑ >>β= aux 
  where
    aux : ∀ {m} → n ℕ.≤ m → Val m ⇀ Dom m
    aux _ (con K as) = f K as
    aux _ _          = nothing
    
-- And finally the semantics

sem : ∀ {n} → Exp → (Var ⇀ Addr n) → Dom n
sem {n} = fix sem' n
  where
    sem' : ▹(∀ {n} → Exp → (Var ⇀ Addr n) → Dom n) → ∀ {n} → Exp → (Var ⇀ Addr n) → Dom n
    sem' recurse▹ (ref x) ρ n≤m μ with ρ x
    ... | nothing = stuck
    ... | just a  = next (look (ι-≤ n≤m a)) :: (λ α → LDom.thed (μ (ι-≤ n≤m a)) α (ℕ.≤-reflexive _) μ)
    sem' recurse▹ (lam x e) ρ = 
      ret' (fun (λ {k} n≤m a → next (app2 x a) ::> (λ α → recurse▹ α n≤m e n≤m (ι-Env n≤m ρ [ x ↦ a ]))))
    sem' recurse▹ (app e x) ρ n≤m μ with ρ x 
    ... | nothing = stuck 
    ... | just a  = let dₑ▹ = λ α → recurse▹ α n e ρ in
                    next (app1 a) ::> (λ α → apply (dₑ▹ α) a)
    sem' recurse▹ {m} n≤m {p} (let' x e₁ e₂) ρ μ =
      let a = fresh m in
      let ρ' = ι-Env {m} {suc m} _ ρ [ x ↦ a ] in
      let d₁▹ = λ α → recurse▹ α (suc m) e₁ ρ' in
      let d₂▹ = λ α → recurse▹ α (suc m) e₂ ρ' in
      (λ α → bind x a (d₁▹ α)) :: (λ α → d₂▹ α (extend μ (d₁▹ α)))
    sem' recurse▹ n≤m (conapp K xs) ρ μ with pmap ρ xs
    ... | nothing = stuck
    ... | just as = ret (con K as) μ
    sem' recurse▹ {m} n≤m (case' eₛ alts) ρ = 
      let dₛ▹ = λ α → recurse▹ α m eₛ ρ in
      (λ α → case1 (dₛ▹ α)) ::> (λ α → select (dₛ▹ α) f)
        where
          f : ∀ {k} → m ℕ.≤ k → Con → List (Addr k) ⇀ Dom k
          f {k} n≤m K as with findAlt K alts
          ... | nothing         =  nothing
          ... | just (xs , rhs) = 
            just (next (case2 K (L.zip xs as)) ::> (λ α → recurse▹ α k rhs (ι-Env n≤m ρ [ xs ↦* as ]))) 