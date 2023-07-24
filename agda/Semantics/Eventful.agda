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
Heap n = ∀ {m} → {n ℕ.≤ m} → Addr m → LDom m

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
  ret : Val n → Heap n → Trc n -- NB: ret : Val → Dom
  stuck : Trc n
  _::_ : ∀ {m} → ▹ (Act n m) → ▹ Trc m → Trc n
infixr 20 _::_ 

Dom n = Heap n → Trc n

data Val n where
  fun : (∀ {m} → {n ℕ.≤ m} → Addr m → Dom m) → Val n
  con : Con → List (Addr n) → Val n

-- Domain combinators

ι-≤′ : ∀ {n m} → n ℕ.≤′ m → Addr n → Addr m
ι-≤′ ℕ.≤′-refl     a = a
ι-≤′ (ℕ.≤′-step x) a = ι (ι-≤′ x a)

ι-≤ : ∀ {n m} → n ℕ.≤ m → Addr n → Addr m
ι-≤ p a = ι-≤′ (ℕ.≤⇒≤′ p) a

ι-Val : ∀ {n m} → n ℕ.≤ m → Val n → Val m
ι-Val n≤m (fun f) = fun (λ {k} {m≤k} a → f {k} {ℕ.≤-trans n≤m m≤k} a)
ι-Val n≤m (con K xas) = con K (L.map (ι-≤ n≤m) xas)

ι-Heap : ∀ {n m} → n ℕ.≤ m → Heap m → Heap n
ι-Heap n≤m μ {k} {n≤k} = μ {k} {_}

ι-Dom : ∀ {n m} → n ℕ.≤ m → Dom n → Dom m
ι-Dom n≤m d μ = d (ι-Heap n≤m μ)

ι-LDom : ∀ {n m} → n ℕ.≤ m → LDom n → LDom m
ι-LDom x = {!   !}

ι-Env : ∀ {n m} → n ℕ.≤ m → (Var ⇀ Addr n) → (Var ⇀ Addr m)
ι-Env x = {!   !}

ι-Trc : ∀ {n m} → n ℕ.≤ m → Trc n → Trc m
ι-Trc x = {!   !}

ι-Act : ∀ {n₁ m₁ n₂} → n₁ ℕ.≤ m₁ → Act n₁ n₂ → Σ[ m₂ ∈ ℕ ] (n₂ ℕ.≤ m₂ × Act n₂ m₂)
ι-Act x = {!   !}

update : ∀ {n} → Heap n → Addr n → Dom n → Heap n
update μ a d a' with decAddr a a' 
... | yes _ = ldom (next d) 
... | no _  = μ a'

extend : ∀ {n} → Heap n → Dom (suc n) → Heap (suc n)
extend {n} μ d a' with decAddr a' (fresh n) 
... | yes _ = ldom (next d) 
... | no np = ι-LDom _ (μ (down a' np))

_>>β=_ : ∀ {n} → Dom n → (∀ {m} → {n ℕ.≤ m} → Val m ⇀ Dom m) → Dom n
_>>β=_ {n} d f μ = fix go n (d μ)
  where
    go : ▹ (∀ m → {n ℕ.≤ m} → Trc m → Trc m) → ∀ m → {n ℕ.≤ m} → Trc m → Trc m
    go recurse▹ m (a▹ :: τ▹) = a▹ :: (λ α → recurse▹ α _ (τ▹ α))
    go recurse▹ m {p} (ret v μ) with f {m} {p} v
    ... | just d  = d μ
    ... | nothing = stuck
    go _ _ _ = stuck

_::>_ : ∀ {n} → ▹ (Act n n) → ▹ (Dom n) → Dom n
(a▹ ::> d▹) μ = a▹ :: d▹ ⊛ next μ
infixr 20 _::>_ 

memo : ∀ {n} → Addr n → Dom n → Dom n
memo {n} a d = d >>β= aux
  where
    aux : ∀ {m} → {n ℕ.≤ m} → Val m ⇀ Dom m
    aux {_} {p} v = 
      let a' = ι-≤ p a in
      just (λ μ → next (upd a' v) :: next (ret v (update μ a' (ret v))))

apply : ∀ {n} → Dom n → Addr n → Dom n
apply {n} dₑ a = dₑ >>β= aux 
  where
    aux : ∀ {m} → {n ℕ.≤ m} → Val m ⇀ Dom m 
    aux {_} {p} (fun f) = just (f (ι-≤ p a))
    aux         _       = nothing
    
select : ∀ {n} → Dom n → (∀ {m} → {n ℕ.≤ m} → Con → List (Addr m) ⇀ Dom m) → Dom n
select {n} dₑ f = dₑ >>β= aux 
  where
    aux : ∀ {m} → {n ℕ.≤ m} → Val m ⇀ Dom m
    aux (con K as) = f K as
    aux _          = nothing
    
-- And finally the semantics

sem : ∀ {n} → Exp → (Var ⇀ Addr n) → Dom n
sem {n} = fix sem' n
  where
    sem' : ▹(∀ m → {n ℕ.≤ m} → Exp → (Var ⇀ Addr m) → Dom m) → ∀ m → {n ℕ.≤ m} → Exp → (Var ⇀ Addr m) → Dom m
    sem' recurse▹ m (ref x) ρ μ with ρ x
    ... | nothing = stuck
    ... | just a  = next (look a) :: (λ α → LDom.thed (μ a) α μ)
    sem' recurse▹ m (lam x e) ρ = 
      ret (fun (λ {k} {p} a → next (app2 x a) ::> (λ α → recurse▹ α k e (ι-Env p ρ [ x ↦ a ]))))
    sem' recurse▹ m (app e x) ρ with ρ x 
    ... | nothing = λ _ → stuck 
    ... | just a  = let dₑ▹ = λ α → recurse▹ α n e ρ in
                    next (app1 a) ::> (λ α → apply (dₑ▹ α) a)
    sem' recurse▹ m {p} (let' x e₁ e₂) ρ μ =
      let a = fresh m in
      let ρ' = ι-Env {m} {suc m} _ ρ [ x ↦ a ] in
      let d₁▹ = λ α → recurse▹ α (suc m) e₁ ρ' in
      let d₂▹ = λ α → recurse▹ α (suc m) e₂ ρ' in
      (λ α → bind x a (d₁▹ α)) :: (λ α → d₂▹ α (extend μ (d₁▹ α)))
    sem' recurse▹ m (conapp K xs) ρ μ with pmap ρ xs
    ... | nothing = stuck
    ... | just as = ret (con K as) μ
    sem' recurse▹ m (case' eₛ alts) ρ = 
      let dₛ▹ = λ α → recurse▹ α m eₛ ρ in
      (λ α → case1 (dₛ▹ α)) ::> (λ α → select (dₛ▹ α) f)
        where
          f : ∀ {k} → {m ℕ.≤ k} → Con → List (Addr k) ⇀ Dom k
          f {k} {p} K as with findAlt K alts
          ... | nothing         =  nothing
          ... | just (xs , rhs) = 
            just (next (case2 K (L.zip xs as)) ::> (λ α → recurse▹ α k rhs (ι-Env p ρ [ xs ↦* as ])))