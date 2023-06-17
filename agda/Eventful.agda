{-# OPTIONS --cubical --guarded #-}
module Eventful where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool

-- The Domain

Dom : Set

{-# NO_POSITIVITY_CHECK #-}
data LDom : Set where 
  ldom : (▹ Dom) -> LDom

Heap = Addr -> LDom

data Val : Set

data Act : Set where
  bind : Var -> Addr -> Dom -> Act
  look : Addr -> Act
  upd : Addr -> Val -> Act
  app1 : Dom -> Act
  app2 : Var -> Dom -> Act
  case1 : Dom -> Act
  case2 : Con -> List (Var × Dom) -> Act

{-# NO_POSITIVITY_CHECK #-}
data T∞ : Set where
  ret : Val -> Heap -> T∞ -- NB: ret : Val -> Dom
  stuck : T∞
  _::_ : ▹ Act -> ▹ T∞ -> T∞
infixr 20 _::_ 

Dom = Heap -> T∞

data Val where
  fun : (▹ Dom -> Dom) -> Val
  con : Con -> List (▹ Dom) -> Val

-- Domain combinators

update : Heap -> Addr -> Dom -> Heap
update μ a d a' = if a ≡ᵇ a' then ldom (next d) else μ a'

lookup : Heap -> Addr -> ▹ Dom
lookup μ a with μ a
... | ldom d▹ = d▹

_>>β=_ : Dom -> (Val -> Maybe Dom) -> Dom
(d >>β= f) μ = fix go (d μ)
  where
    go : ▹ (T∞ -> T∞) -> T∞ -> T∞
    go recurse▹ (a▹ :: τ▹) = a▹ :: recurse▹ ⊛ τ▹
    go recurse▹ (ret v μ) with f v
    ... | just d  = d μ
    ... | nothing = stuck
    go _ _ = stuck

_::>_ : ▹ Act -> ▹ Dom -> Dom
(a▹ ::> d▹) μ = a▹ :: d▹ ⊛ next μ
infixr 20 _::>_ 

deref : Addr -> Dom
deref a μ = next (look a) :: (λ α -> (lookup μ a α >>β= aux) μ)
  where
    aux : Val -> Maybe Dom
    aux v = just (λ μ -> next (upd a v) :: next (ret v (update μ a (ret v))))

apply : Dom -> Dom -> Dom
apply dₑ dₓ = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (fun f) = just (f (next dₓ))
    aux _       = nothing
    
select : Dom -> (Con -> List (▹ Dom) -> Dom) -> Dom
select dₑ f = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (con K d▹s) = just (f K d▹s)
    aux _           = nothing
    
postulate alloc : Heap -> Addr

-- Helpers I'd rather not need

_[_↦_] : (Var -> Maybe Dom) -> Var -> Dom -> (Var -> Maybe Dom)
_[_↦_] ρ x d y = if x == y then just d else ρ y

_[_↦*_] : (Var -> Maybe Dom) -> List Var -> ▹ List Dom -> ▹ (Var -> Maybe Dom)
_[_↦*_] ρ xs ds▹ α = aux (Data.List.zip xs (ds▹ α))
  where
    aux : List (Var × Dom) -> (Var -> Maybe Dom)
    aux []             y = ρ y
    aux ((x , d) ∷ xs) y = if x == y then just d else aux xs y

sequence : ∀ {A : Set} → List (▹ A) -> ▹ List A
sequence [] = next []
sequence (x ∷ xs) = next _∷_ ⊛ x ⊛ sequence xs

-- And finally the semantics

sem : Exp -> (Var -> Maybe Dom) -> Dom
sem = fix sem'
  where
    sem' : ▹(Exp -> (Var -> Maybe Dom) -> Dom) -> Exp -> (Var -> Maybe Dom) -> Dom 
    sem' recurse▹ (ref x) ρ with ρ x
    ... | nothing = λ _ -> stuck
    ... | just d  = d
    sem' recurse▹ (lam x e) ρ = 
      ret (fun (λ d▹ -> (λ α -> app2 x (d▹ α)) ::> (λ α -> recurse▹ α e (ρ [ x ↦ d▹ α ]))))
    sem' recurse▹ (app e x) ρ with ρ x 
    ... | nothing = λ _ -> stuck 
    ... | just dₓ = let dₑ▹ = recurse▹ ⊛ next e ⊛ next ρ in
                    next (app1 dₓ) ::> (λ α -> apply (dₑ▹ α) dₓ)
    sem' recurse▹ (let' x e₁ e₂) ρ μ =
      let a = alloc μ in
      let ρ' = ρ [ x ↦ deref a ] in
      let d₁▹ = recurse▹ ⊛ next e₁ ⊛ next ρ' in
      let d₂▹ = recurse▹ ⊛ next e₂ ⊛ next ρ' in
      (λ α -> bind x a (d₁▹ α)) :: (λ α -> d₂▹ α (update μ a (d₁▹ α)))
    sem' recurse▹ (conapp K xs) ρ = 
      let ds▹ = Data.List.map (λ x α -> recurse▹ α (ref x) ρ) xs in
      ret (con K ds▹)
    sem' recurse▹ (case' eₛ alts) ρ = 
      let dₛ▹ = recurse▹ ⊛ next eₛ ⊛ next ρ in
      (λ α -> case1 (dₛ▹ α)) ::> (λ α -> select (dₛ▹ α) f)
        where
          f : Con -> List (▹ Dom) -> Dom
          f K d▹s with findAlt K alts
          ... | nothing =  λ _ -> stuck
          ... | just (xs , rhs) = 
            let ds▹ = sequence d▹s in
            let ρ'▹ =  ρ [ xs ↦* ds▹ ] in
            (λ α -> case2 K (Data.List.zip xs (ds▹ α))) ::> (λ α -> recurse▹ α rhs (ρ'▹ α))