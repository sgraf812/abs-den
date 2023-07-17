{-# OPTIONS --cubical --guarded #-}
module Semantics.Eventful where

open import Utils.Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool

-- The Domain

Dom : Set

{-# NO_POSITIVITY_CHECK #-}
record LDom : Set where
  inductive
  constructor ldom
  field 
    thed : ▹ Dom

Heap = Addr -> LDom

data Val : Set

data Act : Set where
  bind : Var -> Addr -> Dom -> Act
  look : Addr -> Act
  upd : Addr -> Val -> Act
  app1 : Addr -> Act
  app2 : Var -> Addr -> Act
  case1 : Dom -> Act
  case2 : Con -> List (Var × Addr) -> Act

data Trc : Set where
  ret : Val -> Heap -> Trc -- NB: ret : Val -> Dom
  stuck : Trc
  _::_ : ▹ Act -> ▹ Trc -> Trc
infixr 20 _::_ 

Dom = Heap -> Trc

data Val where
  fun : (Addr -> Dom) -> Val
  con : Con -> List Addr -> Val

-- Domain combinators

update : Heap -> Addr -> Dom -> Heap
update μ a d a' = if a ≡ᵇ a' then ldom (next d) else μ a'

_>>β=_ : Dom -> (Val -> Maybe Dom) -> Dom
(d >>β= f) μ = fix go (d μ)
  where
    go : ▹ (Trc -> Trc) -> Trc -> Trc
    go recurse▹ (a▹ :: τ▹) = a▹ :: recurse▹ ⊛ τ▹
    go recurse▹ (ret v μ) with f v
    ... | just d  = d μ
    ... | nothing = stuck
    go _ _ = stuck

_::>_ : ▹ Act -> ▹ Dom -> Dom
(a▹ ::> d▹) μ = a▹ :: d▹ ⊛ next μ
infixr 20 _::>_ 

memo : Addr -> Dom -> Dom
memo a d = d >>β= aux
  where
    aux : Val -> Maybe Dom
    aux v = just (λ μ -> next (upd a v) :: next (ret v (update μ a (ret v))))

apply : Dom -> Addr -> Dom
apply dₑ a = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (fun f) = just (f a)
    aux _       = nothing
    
select : Dom -> (Con -> List Addr -> Maybe Dom) -> Dom
select dₑ f = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (con K as) = f K as 
    aux _          = nothing
    
postulate alloc : Heap -> Addr

-- Helpers I'd rather not need

_[_↦_] : (Var -> Maybe Addr) -> Var -> Addr -> (Var -> Maybe Addr)
_[_↦_] ρ x a y = if x == y then just a else ρ y

_[_↦*_] : (Var -> Maybe Addr) -> List Var -> List Addr -> (Var -> Maybe Addr)
_[_↦*_] ρ xs as = aux (Data.List.zip xs as)
  where
    aux : List (Var × Addr) -> (Var -> Maybe Addr)
    aux []             y = ρ y
    aux ((x , a) ∷ xs) y = if x == y then just a else aux xs y

traverseMaybe : ∀ {A B : Set} -> (A -> Maybe B) -> List A -> Maybe (List B)
traverseMaybe f [] = just []
traverseMaybe {_} {B} f (a ∷ as) with f a 
... | nothing = nothing
... | just b  = aux b (traverseMaybe f as)
  where
    aux : B -> Maybe (List B) -> Maybe (List B)
    aux b nothing = nothing
    aux b (just bs) = just (b ∷ bs)

-- And finally the semantics

sem : Exp -> (Var -> Maybe Addr) -> Dom
sem = fix sem'
  where
    sem' : ▹(Exp -> (Var -> Maybe Addr) -> Dom) -> Exp -> (Var -> Maybe Addr) -> Dom 
    sem' recurse▹ (ref x) ρ μ with ρ x
    ... | nothing = stuck
    ... | just a  = next (look a) :: (λ α -> LDom.thed (μ a) α μ)
    sem' recurse▹ (lam x e) ρ = 
      ret (fun (λ a -> next (app2 x a) ::> (λ α -> recurse▹ α e (ρ [ x ↦ a ]))))
    sem' recurse▹ (app e x) ρ with ρ x 
    ... | nothing = λ _ -> stuck 
    ... | just a  = let dₑ▹ = recurse▹ ⊛ next e ⊛ next ρ in
                    next (app1 a) ::> (λ α -> apply (dₑ▹ α) a)
    sem' recurse▹ (let' x e₁ e₂) ρ μ =
      let a = alloc μ in
      let ρ' = ρ [ x ↦ a ] in
      let d₁▹ = recurse▹ ⊛ next e₁ ⊛ next ρ' in
      let d₂▹ = recurse▹ ⊛ next e₂ ⊛ next ρ' in
      (λ α -> bind x a (d₁▹ α)) :: (λ α -> d₂▹ α (update μ a (d₁▹ α)))
    sem' recurse▹ (conapp K xs) ρ μ with traverseMaybe ρ xs
    ... | nothing = stuck
    ... | just as = ret (con K as) μ
    sem' recurse▹ (case' eₛ alts) ρ = 
      let dₛ▹ = recurse▹ ⊛ next eₛ ⊛ next ρ in
      (λ α -> case1 (dₛ▹ α)) ::> (λ α -> select (dₛ▹ α) f)
        where
          f : Con -> List Addr -> Maybe Dom
          f K as with findAlt K alts
          ... | nothing         =  nothing
          ... | just (xs , rhs) = 
            just (next (case2 K (Data.List.zip xs as)) ::> (λ α -> recurse▹ α rhs (ρ [ xs ↦* as ])))