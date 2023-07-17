{-# OPTIONS --cubical --guarded #-}
module Semantics.Vanilla where

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

data Trc : Set where
  ret : Val -> Heap -> Trc -- NB: ret : Val -> Dom
  stuck : Trc
  later : ▹ Trc -> Trc

data Val where
  fun : (Addr -> LDom) -> Val
  con : Con -> List Addr -> Val

Dom = Heap -> Trc

-- Domain combinators

update : Heap -> Addr -> Dom -> Heap
update μ a d a' = if a ≡ᵇ a' then ldom (next d) else μ a'

_>>β=_ : Dom -> (Val -> Maybe Dom) -> Dom
(d >>β= f) μ = fix go (d μ)
  where
    go : ▹ (Trc -> Trc) -> Trc -> Trc
    go recurse▹ (later τ▹) = later (recurse▹ ⊛ τ▹)
    go recurse▹ (ret v μ) with f v
    ... | just d  = d μ
    ... | nothing = stuck
    go _ _ = stuck

laterD : ▹ Dom -> Dom
laterD d▹ μ = later (d▹ ⊛ next μ)

memo : Addr -> Dom -> Dom
memo a d = d >>β= aux
  where
    aux : Val -> Maybe Dom
    aux v = just (λ μ -> later (next (ret v (update μ a (ret v)))))

apply : Dom -> Addr -> Dom
apply dₑ a = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (fun f) = just (laterD (LDom.thed (f a)))
    aux _       = nothing
    
select : Dom -> (Con -> List Addr -> Maybe Dom) -> Dom
select dₑ f = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (con K as) = f K as 
    aux _          = nothing
    
postulate alloc : Heap -> Addr

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
    ... | just a  = later (λ α -> LDom.thed (μ a) α μ)
    sem' recurse▹ (lam x e) ρ = ret (fun (λ a -> ldom (λ α -> recurse▹ α e (ρ [ x ↦ a ]))))
    sem' recurse▹ (app e x) ρ μ with ρ x
    ... | nothing = stuck
    ... | just a  = later (λ α -> apply (recurse▹ α e ρ) a μ)
    sem' recurse▹ (let' x e₁ e₂) ρ μ =
      let a = alloc μ in
      let ρ' = ρ [ x ↦ a ] in
      later (λ α -> recurse▹ α e₂ ρ' (update μ a (recurse▹ α e₁ ρ')))
    sem' recurse▹ (conapp K xs) ρ μ with traverseMaybe ρ xs
    ... | nothing = stuck
    ... | just as = ret (con K as) μ
    sem' recurse▹ (case' eₛ alts) ρ μ =
      later (λ α -> select (recurse▹ α eₛ ρ) f μ)
        where
          f : Con -> List Addr -> Maybe Dom
          f K as with findAlt K alts
          ... | nothing         = nothing
          ... | just (xs , rhs) =
            just (λ μ -> later (λ α -> recurse▹ α rhs (ρ [ xs ↦* as ]) μ))
 