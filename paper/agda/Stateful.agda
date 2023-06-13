{-# OPTIONS --cubical --guarded #-}
module Stateful where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality

-- The Domain

Dom : Set
data S∞ : Set
data Val : Set

{-# NO_POSITIVITY_CHECK #-}
data LDom : Set where 
  ldom : (▹ Dom) -> LDom

Heap = Addr -> LDom

early-ldom : LDom -> Set
early-ldom ld = ∃[ d ] ld ≡ ldom (next d)

-- I'd rather have this invariant attached to the Heap directly instead 
-- of postulated, e.g.,
-- > Heap = Σ (Addr -> LDom) (λ μ -> ∀ {a : Addr} -> early-ldom (μ a))
-- *Very* annoyingly though, this trips up the positivity checker. 
-- It is easy to see though that this invariant holds in both
-- sites where we extend the heap. 
postulate early-heap : ∀ (μ : Heap) (a : Addr) -> early-ldom (μ a)

data Ctrl : Set where
  eval : Exp -> Ctrl  -- syntactic expression
  retn : Val -> Ctrl  -- semantic  value

S = Ctrl × Heap 

data S∞ where
  ok : S -> S∞
  stuck : S -> S∞
  _::_ : S -> ▹ S∞ -> S∞
infixr 20 _::_ 

Dom = Heap -> S∞

data Val where
  fun : (▹ Dom -> ▹ Dom) -> Val
  con : Con -> List (▹ Dom) -> Val

-- Domain combinators

_>>β=_ : S∞ -> (S -> Maybe (▹ S∞)) -> S∞ 
τ >>β= f = fix go τ
  where
    go : ▹ (S∞ -> S∞) -> S∞ -> S∞
    go recurse▹ (σ :: τ▹) = σ :: recurse▹ ⊛ τ▹
    go recurse▹ (ok σ) with f σ
    ... | just τ▹ = σ :: τ▹
    ... | nothing  = stuck σ
    go recurse▹ (stuck σ) = stuck σ

ret : Val -> Dom
ret v μ = ok (retn v , μ)

deref : Addr -> Dom
deref a μ with early-heap μ a
... | ( d , _ ) = d μ >>β= aux
  where
    aux : S -> Maybe (▹ S∞)
    aux (retn v , μ) = just (next (ok (retn v , λ a' -> if a ≡ᵇ a' then ldom (next (ret v)) else μ a')))
        -- NB: postulated invariant early-heap is satisfied here!
        -- > μ a = ldom (next (ret v))
    aux _            = nothing
    
apply : S∞ -> Dom -> S∞
apply τ d = τ >>β= aux 
  where
    aux : S -> Maybe (▹ S∞)
    aux (retn (fun f), μ) = just (f (next d) ⊛ next μ)
    aux _                 = nothing
    
select : S∞ -> (Con -> List (▹ Dom) -> Maybe (▹ Dom)) -> S∞
select dₑ f = dₑ >>β= aux
  where
    aux : S -> Maybe (▹ S∞)
    aux (retn (con K d▹s), μ) with f K d▹s
    ... | just d▹ = just (λ κ -> d▹ κ μ)
    ... | nothing = nothing
    aux _         = nothing
    
postulate alloc : Heap -> Addr

-- Helpers I'd rather not need

_[_↦_] : (Var -> Maybe Dom) -> Var -> Dom -> (Var -> Maybe Dom)
_[_↦_] ρ x d y = if x == y then just d else ρ y

_[_↦*_] : (Var -> Maybe Dom) -> List Var -> List (▹ Dom) -> ▹ (Var -> Maybe Dom)
_[_↦*_] ρ xs d▹s = aux (Data.List.zip xs d▹s)
  where
    aux : List (Var × ▹ Dom) -> ▹ (Var -> Maybe Dom)
    aux []               κ y = ρ y
    aux ((x , d▹) ∷ xs) κ y = if x == y then just (d▹ κ) else aux xs κ y

-- And finally the semantics

sem : Exp -> (Var -> Maybe Dom) -> Dom
sem = fix sem'
  where
    sem' : ▹(Exp -> (Var -> Maybe Dom) -> Dom) -> Exp -> (Var -> Maybe Dom) -> Dom 
    sem' recurse▹ e@(ref x) ρ μ with ρ x
    ... | nothing = stuck (eval e , μ)
    ... | just d  = (eval e , μ) :: next (d μ)
    sem' recurse▹ (lam x e) ρ = ret (fun (λ d▹ κ -> recurse▹ κ e (ρ [ x ↦ d▹ κ ])))
    sem' recurse▹ (app e x) ρ μ with ρ x 
    ... | nothing = stuck (eval (app e x), μ)
    ... | just dₓ = let dₑ▹ = recurse▹ ⊛ next e ⊛ next ρ ⊛ next μ in
                    (eval (app e x), μ) :: next apply ⊛ dₑ▹ ⊛ next dₓ
    sem' recurse▹ e@(let' x e₁ e₂) ρ μ =
      let a = alloc μ in
      let ρ' = ρ [ x ↦ deref a ]  in
      let d₁▹ = recurse▹ ⊛ next e₁ ⊛ next ρ' in
      let d₂▹ = recurse▹ ⊛ next e₂ ⊛ next ρ' in
      let μ'▹ κ a' = if a ≡ᵇ a' then ldom (next (d₁▹ κ)) else μ a' in
      (eval e , μ) :: d₂▹ ⊛ μ'▹ 
        -- NB: postulated invariant early-heap is satisfied here! 
        -- > μ' a = ldom (next (d₁▹ κ))
    sem' recurse▹ e@(conapp K xs) ρ = 
      let ds▹ = Data.List.map (λ x κ -> recurse▹ κ (ref x) ρ) xs in
      ret (con K ds▹)
    sem' recurse▹ e@(case' eₛ alts) ρ μ = 
      let dₛ▹ = recurse▹ ⊛ next eₛ ⊛ next ρ in
      (eval e , μ) :: λ κ -> select (dₛ▹ κ μ) f
        where
          f : Con -> List (▹ Dom) -> Maybe (▹ Dom)
          f K d▹s with findAlt K alts
          ... | nothing = nothing
          ... | just (xs , rhs) = 
            let ρ' = ρ [ xs ↦* d▹s ] in
            just (λ κ -> recurse▹ κ rhs (ρ' κ))