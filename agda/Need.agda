{-# OPTIONS --cubical --guarded #-}
module Need where

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

-- The Domain

Dom : Set

{-# NO_POSITIVITY_CHECK #-}
data LDom : Set where
  ldom : (▹ Dom) -> LDom

Heap = Addr -> LDom

data Val : Set

data Trc : Set where
  ret : Val -> Heap -> Trc -- NB: ret : Val -> Dom
  stuck : Trc
  later : ▹ Trc -> Trc

data Val where
  fun : (Addr -> Dom) -> Val
  con : Con -> List Addr -> Val

Dom = Heap -> Trc

-- Domain combinators

upd : Heap -> Addr -> Dom -> Heap
upd μ a d a' = if a ≡ᵇ a' then ldom (next d) else μ a'

look : Heap -> Addr -> ▹ Dom
look μ a with μ a
... | ldom d▹ = d▹

_>>β=_ : Trc -> (Val -> Heap -> Maybe Trc) -> Trc
τ >>β= f = fix go τ
  where
    go : ▹ (Trc -> Trc) -> Trc -> Trc
    go recurse▹ (later τ▹) = later (recurse▹ ⊛ τ▹)
    go recurse▹ (ret v μ) with f v μ
    ... | just τ  = τ
    ... | nothing = stuck
    go _ _ = stuck

deref : (a : Addr) -> Dom
deref a μ = later (λ α -> look μ a α μ >>β= aux)
  where
    aux : Val -> Heap -> Maybe Trc
    aux v μ = just (ret v (upd μ a (ret v))) -- NB: Stateful and stateless semantics do a step here for the update transition

apply : Trc -> Dom -> Trc
apply τₑ dₓ = τₑ >>β= aux
  where
    aux : Val -> Heap -> Maybe Trc
    aux (fun f) μ = just (f (next dₓ) μ)
    aux _       _ = nothing

select : Trc -> (Con -> List (▹ Dom) -> Maybe Dom) -> Trc
select τₑ f = τₑ >>β= aux
  where
    aux : Val -> Heap -> Maybe Trc
    aux (con K d▹s) μ with f K d▹s
    ... | just d  = just (d μ)
    ... | nothing = nothing
    aux _ _       = nothing

postulate alloc : Heap -> Addr

-- Helpers I'd rather not need

_[_↦_] : (Var -> Maybe Dom) -> Var -> Dom -> (Var -> Maybe Dom)
_[_↦_] ρ x d y = if x == y then just d else ρ y

_[_↦*_] : (Var -> Maybe Dom) -> List Var -> List (▹ Dom) -> ▹ (Var -> Maybe Dom)
_[_↦*_] ρ xs d▹s = aux (Data.List.zip xs d▹s)
  where
    aux : List (Var × ▹ Dom) -> ▹ (Var -> Maybe Dom)
    aux []               α y = ρ y
    aux ((x , d▹) ∷ xs) α y = if x == y then just (d▹ α) else aux xs α y

-- And finally the semantics

sem : Exp -> (Var -> Maybe Dom) -> Dom
sem = fix sem'
  where
    sem' : ▹(Exp -> (Var -> Maybe Dom) -> Dom) -> Exp -> (Var -> Maybe Dom) -> Dom
    sem' recurse▹ (ref x) ρ with ρ x
    ... | nothing = λ _ -> stuck
    ... | just d  = d
    sem' recurse▹ (lam x e) ρ = ret (fun (λ d▹ μ -> later (λ α -> recurse▹ α e (ρ [ x ↦ d▹ α ]) μ)))
    sem' recurse▹ (app e x) ρ with ρ x
    ... | nothing = λ _ -> stuck
    ... | just dₓ = λ μ -> later (λ α -> apply (recurse▹ α e ρ μ) dₓ)
    sem' recurse▹ (let' x e₁ e₂) ρ μ =
      let a = alloc μ in
      let ρ' = ρ [ x ↦ deref a ] in
      later (λ α -> recurse▹ α e₂ ρ' (upd μ a (recurse▹ α e₁ ρ')))
    sem' recurse▹ (conapp K xs) ρ =
      let ds▹ = Data.List.map (λ x α -> recurse▹ α (ref x) ρ) xs in
      ret (con K ds▹)
    sem' recurse▹ (case' eₛ alts) ρ μ =
      later (λ α -> select (recurse▹ α eₛ ρ μ) f)
        where
          f : Con -> List (▹ Dom) -> Maybe Dom
          f K d▹s with findAlt K alts
          ... | nothing         = nothing
          ... | just (xs , rhs) =
            just (λ μ -> later (λ α -> recurse▹ α rhs ((ρ [ xs ↦* d▹s ]) α) μ))
