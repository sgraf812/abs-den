{-# OPTIONS --cubical --guarded #-}
module Semantics where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool

Var = String
Addr = ℕ
Con = ℕ
data Expr : Set where
  Ref : Var -> Expr
  Lam : Var -> Expr -> Expr
  App : Expr -> Var -> Expr
  Let : Var -> Expr -> Expr -> Expr

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹ A = (@tick x : Tick) -> A

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)
infixl 21 _⊛_ 

Dom : Set
data T∞ : Set
data Val : Set

data Act : Set where
  bind : Var -> Addr -> Dom -> Act
  look : Addr -> Act
  upd : Addr -> Dom -> Act
  app1 : Dom -> Act
  app2 : Var -> Dom -> Act
  --case1 : Dom -> Act
  --case2 : Con -> List (Var, Dom) -> Act

T* = List Act

{-# NO_POSITIVITY_CHECK #-}
data T∞ where
  ok : Val -> T∞
  div : T∞
  _::_ : ▹ Act -> ▹ T∞ -> T∞

Dom = T* -> T∞

data Val where
  fun : (Dom -> Dom) -> Val
  --cons : Con -> (List (List ▹ Dom)) -> Val

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

_>>β=_ : Dom -> (Val -> Maybe Dom) -> Dom
(d >>β= f) ι = fix go [] (d ι)
  where
    go : ▹ (T* -> T∞ -> T∞) -> T* -> T∞ -> T∞
    go recurse▹ ι2 (a▹ :: τ▹) = a▹ :: ((recurse▹ ⊛ ((next _∷_ ⊛ a▹) ⊛ next ι2)) ⊛ τ▹)
    go recurse▹ ι2 (ok v) with f v
    ... | just d  = d (ι Data.List.++ reverse ι2)
    ... | nothing = div
    go _ _ _ = div

_::>_ : ▹ Act -> ▹ Dom -> Dom
(a▹ ::> d▹) ι = a▹ :: (d▹ ⊛ ((next _∷_ ⊛ a▹) ⊛ next ι))

ret : Val -> Dom
ret v i = ok v

postulate well-addressed : ∀ (ι : T*) (a : Addr) -> (∃[ d ] upd a d ∈ ι) ⊎ (∃[ x ] ∃[ d ] bind x a d ∈ ι)

μ : T* -> Addr -> Dom
μ ι a with well-addressed ι a
...  | inj₁ (d , _prf)       = d
...  | inj₂ (_x , d , _prf) = d
    
deref : (a : Addr) -> Dom
deref a ι = (next (look a) ::> next (μ ι a >>β= λ v -> just (next (upd a (ret v)) ::> next (ret v)))) ι

apply : Dom -> Dom -> Dom
apply dₑ dₓ = dₑ >>β= aux 
  where
    aux : Val -> Maybe Dom
    aux (fun f) = just (f dₓ)
    -- aux (cons _ _)       = nothing

-- select : Dom -> (List (List Dom -> Maybe Dom)) -> Dom
-- select dₛ fs = dₑ >>β= aux 
--   where
--     aux : Val -> Maybe Dom
--     aux (cons k field_mappings) = just ... fs ...
--     aux (fun _)                 = nothing

data Fresh : (Addr -> Dom) -> Set where
  _#_ : Addr -> (μ : Addr -> Dom) -> Fresh μ

postulate alloc : ∀ (μ : Addr -> Dom) -> Fresh μ

sem : Expr -> (Var -> Maybe Dom) -> Dom
sem = fix sem'
  where
    sem' : ▹(Expr -> (Var -> Maybe Dom) -> Dom) -> Expr -> (Var -> Maybe Dom) -> Dom 
    sem' recurse▹ (Ref x) ρ with ρ x
    ... | just d  = d
    ... | nothing = λ _ -> div
    sem' recurse▹ (Lam x e) ρ = ret (fun (λ d -> next (app2 x d) ::> recurse▹ ⊛ next e ⊛ next (λ y -> if x == y then just d else ρ y))) 
    sem' recurse▹ (App e x) ρ with ρ x 
    ... | just d  = next (app1 d) ::> next apply ⊛ (recurse▹ ⊛ next e ⊛ next ρ) ⊛ next d
    ... | nothing = λ _ -> div 
    sem' recurse▹ (Let x e₁ e₂) ρ ι with alloc (μ ι) 
    ... | a # _ = let ρ' y = if x == y then just (deref a) else ρ y in
                  (next (bind x a) ⊛ (recurse▹ ⊛ next e₁ ⊛ next ρ') ::> recurse▹ ⊛ next e₂ ⊛ next ρ') ι