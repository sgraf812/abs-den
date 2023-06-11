{-# OPTIONS --cubical --guarded #-}
module Semantics where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Bool

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

module _ where

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

  postulate fix : ∀ {l} {A : Set l} → (▹ A → A) → A

-- End of Guarded Cubical Agda "Prelude" from https://github.com/agda/agda/blob/master/test/Succeed/LaterPrims.agda

postulate UNDEFINED : ∀ {l} {A : Set l} → A -- just for lookups that should always succeed

Var = String
Addr = ℕ
Con = ℕ
data Exp : Set where
  ref : Var -> Exp
  lam : Var -> Exp -> Exp
  app : Exp -> Var -> Exp
  let' : Var -> Exp -> Exp -> Exp
  conapp : Con -> List Var -> Exp
  case' : Exp -> List (Con × List Var × Exp) -> Exp

Dom : Set
data T∞ : Set
data Val : Set

data Act : Set where
  bind : Var -> Addr -> Dom -> Act
  look : Addr -> Act
  upd : Addr -> Dom -> Act
  app1 : Dom -> Act
  app2 : Var -> Dom -> Act
  case1 : Dom -> Act
  case2 : Con -> List (Var × Dom) -> Act

T* = List Act

{-# NO_POSITIVITY_CHECK #-}
data T∞ where
  ok : Val -> T∞
  stuck : T∞
  _::_ : ▹ Act -> ▹ T∞ -> T∞
infixr 20 _::_ 

Dom = T* -> T∞

data Val where
  fun : (▹ Dom -> Dom) -> Val
  con : Con -> List (▹ Dom) -> Val

_>>β=_ : Dom -> (Val -> Maybe Dom) -> Dom
(d >>β= f) ι = fix go [] (d ι)
  where
    go : ▹ (T* -> T∞ -> T∞) -> T* -> T∞ -> T∞
    go recurse▹ ι2 (a▹ :: τ▹) = a▹ :: recurse▹ ⊛ (next _∷_ ⊛ a▹ ⊛ next ι2) ⊛ τ▹
    go recurse▹ ι2 (ok v) with f v
    ... | just d  = d (ι Data.List.++ reverse ι2)
    ... | nothing = stuck
    go _ _ _ = stuck

_::>_ : ▹ Act -> ▹ Dom -> Dom
(a▹ ::> d▹) ι = a▹ :: d▹ ⊛ (next _∷_ ⊛ a▹ ⊛ next ι)
infixr 20 _::>_ 

ret : Val -> Dom
ret v i = ok v

postulate well-addressed : ∀ (ι : T*) (a : Addr) -> (∃[ d ] upd a d ∈ ι) ⊎ (∃[ x ] ∃[ d ] bind x a d ∈ ι)

μ : T* -> Addr -> Dom
μ ι a with well-addressed ι a
...  | inj₁ (d , _prf)       = d
...  | inj₂ (_x , d , _prf) = d
    
deref : (a : Addr) -> Dom
deref a ι = (next (look a) ::> next (μ ι a >>β= aux)) ι
  where
    aux : Val -> Maybe Dom
    aux v = just (next (upd a (ret v)) ::> next (ret v))

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
    
postulate alloc : ∀ (μ : Addr -> Dom) -> Addr

-- Helpers I'd rather not need

_[_↦_] : ∀ {B : Set} -> (Var -> Maybe B) -> Var -> B -> (Var -> Maybe B)
_[_↦_] env x b y with x == y
... | true  = just b 
... | false = env y

_[_↦*_] : ∀ {B : Set} -> (Var -> Maybe B) -> List Var -> List B -> (Var -> Maybe B)
_[_↦*_] {B} env xs bs y = aux (Data.List.zip xs bs) 
  where
    aux : List (Var × B) -> Maybe B
    aux [] = env y
    aux ((x , b) ∷ xs) = if x == y then just b else aux xs

findBy : ∀ {A : Set} → (A -> Bool) -> List A -> A
findBy p [] = UNDEFINED
findBy p (x ∷ xs) = if p x then x else findBy p xs

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
    sem' recurse▹ (lam x e) ρ = ret (fun (λ d▹ -> next (app2 x) ⊛ d▹ ::> recurse▹ ⊛ next e ⊛ (next (λ d -> ρ [ x ↦ d ]) ⊛ d▹)))
    sem' recurse▹ (app e x) ρ with ρ x 
    ... | nothing = λ _ -> stuck 
    ... | just dₓ = let dₑ▹ = recurse▹ ⊛ next e ⊛ next ρ in
                    next (app1 dₓ) ::> next apply ⊛ dₑ▹ ⊛ next dₓ
    sem' recurse▹ (let' x e₁ e₂) ρ ι =
      let a = alloc (μ ι) in
      let ρ' = ρ [ x ↦ deref a ] in
      let d₁▹ = recurse▹ ⊛ next e₁ ⊛ next ρ' in
      let d₂▹ = recurse▹ ⊛ next e₂ ⊛ next ρ' in
      (next (bind x a) ⊛ d₁▹ ::> d₂▹) ι
    sem' recurse▹ (conapp K xs) ρ = 
      let ds▹ = Data.List.map (λ x -> recurse▹ ⊛ next (ref x) ⊛ next ρ) xs in
      ret (con K ds▹)
    sem' recurse▹ (case' eₛ alts) ρ = 
      let dₛ▹ = recurse▹ ⊛ next eₛ ⊛ next ρ in
      next case1 ⊛ dₛ▹ ::> next select ⊛ dₛ▹ ⊛ next f
        where
          f : Con -> List (▹ Dom) -> Dom
          f K d▹s with findBy (λ (K' , _ , _) -> K ≡ᵇ K') alts
          ... | (_ , xs , rhs) = 
            let ds▹ = sequence d▹s in
            let ρ'▹ = next (_[_↦*_] ρ xs) ⊛ ds▹ in
            next (case2 K) ⊛ (next (Data.List.zip xs) ⊛ ds▹) ::> recurse▹ ⊛ next rhs ⊛ ρ'▹ 