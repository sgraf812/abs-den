{-# OPTIONS --cubical --guarded --rewriting #-}
module Semantics.Vanilla where

open import Utils.Later
open import Syntax hiding (Val)
open import Data.Nat
open import Data.String
open import Data.List as List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (T)
open import Function
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Relation.Nullary.Base

-- The Domain

data Event : Set where
  lookup : Var → Event
  update : Event
  app1 : Event
  app2 : Event
  case1 : Event
  case2 : Event
  let1 : Event

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A} {B} → M A → (A → M B) → M B

open Monad {{...}}

record Trace (T : Set → Set) : Set₁ where
  field
    {{monad}} : Monad T
    step : ∀ {V} → Event → ▹ (T V) → T V

open Trace {{...}}

record Domain (D : Set) (p : D → Set) : Set where
  field
    stuck : D
    fun : (Σ D p → D) → D
    apply : D → Σ D p → D
    con : Var → List (Σ D p) → D
    select : D → List (Var × (List (Σ D p) → D)) → D

open Domain {{...}}

record HasBind (D : Set) : Set where
  field
    bind : (▹ D → ▹ D) → (▹ D → D) → D

open HasBind {{...}}

_⇀_ : Set → Set → Set 
K ⇀ V = K → Maybe V

_[_↦_] : ∀ {A} → (Var ⇀ A) → Var → A → (Var ⇀ A)
_[_↦_] ρ x a y = if x ≡ᵇ y then just a else ρ y

_[_↦*_] : ∀ {A} → (Var ⇀ A) → List Var → List A → (Var ⇀ A)
_[_↦*_] {A} ρ xs as = aux (List.zip xs as)
  where
    aux : List (Var × A) → (Var ⇀ A)
    aux []             y = ρ y
    aux ((x , a) ∷ xs) y = if x ≡ᵇ y then just a else aux xs y

traverseMaybe : ∀ {A B : Set} → (A ⇀ B) → List A ⇀ (List B)
traverseMaybe f [] = just []
traverseMaybe {_} {B} f (a ∷ as) with f a 
... | nothing = nothing
... | just b  = aux b (traverseMaybe f as)
  where
    aux : B → Maybe (List B) ⇀ List B
    aux b nothing = nothing
    aux b (just bs) = just (b ∷ bs)

-- | This characterises the subtype of `τ v` that we pass around in `fun` and `apply`
is-look : ∀ {τ} {v} {{trc : Trace τ}} → τ v → Set
is-look d = ∃[ x ] ∃[ d▹ ] (d ≡ step (lookup x) d▹) 

S⟦_⟧_ : ∀ {τ} {v} {{trc : Trace τ}} {{domain : Domain (τ v) is-look}} {{has-bind : HasBind (τ v)}} 
      → Exp → (Var ⇀ Σ (τ v) is-look) → τ v
S⟦_⟧_ {τ} {v} {{trc}} {{domain}} {{has-bind}} e ρ = fix sem' e ρ
  where
    sem' : ▹(Exp → (Var ⇀ Σ (τ v) is-look) → τ v) → Exp → (Var ⇀ Σ (τ v) is-look) → τ v
    sem' recurse▹ (ref x) ρ with ρ x
    ... | nothing      = stuck 
    ... | just (d , _) = d
    sem' recurse▹ (lam x body) ρ = fun (λ d → step app2 (λ α → recurse▹ α body (ρ [ x ↦ d ])))
    sem' recurse▹ (app e x) ρ with ρ x
    ... | nothing = stuck
    ... | just d  = step app1 (λ α → apply (recurse▹ α e ρ) d)
    sem' recurse▹ (let' x e₁ e₂) ρ =
      bind (λ d₁ α → recurse▹ α e₁ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ])) 
                    (λ d₁ → step let1 (λ α → recurse▹ α e₂ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ])))
    sem' recurse▹ (conapp K xs) ρ with traverseMaybe ρ xs
    ... | nothing = stuck
    ... | just ds = con K ds -- lacking test that length xs matches the arity of K
    sem' recurse▹ (case' eₛ alts) ρ =
      step case1 (λ α → select (recurse▹ α eₛ ρ) (List.map alt alts))
        where
          alt : Con × List Var × Exp → Con × (List (Σ (τ v) is-look) → τ v)
          alt (k , xs , eᵣ) = (k , (λ ds → step case2 (λ α → recurse▹ α eᵣ (ρ [ xs ↦* ds ])))) 

data T (A : Set) : Set where
  ret-T : A → T A
  step-T : Event → ▹ T A → T A

data Value (τ : Set → Set) : Set

D : (Set → Set) → Set
D τ = τ (Value τ)

{-# NO_POSITIVITY_CHECK #-}
data LookupD (τ : Set → Set) : Set where
  stepLookup : Var → ▹(D τ) → LookupD τ
  -- An LookupD is effectively a subtype of D.
  -- Think of `stepLookup x d' : LookupD` as a `d : D` 
  -- such that `d = step (lookup x) d'`.
  -- We simply have no type safe way to say the latter, 
  -- hence this weird encoding. 
  -- Here is the corresponding bijection:

toSubtype : ∀ {τ} {{trc : Trace τ}} → LookupD τ → Σ (D τ) is-look 
toSubtype {{trc}} (stepLookup x d▹) = (Trace.step trc (lookup x) d▹ , x , d▹ , refl)

fromSubtype : ∀ {τ} {{trc : Trace τ}} → Σ (D τ) is-look → LookupD τ
fromSubtype {{trc}} (_ , x , d▹ , _) = stepLookup x d▹

data Value τ where 
  stuck-V : Value τ
  fun-V : (LookupD τ → D τ) → Value τ 
  con-V : Con → List (LookupD τ) → Value τ

return-T : ∀ {A} → A → T A
return-T = ret-T

_>>=-T_ : ∀ {A} {B} → T A → (A → T B) → T B
ret-T a >>=-T k = k a
step-T e τ >>=-T k = step-T e (λ α → τ α >>=-T k) 

monad-T : Monad T
monad-T = record { return = ret-T; _>>=_ = _>>=-T_ }

trace-T : Trace T
trace-T = record { step = step-T; monad = monad-T }

stuck-Value : ∀ {τ} {{trc : Trace τ}} → D τ
stuck-Value = return stuck-V

fun-Value : ∀ {τ} {{trc : Trace τ}} → (Σ (D τ) is-look → D τ) → D τ
fun-Value f = return (fun-V (f ∘ toSubtype))
    
apply-Value : ∀ {τ} {{trc : Trace τ}} → D τ → Σ (D τ) is-look → D τ
apply-Value {τ} dv da = dv >>= aux
  where 
    aux : Value τ → D τ
    aux (fun-V f) = f (fromSubtype da)
    aux _         = return stuck-V

con-Value : ∀ {τ} {{trc : Trace τ}} → Con → List (Σ (D τ) is-look) → D τ
con-Value K ds = return (con-V K (List.map fromSubtype ds))

select-Value : ∀ {τ} {{trc : Trace τ}} → D τ → List (Con × (List (Σ (D τ) is-look) → D τ)) → D τ
select-Value {τ} dv alts = dv >>= aux alts
  where 
    aux : List (Con × (List (Σ (D τ) is-look) → D τ)) → Value τ → D τ
    aux ((K' , alt) ∷ alts) (con-V K ds) with decEq-ℕ K K' 
    ... | yes _ = alt (List.map toSubtype ds)
    ... | no _  = aux alts (con-V K ds) 
    aux _ _ = stuck-Value 

domain-Value : ∀ {τ} {{trc : Trace τ}} → Domain (D τ) is-look
domain-Value = record { stuck = stuck-Value; fun = fun-Value; apply = apply-Value; con = con-Value; select = select-Value } 

record ByName (τ : Set → Set) (v : Set) : Set where
  field byName : τ v

-- monad-ByName : ∀ {τ} {{monad : Monad τ}} → Monad (ByName τ)
-- monad-ByName = record { return = (ByName ∘ return); _>>=_ = ? }

data ByNeed (τ : Set → Set) : Set where

 