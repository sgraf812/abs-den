{-# OPTIONS --cubical --guarded --rewriting #-}

-- | Definitions and instances for T, Value, D, ByName, ByNeed
module Concrete where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List as List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (T)
open import Function
open import PartialFunction
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Relation.Nullary.Base
open import Semantics

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A} {B} → M A → (A → M B) → M B
  _>>_ : ∀ {A} {B} → M A → M B → M B
  l >> r = l >>= (λ _ → r)

open Monad {{...}} public

data T (A : Set) : Set where
  ret-T : A → T A
  step-T : Event → ▹ T A → T A

data Value (τ : Set → Set) : Set

{-# NO_POSITIVITY_CHECK #-}
  -- This pragma is only necessary because of a bug in Agda.
  -- (We cannot link to the issue without risking deanonymisation.)
  -- Its purpose is to hide the dependency on Value from the
  -- totality checker; doing so is fine because it occurs
  -- under a Later.
data LookupD (D : Set) : Set where
  stepLookup : Var → ▹ D → LookupD D
  -- An LookupD is effectively a subtype of D.
  -- Think of `stepLookup x d' : LookupD` as a `d : D`
  -- such that `d = step (lookup x) d'`.
  -- We simply have no type safe way to say the latter,
  -- hence this weird encoding.
  -- Here is the corresponding bijection:

toSubtype : ∀ {D} {{_ : Trace D}} → LookupD D → Σ D is-look
toSubtype {{_}} (stepLookup x d▹) = (step (lookup x) d▹ , x , d▹ , refl)

fromSubtype : ∀ {D} {{_ : Trace D}} → Σ D is-look → LookupD D
fromSubtype {{_}} (_ , x , d▹ , _) = stepLookup x d▹

-- The concrete D
D : (Set → Set) → Set
D τ = τ (Value τ)

data Value T where
  stuck-V : Value T
  fun-V : (LookupD (D T) → D T) → Value T
  con-V : Con → List (LookupD (D T)) → Value T

return-T : ∀ {A} → A → T A
return-T = ret-T

_>>=-T_ : ∀ {A} {B} → T A → (A → T B) → T B
ret-T a >>=-T k = k a
step-T e τ >>=-T k = step-T e (λ α → τ α >>=-T k)

instance
  monad-T : Monad T
  monad-T = record { return = ret-T; _>>=_ = _>>=-T_ }

instance
  trace-T : ∀ {V} → Trace (T V)
  trace-T = record { step = step-T }

stuck-Value : ∀ {τ} {{_ : Monad τ}} → D τ
stuck-Value = return stuck-V

fun-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → (Σ (D τ) is-look → D τ) → D τ
fun-Value f = return (fun-V (f ∘ toSubtype))

apply-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → D τ → Σ (D τ) is-look → D τ
apply-Value {τ} dv da = dv >>= aux
  where
    aux : Value τ → D τ
    aux (fun-V f) = f (fromSubtype da)
    aux _         = stuck-Value

con-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → Con → List (Σ (D τ) is-look) → D τ
con-Value K ds = return (con-V K (List.map fromSubtype ds))

select-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → D τ → List (Con × (List (Σ (D τ) is-look) → D τ)) → D τ
select-Value {τ} dv alts = dv >>= aux alts
  where
    aux : List (Con × (List (Σ (D τ) is-look) → D τ)) → Value τ → D τ
    aux ((K' , alt) ∷ alts) (con-V K ds) with decEq-ℕ K K'
    ... | yes _ = alt (List.map toSubtype ds)
    ... | no _  = aux alts (con-V K ds)
    aux _ _ = stuck-Value

instance
  domain-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → Domain (D τ) is-look
  domain-Value = record { stuck = stuck-Value; fun = fun-Value; apply = apply-Value; con = con-Value; select = select-Value }

record ByName (τ : Set → Set) (v : Set) : Set where
  constructor mkByName
  field get : τ v

instance
  monad-ByName : ∀ {τ} {{_ : Monad τ}} → Monad (ByName τ)
  monad-ByName = record { return = mkByName ∘ return; _>>=_ = λ m k → mkByName (ByName.get m >>= (ByName.get ∘ k)) }

instance
  trace-ByName : ∀ {τ} {{_ : ∀ {V} → Trace (τ V)}} {V} → Trace (ByName τ V)
  trace-ByName = record { step = λ e τ → mkByName (step e (λ α → ByName.get (τ α))) }

instance
  has-bind-ByName : ∀ {τ} {v} → HasBind (ByName τ v)
  has-bind-ByName {τ} = record { bind = λ rhs body → body (λ α → fix (λ rhs▹ → rhs α rhs▹)) }

eval-by-name : Exp → D (ByName T)
eval-by-name e = S⟦ e ⟧ empty-pfun

Addr : Set
Addr = ℕ

record ByNeed (τ : Set → Set) (v : Set) : Set

{-# NO_POSITIVITY_CHECK #-}
  -- This pragma is only necessary because of a bug in Agda.
  -- (We cannot link to the issue without risking deanonymisation.)
  -- Its purpose is to hide the dependency on Value from the
  -- totality checker; doing so is fine because it occurs
  -- under a Later.
data HeapD (τ : Set → Set) : Set where
  heapD : ▹(D τ) → HeapD τ

Heap : (Set → Set) → Set
Heap τ = Addr ⇀ HeapD τ
postulate nextFree : ∀ {τ} → Heap τ → Addr
postulate well-addressed : ∀ {τ} (μ : Heap τ) (a : Addr) → ∃[ d ] (μ a ≡ just d)

record ByNeed τ v where
  constructor mkByNeed
  field get : Heap (ByNeed τ) → τ (v × Heap (ByNeed τ))

return-ByNeed : ∀ {τ} {{_ : Monad τ}} {v} → v → ByNeed τ v
return-ByNeed v = mkByNeed (λ μ → return (v , μ))

_>>=-ByNeed_ : ∀ {τ} {{_ : Monad τ}} {a} {b} → ByNeed τ a → (a → ByNeed τ b) → ByNeed τ b
_>>=-ByNeed_ {τ} {a} {b} m k = mkByNeed (λ μ → ByNeed.get m μ >>= aux)
  where
    aux : (a × Heap (ByNeed τ)) → τ (b × Heap (ByNeed τ))
    aux (a , μ') = ByNeed.get (k a) μ'

instance
  monad-ByNeed : ∀ {τ} {{_ : Monad τ}} → Monad (ByNeed τ)
  monad-ByNeed = record { return = return-ByNeed; _>>=_ = _>>=-ByNeed_ }

step-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Event → ▹(ByNeed τ v) → ByNeed τ v
step-ByNeed {τ} {v} e m = mkByNeed (λ μ → step e (λ α → ByNeed.get (m α) μ))
  -- NB: If we were able to switch the order of λ μ and λ α this code would still compile
  --     and we would not need the postulate no-α-in-μ.
  --     Alas, we are stuck with the current encoding because of the abstractions involved:
  --     We can't push the λ α into the surrounding ByNeed.

instance
  trace-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Trace (ByNeed τ v)
  trace-ByNeed = record { step = step-ByNeed  }

-- | See step-ByNeed why this postulate is OK.
postulate no-α-in-μ : ∀ {τ} (f : Heap (ByNeed τ) → ▹(τ (Value (ByNeed τ) × Heap (ByNeed τ))))
                    → Σ (▹(D (ByNeed τ)))
                         (λ d▹ → ∀ μ (@tick α : Tick) → ByNeed.get (d▹ α) μ ≡ f μ α)

fetch : ∀ {τ} {{_ : Monad τ}} → Addr → ▹(D (ByNeed τ))
fetch {τ} a = fst (no-α-in-μ (λ μ → aux μ (fst (well-addressed μ a))))
  where
    aux : Heap (ByNeed τ) → HeapD (ByNeed τ) → ▹(τ (Value (ByNeed τ) × Heap (ByNeed τ)))
    aux μ (heapD d▹) α = ByNeed.get (d▹ α) μ

memo : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → Addr → ▹(D (ByNeed τ)) → ▹(D (ByNeed τ))
memo {τ} a d▹ = fix memo' d▹
  where
    memo' : ▹(▹(D (ByNeed τ)) → ▹(D (ByNeed τ)))
          →   ▹(D (ByNeed τ)) → ▹(D (ByNeed τ))
    memo' rec▹ d▹ α₁ = do
      v ← d▹ α₁
      step update (λ _α₂ → mkByNeed (λ μ → return (v , μ [ a ↦ heapD (rec▹ α₁ (λ _ → return v)) ])))

bind-ByNeed : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → ▹(▹(D (ByNeed τ)) → D (ByNeed τ)) → (▹(D (ByNeed τ)) → D (ByNeed τ)) → D (ByNeed τ)
bind-ByNeed {τ} rhs body = do
  a ← mkByNeed (λ μ → return (nextFree μ , μ))
  mkByNeed (λ μ → return (42 , μ [ a ↦ heapD (memo a (λ α → rhs α (fetch a))) ]))
  step let1 (λ _α → body (fetch a))

instance
  has-bind-ByNeed : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → HasBind (D (ByNeed τ))
  has-bind-ByNeed = record { bind = bind-ByNeed }

eval-by-need : Exp → T (Value (ByNeed T) × Heap (ByNeed T))
eval-by-need e = ByNeed.get (S⟦ e ⟧ empty-pfun) empty-pfun
