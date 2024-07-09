{-# OPTIONS --cubical --guarded --rewriting #-}

-- | Definitions and instances for T, Value, D, ByName, ByNeed
-- and corresponding instantiations of the interpreter
module Concrete where

open import Later
open import Syntax
open import Data.Nat
open import Data.String
open import Data.List as List
open import Data.List.Membership.Propositional
open import Data.Maybe hiding (_>>=_)
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (T; _∧_; _∨_)
open import Function
open import PartialFunction
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Relation.Nullary.Base
open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
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

Value : (Set → Set) → Set
D : (Set → Set) → Set

-- This type characterises elements in the environment.
-- Crucially, it hides the occurrence of D under a ▸,
-- so that Value below can be defined by guarded recursion.
--
-- This would not be possible if we were simply using `Σ D is-env`.
-- The latter would require an instance of `Trace (D T)` to state the *type*
-- of `fun-V`, leading to a circular definition.
data EnvD (D : ▹ Set) : Set where
  stepLook : Var → ▸ D → EnvD D

-- Fortunately, the two types are isomorphic:

toSubtype : ∀ {D} {{_ : Trace D}} → EnvD (next D) → Σ D is-env
toSubtype {{_}} (stepLook x d▹) = (step (look x) d▹ , x , d▹ , refl)

fromSubtype : ∀ {D} {{_ : Trace D}} → Σ D is-env → EnvD (next D)
fromSubtype {{_}} (_ , x , d▹ , _) = stepLook x d▹

env-iso : ∀ {D} {{_ : Trace D}} → Iso (EnvD (next D)) (Σ D is-env)
env-iso = iso toSubtype fromSubtype from-to to-from
  where
    from-to : ∀ d → toSubtype (fromSubtype d) ≡ d
    from-to (d , x , d▹ , prf) i = (prf (~ i) , x , d▹ , λ i₁ → prf (i₁ ∨ (~ i)))
    to-from : ∀ d → fromSubtype (toSubtype d) ≡ d
    to-from (stepLook x d▹) = refl

-- For the definition of ValueF, we need to turn off the positivity checker
-- because of the recursive occurrence as an argument to parameter τ.
-- If we were to monomorphise for T, we would not need this pragma.
-- It has nothing to do with the use of the later modality and guarded
-- recursion; we could perhaps have picked a different encoding of D and Value,
-- but we decided to stay true to the encoding in the paper.
{-# NO_POSITIVITY_CHECK #-}
data ValueF (τ : Set → Set) (d⁻ : ▹ Set) : Set where
  stuck-V : ValueF τ d⁻
  fun-V : (EnvD d⁻ → (D τ)) → ValueF τ d⁻
  con-V : Con → List (EnvD d⁻) → ValueF τ d⁻

Value τ = ValueF τ (dfix (τ ∘ ValueF τ))
D τ = τ (Value τ)

-- Sanity check:
_ : ∀ {τ} → D τ ≡ fix (τ ∘ ValueF τ)
_ = refl

-- The following equality is useful to unroll one layer of `Σ (D τ) is-env`.
EnvD≡is-env : ∀ τ → {{_ : Trace (D τ)}} → EnvD (dfix (τ ∘ ValueF τ)) ≡ Σ (D τ) is-env
EnvD≡is-env τ = roll ∙ subty
  where
    roll : EnvD (dfix (τ ∘ ValueF τ)) ≡ EnvD (next (D τ))
    roll i = EnvD (pfix (τ ∘ ValueF τ) i)
    subty : EnvD (next (D τ)) ≡ Σ (D τ) is-env
    subty = isoToPath (env-iso {D τ})

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

fun-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
             → (Σ (D τ) is-env → D τ) → D τ
fun-Value {τ} f = return (fun-V (f ∘ transport (EnvD≡is-env τ)))

apply-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
               → D τ → Σ (D τ) is-env → D τ
apply-Value {τ} dv da = dv >>= aux
  where
    aux : Value τ → D τ
    aux (fun-V f) = f (transport⁻ (EnvD≡is-env τ) da)
    aux _          = stuck-Value

con-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
             → Con → List (Σ (D τ) is-env) → D τ
con-Value {τ} K ds = return (con-V K (List.map (transport⁻ (EnvD≡is-env τ)) ds))

select-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
                → D τ → List (Con × (List (Σ (D τ) is-env) → D τ)) → D τ
select-Value {τ} dv alts = dv >>= aux alts
  where
    aux : List (Con × (List (Σ (D τ) is-env) → D τ)) → Value τ → D τ
    aux ((K' , alt) ∷ alts) (con-V K ds) with decEq-ℕ K K'
    ... | yes _ = alt (List.map (transport (EnvD≡is-env τ)) ds)
    ... | no _  = aux alts (con-V K ds)
    aux _ _ = stuck-Value

instance
  domain-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → Domain (D τ) is-env
  domain-Value = record {  stuck = stuck-Value;
                           fun = fun-Value;  apply = apply-Value;
                           con = con-Value;  select = select-Value }

record ByName (τ : Set → Set) (v : Set) : Set where
  constructor mkByName
  field get : τ v

instance
  monad-ByName : ∀ {τ} {{_ : Monad τ}} → Monad (ByName τ)
  monad-ByName =
    record {  return = mkByName ∘ return;
              _>>=_ = λ m k → mkByName (ByName.get m >>= (ByName.get ∘ k)) }

instance
  trace-ByName :  ∀ {τ} {{_ : ∀ {V} → Trace (τ V)}} {V} → Trace (ByName τ V)
  trace-ByName =
    record { step = λ e τ → mkByName (step e (λ α → ByName.get (τ α))) }

instance
  has-bind-ByName :  ∀ {τ} {v} → HasBind (ByName τ v)
  has-bind-ByName {τ} =
    record { bind = λ rhs body → body (λ α → fix (λ rhs▹ → rhs α rhs▹)) }

eval-by-name : Exp → D (ByName T)
eval-by-name e = 𝒮⟦ e ⟧ empty-pfun

-- For ByNeed, we need addresses and heaps.
-- The following provides a very naïve axiomatisation that is suitable to prove
-- totality of the resulting definitions:

Addr : Set
Addr = ℕ

record ByNeed (τ : Set → Set) (v : Set) : Set

Heap : ▹ Set → Set
Heap D = Addr ⇀ ▸ D
postulate nextFree : ∀ {D} → Heap D → Addr
postulate well-addressed : ∀ {D} (μ : Heap D) (a : Addr) → ∃[ d ] (μ a ≡ just d)
-- Note that `fst (well-addressed μ a)` simply returns the heap entry in `μ`
-- at address `a`, which must be present by our assumption of well-addressedness.

-- Since the heap again relies on guarded recursion, we need to introduce
-- another signature functor with associated equalities:

ByNeedF : (Set → Set) → ▹ Set → Set → Set
ByNeedF τ d⁻ v = Heap d⁻ → τ (v × Heap d⁻)

record ByNeed τ v where
  constructor mkByNeed
  field get : ByNeedF τ (dfix (D ∘ ByNeedF τ)) v

≡-ByNeed : ∀ τ v → ByNeed τ v ≡ ByNeedF τ (dfix (D ∘ ByNeedF τ)) v
≡-ByNeed _ _ = isoToPath (iso ByNeed.get mkByNeed (λ _ → refl) (λ _ → refl))

≡-HeapD : ∀ τ → dfix (D ∘ ByNeedF τ) ≡ next (D (ByNeed τ))
≡-HeapD τ = pfix (D ∘ ByNeedF τ) ∙ (λ i → next (D (λ v → sym (≡-ByNeed τ v) i)))

≡-▸HeapD : ∀ τ → ▸ dfix (D ∘ ByNeedF τ) ≡ ▹ D (ByNeed τ)
≡-▸HeapD τ i = ▸ ≡-HeapD τ i

≡-DByNeed : ∀ τ → D (ByNeed τ) ≡ ByNeedF τ (next (D (ByNeed τ))) (Value (ByNeed τ))
≡-DByNeed τ = ≡-ByNeed τ (Value (ByNeed τ)) ∙ (λ i → ByNeedF τ (≡-HeapD τ i) (Value (ByNeed τ)))

return-ByNeed : ∀ {τ} {{_ : Monad τ}} {v} → v → ByNeed τ v
return-ByNeed v = mkByNeed (λ μ → return (v , μ))

_>>=-ByNeed_ :  ∀ {τ} {{_ : Monad τ}} {a} {b}
                → ByNeed τ a → (a → ByNeed τ b) → ByNeed τ b
_>>=-ByNeed_ {τ} {a} {b} m k = mkByNeed (λ μ → ByNeed.get m μ >>= aux)
  where
    aux : (a × Heap (dfix (D ∘ ByNeedF τ))) → τ (b × Heap (dfix (D ∘ ByNeedF τ)))
    aux (a , μ') = ByNeed.get (k a) μ'

instance
  monad-ByNeed : ∀ {τ} {{_ : Monad τ}} → Monad (ByNeed τ)
  monad-ByNeed = record { return = return-ByNeed; _>>=_ = _>>=-ByNeed_ }

step-ByNeed :  ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}}
               → Event → ▹(ByNeed τ v) → ByNeed τ v
step-ByNeed {τ} {v} e m = mkByNeed (λ μ → step e (λ α → ByNeed.get (m α) μ))

instance
  trace-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Trace (ByNeed τ v)
  trace-ByNeed = record { step = step-ByNeed  }

-- The following definition constructs the total Agda equivalent of the Haskell expression
-- `step (Look x) (fetch a)`, for the given variable `x` and address `a`.
-- Ultimately, all denotations in the interpreter environment `ρ` will take this
-- form under by-need evaluation.
-- In fact, *all* uses of `fetch` will take this form!
stepLookFetch :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
                 → Var → Addr → D (ByNeed τ)
stepLookFetch {τ} x a = mkByNeed (λ μ →
  let d▹ = fst (well-addressed μ a) in
  step (look x) (λ α → ByNeed.get (transport (≡-▸HeapD τ) d▹ α) μ))

fetch : ∀ {τ} {{_ : Monad τ}} → Addr → ▹(D (ByNeed τ))

-- It is evident that `stepLookFetch x a` is the same as `step (look x) (fetch a)`:
same-thing :  ∀ {τ x a} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
              → step (look x) (fetch {τ} a) ≡ stepLookFetch x a

-- Unfortunately, it is hard to decompose `stepLookFetch` into
-- separate function calls to `step` and `fetch`,
-- because the latter will then need to bind the tick variable `α`
-- before the heap `μ`.
-- This is in contrast to the order of binders in `stepLookFetch`,
-- which may bind `μ` before `α`, because look steps leave the heap unchanged.
--
-- Hence we currently need the following postulate in order to define fetch:

postulate
  flip-tick       : ∀ {A B : Set} → (A → ▹ B) → ▹ (A → B)
  flip-tick-beta  :  ∀ {A B : Set} {f : A → ▹ B} {μ : A} {@tick α : Tick}
                     → flip-tick f α μ ≣ f μ α
{-# REWRITE flip-tick-beta #-}

-- We think that rule `flip-tick` and its rewrite rule look rather benign
-- for its only use site in `fetch`. Note that the rewrite rule cannot even
-- fire when α flows into μ due to the order of quantification!

fetch {τ} a = map▹ mkByNeed (flip-tick (λ μ →
  let d▹ = fst (well-addressed μ a) in
  (λ α → ByNeed.get (transport (≡-▸HeapD τ) d▹ α) μ)))

-- (Note that `flip-tick-beta` is automatically applied in the following proof.)
same-thing = refl

memo :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
        → Addr → ▹(D (ByNeed τ)) → ▹(D (ByNeed τ))
memo {τ} a d▹ = fix memo' d▹
  where
    memo' : ▹(▹(D (ByNeed τ)) → ▹(D (ByNeed τ)))
          →   ▹(D (ByNeed τ)) → ▹(D (ByNeed τ))
    memo' rec▹ d▹ α₁ = do
      v ← d▹ α₁
      step update (λ _α₂ → mkByNeed (λ μ →
        return (v , μ [ a ↦ transport⁻ (≡-▸HeapD τ) (rec▹ α₁ (λ _ → return v)) ])))

bind-ByNeed :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
               → ▹  (▹(D (ByNeed τ)) → D (ByNeed τ))
               →    (▹(D (ByNeed τ)) → D (ByNeed τ))
               →    D (ByNeed τ)
bind-ByNeed {τ} rhs body = do
  a ← mkByNeed (λ μ → return (nextFree μ , μ))
  mkByNeed (λ μ →
    return (tt , μ [ a ↦ transport⁻ (≡-▸HeapD τ) (memo a (λ α → rhs α (fetch a))) ]))
  step let1 (λ _α → body (fetch a))

instance
  has-bind-ByNeed  : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
                   → HasBind (D (ByNeed τ))
  has-bind-ByNeed = record { bind = bind-ByNeed }

eval-by-need : Exp → T (Value (ByNeed T) × Heap (next (D (ByNeed T))))
eval-by-need e = transport (≡-DByNeed T) (𝒮⟦ e ⟧ empty-pfun) empty-pfun

exp1 : Exp
exp1 = let' 0 (app (lam 1 (lam 2 (ref 2))) 0) (app (ref 0) 0)
-- A translation of `let i = (λy.λx.x) i in i i`

res1 = eval-by-need exp1
