\subsection*{Concrete domain instances \AgdaDatatype{ByName}, \AgdaDatatype{ByNeed}}

Separately from the denotational interpreter, we can prove that its
instances at \AgdaDatatype{ByName} and \AgdaDatatype{ByNeed} are well-defined as
well.

In order to do so, I first need to define the concrete type \AgdaFunction{D},
which needs the concrete trace type \AgdaDatatype{T} as well as the concrete
value type \AgdaDatatype{Value}.

\begin{code}
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
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Data.Unit
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
  step-T : Event → ▸ T A → T A
\end{code}

As explained in \Cref{sec:totality-formal}, a notable difference to the
definition of \AgdaDatatype{Value} in the main body is that I need to break the
negative occurrence in \AgdaField{fun} by the use of \emph{later} $▸$.
Doing so is permitted in guarded type theory.
Unfortunately, Agda's positivity checker does not currently support
the later modality, so I have to deactivate it via a potentially
dangerous-looking pragma in the definition that follows.
Note that the use of this pragma is solely so that the positivity
checker does not try to recurse through the occurrence of $▸ D$.

\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data EnvD (D : Set) (q : ▸ D → Set) : Set where
  stepLookup : Var → (d▸ : ▸ D) → q d▸ → EnvD D q
\end{code}

I have reported this bug to the Agda maintainers.%
\footnote{\url{https://github.com/agda/agda/issues/6587}}

Note that a $\AgdaDatatype{EnvD}~D$ is effectively a subtype of $D$.
One should think of $\AgdaField{stepLookup}~x~d'$ as a $d$ such that
$d = \AgdaField{step}~(\AgdaInductiveConstructor{lookup}~x)~d'$.

Actually, I would prefer to simply \emph{say} the latter via
$\AgdaFunction{Σ}~D~\AgdaFunction{is-env}$, as in the type of \AgdaField{fun},
but there currently is no type-safe way to say that.

Defining the bijection myself is easy, enough, though:

\begin{code}
toSubtype : ∀ {D q} {{_ : Trace D}} → EnvD D q → Σ D (is-env q)
toSubtype {{_}} (stepLookup x d▸ h) = (step (lookup x) d▸ , x , d▸ , refl , h)

fromSubtype : ∀ {D q} {{_ : Trace D}} → Σ D (is-env q) → EnvD D q
fromSubtype {{_}} (_ , x , d▸ , _ , h) = stepLookup x d▸ h
\end{code}

Hence I define the data constructors \AgdaInductiveConstructor{fun-V} and
\AgdaInductiveConstructor{con-V} of \AgdaDatatype{Value} in terms of
\AgdaDatatype{EnvD} and apply the bijection when defining the
type class instance for \AgdaDatatype{Domain}.
The rest is exactly as in \Cref{sec:interp}.

\begin{code}
data Value (D : Set) (q : ▸ D → Set) : Set where
  stuck-V : Value D q
  fun-V : (EnvD D q → D) → Value D q
  con-V : Con → List (EnvD D q) → Value D q

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

roll : ∀ (τ : Set → Set) {D q} {{_ : Iso D (τ (Value D q))}} → τ (Value D q) → D
roll _ {{eq}} = Iso.inv eq

unroll : ∀ (τ : Set → Set) {D q} {{_ : Iso D (τ (Value D q))}} → D → τ (Value D q)
unroll _ {{eq}} = Iso.fun eq

stuck-Value : ∀ {τ : Set → Set} {D q} {{_ : Iso D (τ (Value D q))}} {{_ : Monad τ}} → D
stuck-Value {τ} = roll τ (return stuck-V)

fun-Value : ∀ {τ : Set → Set} {D q} {{_ : Iso D (τ (Value D q))}} {{_ : Monad τ}} {{_ : Trace D}} → (Σ D (is-env q) → D) → D
fun-Value {τ} f = roll τ (return (fun-V (f ∘ toSubtype)))

apply-Value : ∀ {τ : Set → Set} {D q} {{_ : Iso D (τ (Value D q))}} {{_ : Monad τ}} {{_ : Trace D}} → D → Σ D (is-env q) → D
apply-Value {τ} {D} {q} dv da = roll τ (unroll τ dv >>= (unroll τ ∘ aux))
  where
    aux : Value D q → D
    aux (fun-V f) = f (fromSubtype da)
    aux _         = stuck-Value

con-Value : ∀ {τ : Set → Set} {D q} {{_ : Iso D (τ (Value D q))}} {{_ : Monad τ}} {{_ : Trace D}} → Con → List (Σ D (is-env q)) → D
con-Value {τ} K ds = roll τ (return (con-V K (List.map fromSubtype ds)))

select-Value : ∀ {τ : Set → Set} {D q} {{_ : Iso D (τ (Value D q))}} {{_ : Monad τ}} {{_ : Trace D}} → D → List (Con × (List (Σ D (is-env q)) → D)) → D
select-Value {τ} {D} {q} dv alts = roll τ (unroll τ dv >>= (unroll τ ∘ aux alts))
  where
    aux : List (Con × (List (Σ D (is-env q)) → D)) → Value D q → D
    aux ((K' , alt) ∷ alts) (con-V K ds) with decEq-ℕ K K'
    ... | yes _ = alt (List.map toSubtype ds)
    ... | no _  = aux alts (con-V K ds)
    aux _ _ = stuck-Value

instance
  domain-Value : ∀ {τ D q} {{_ : Monad τ}} {{_ : Trace D}} {{_ : Iso D (τ (Value D q))}} → Domain D (is-env q)
  domain-Value = record { stuck = stuck-Value; fun = fun-Value; apply = apply-Value; con = con-Value; select = select-Value }
\end{code}

This is already enough to define the \AgdaDatatype{ByName} interpreter.
The instance of \AgdaDatatype{HasBind} is particularly interesting, because it
employs the guarded fixpoint combinator \AgdaPrimitive{fix}:

\begin{code}
record ByNameD : Set
definable-by-name : ▸ ByNameD → Set
definable-by-name _ = Unit

{-# NO_POSITIVITY_CHECK #-}
record ByNameD where
  inductive
  pattern
  constructor mkDByName
  field get : T (Value ByNameD definable-by-name)

instance
  trace-ByNameD : Trace ByNameD
  trace-ByNameD = record { step = λ e d▸ → mkDByName (step e (λ α → ByNameD.get (d▸ α))) }

instance
  roll-ByNameD : Iso ByNameD (T (Value ByNameD definable-by-name))
  roll-ByNameD = iso ByNameD.get mkDByName rightInv leftInv
    where
      rightInv : section ByNameD.get mkDByName
      rightInv b = refl
      leftInv : retract ByNameD.get mkDByName
      leftInv (mkDByName _) = refl

instance
  has-bind-ByNameD : HasBind ByNameD (λ _ → Unit)
  has-bind-ByNameD = record { bind = λ rhs body → body ((λ α → fix (λ d▸ → rhs α (d▸ , tt))) , tt) }

eval-by-name : Exp → ByNameD
eval-by-name e = S⟦ e ⟧ empty-pfun
\end{code}

For the \AgdaDatatype{ByNeed} instance, I need to define heaps.
Heaps represent higher-order state, the total modelling of which is one of the
main motivations for guarded type theory.
As such, the heap is also the place where I need to break another negative
recursive occurrence through the use of the \emph{later} modality and
locally deactivating the positivity checker.
Furthermore, I postulate the existence of a bump allocator \AgdaFunction{nextFree}
as well as the well-addressedness invariant from \Cref{sec:op-sem}, that is,
any address allocated is in the domain of the heap.

\begin{code}
Addr : Set
Addr = ℕ

record ByNeedD : Set

{-# NO_POSITIVITY_CHECK #-}
data HeapD : Set where
  heapD : ▸ ByNeedD → HeapD

Heap : Set
Heap = Addr ⇀ HeapD
postulate nextFree : Heap → Addr
postulate well-addressed : (μ : Heap) (a : Addr) → ∃[ d ] (μ a ≡ just d)

definable-by-need : ▸ ByNeedD → Set
definable-by-need _ = Unit

record ByNeedD where
  constructor mkByNeed
  field get : Heap → T (Value ByNeedD definable-by-need × Heap)
\end{code}

Finally, I may give the definition of \AgdaDatatype{ByNeed}.

\begin{code}
return-ByNeed : ∀ {v} → v → Heap → T (v × Heap)
return-ByNeed v = λ μ → return (v , μ)

{-
_>>=-ByNeed_ : ∀ {τ} {{_ : Monad τ}} {a} {b} → ByNeed τ a → (a → ByNeed τ b) → ByNeed τ b
_>>=-ByNeed_ {τ} {a} {b} m k = mkByNeed (λ μ → ByNeed.get m μ >>= aux)
  where
    aux : (a × Heap (ByNeed τ)) → τ (b × Heap (ByNeed τ))
    aux (a , μ') = ByNeed.get (k a) μ'

instance
  monad-ByNeed : ∀ {τ} {{_ : Monad τ}} → Monad (ByNeed τ)
  monad-ByNeed = record { return = return-ByNeed; _>>=_ = _>>=-ByNeed_ }

step-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Event → ▸(ByNeed τ v) → ByNeed τ v
step-ByNeed {τ} {v} e m = mkByNeed (λ μ → step e (λ α → ByNeed.get (m α) μ))

instance
  trace-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Trace (ByNeed τ v)
  trace-ByNeed = record { step = step-ByNeed  }
-}
\end{code}

What is a bit

If we were able to switch the order of λ μ and λ α this code would still compile
and we would not need the postulate no-α-in-μ.
Alas, we are stuck with the current encoding because of the abstractions involved:
We can't push the λ α into the surrounding ByNeed.

\begin{code}
{-
-- | See step-ByNeed why this postulate is OK.
--postulate
--  no-α-in-μ : ∀ {τ} (f : Heap (ByNeed τ) → ▸(τ (Value (ByNeed τ) × Heap (ByNeed τ))))
--            → Σ  (▸(D (ByNeed τ)))
--                (λ d▸ → ∀ μ (@tick α : Tick) → ByNeed.get (d▸ α) μ ≡ (λ μ (@tick α : Tick) →  μ α)

fetch : ∀ {τ} {{_ : Monad τ}} → Addr → ▸ ▸ (D (ByNeed τ))
fetch {τ} a = λ α → λ μ → λ α2 → aux μ (fst (well-addressed μ a)) α
  where
    aux : Heap (ByNeed τ) → HeapD (ByNeed τ) → ▸(τ (Value (ByNeed τ) × Heap (ByNeed τ)))
    aux μ (heapD d▸) α = ByNeed.get (d▸ α) μ

memo : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → Addr → ▸(D (ByNeed τ)) → ▸(D (ByNeed τ))
memo {τ} a d▸ = fix memo' d▸
  where
    memo' : ▸(▸(D (ByNeed τ)) → ▸(D (ByNeed τ)))
          →   ▸(D (ByNeed τ)) → ▸(D (ByNeed τ))
    memo' rec▸ d▸ α₁ = do
      v ← d▸ α₁
      step update (λ _α₂ → mkByNeed (λ μ → return (v , μ [ a ↦ heapD (rec▸ α₁ (λ _ → return v)) ])))

bind-ByNeed : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → ▸(▸(D (ByNeed τ)) → D (ByNeed τ)) → (▸(D (ByNeed τ)) → D (ByNeed τ)) → D (ByNeed τ)
bind-ByNeed {τ} rhs body = do
  a ← mkByNeed (λ μ → return (nextFree μ , μ))
  mkByNeed (λ μ → return (42 , μ [ a ↦ heapD (memo a (λ α → rhs α (fetch a α))) ]))
  step let1 (λ α → mkByNeed (λ μ → ByNeed.get (body (fetch a α))))

instance
  has-bind-ByNeed : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → HasBind (D (ByNeed τ))
  has-bind-ByNeed = record { bind = bind-ByNeed }

eval-by-need : Exp → T (Value (ByNeed T) × Heap (ByNeed T))
eval-by-need e = ByNeed.get (S⟦ e ⟧ empty-pfun) empty-pfun
-}
\end{code}
