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
  step-T : Event → ▸ T A → T A

data Value (τ : Set → Set) : Set

D : (Set → Set) → Set
D τ = τ (Value τ)
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
data LookupD (D : Set) : Set where
  stepLookup : Var → ▸ D → LookupD D
\end{code}

I have reported this bug to the Agda maintainers.%
\footnote{\url{https://github.com/agda/agda/issues/6587}}

Note that a $\AgdaDatatype{LookupD}~D$ is effectively a subtype of $D$.
One should think of $\AgdaField{stepLookup}~x~d'$ as a $d$ such that
$d = \AgdaField{step}~(\AgdaInductiveConstructor{lookup}~x)~d'$.

Actually, I would prefer to simply \emph{say} the latter via
$\AgdaFunction{Σ}~D~\AgdaFunction{is-look}$, as in the type of \AgdaField{fun},
but there currently is no type-safe way to say that.

Defining the bijection myself is easy, enough, though:

\begin{code}
toSubtype : ∀ {D} {{_ : Trace D}} → LookupD D → Σ D is-look
toSubtype {{_}} (stepLookup x d▸) = (step (lookup x) d▸ , x , d▸ , refl)

fromSubtype : ∀ {D} {{_ : Trace D}} → Σ D is-look → LookupD D
fromSubtype {{_}} (_ , x , d▸ , _) = stepLookup x d▸
\end{code}

Hence I define the data constructors \AgdaInductiveConstructor{fun-V} and
\AgdaInductiveConstructor{con-V} of \AgdaDatatype{Value} in terms of
\AgdaDatatype{LookupD} and apply the bijection when defining the
type class instance for \AgdaDatatype{Domain}.
The rest is exactly as in \Cref{sec:interp}.

\begin{code}
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
\end{code}

This is already enough to define the \AgdaDatatype{ByName} interpreter.
The instance of \AgdaDatatype{HasBind} is particularly interesting, because it
employs the guarded fixpoint combinator \AgdaPrimitive{fix}:

\begin{code}
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
  has-bind-ByName {τ} = record { bind = λ rhs body → body (λ α → fix (λ rhs▸ → rhs α rhs▸)) }

eval-by-name : Exp → D (ByName T)
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

record ByNeed (τ : Set → Set) (v : Set) : Set

{-# NO_POSITIVITY_CHECK #-}
record HeapD (τ : Set → Set) : Set where
  constructor heapD
  field get : ▸(D τ)

Heap : (Set → Set) → Set
Heap τ = Addr ⇀ HeapD τ
postulate nextFree : ∀ {τ} → Heap τ → Addr
postulate well-addressed : ∀ {τ} (μ : Heap τ) (a : Addr) → ∃[ d ] (μ a ≡ just d)
\end{code}

Finally, I may give the definition of \AgdaDatatype{ByNeed}.

\begin{code}
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

step-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Event → ▸(ByNeed τ v) → ByNeed τ v
step-ByNeed {τ} {v} e m = mkByNeed (λ μ → step e (λ α → ByNeed.get (m α) μ))

instance
  trace-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Trace (ByNeed τ v)
  trace-ByNeed = record { step = step-ByNeed  }
\end{code}

What is a bit

If we were able to switch the order of λ μ and λ α this code would still compile
and we would not need the postulate no-α-in-μ.
Alas, we are stuck with the current encoding because of the abstractions involved:
We can't push the λ α into the surrounding ByNeed.

\begin{code}
stepLookupFetch : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → Var → Addr → D (ByNeed τ)
stepLookupFetch {τ} x a = mkByNeed (λ μ →
  let d▸ = HeapD.get (fst (well-addressed μ a)) in
  step (lookup x) (λ α → ByNeed.get (d▸ α) μ))

postulate
  unsafe-swap-tick       : ∀ {A B : Set} → (A → ▸ B) → ▸ (A → B)
  unsafe-swap-tick-impl  : ∀ {A B : Set} {f : A → ▸ B} {μ α} → unsafe-swap-tick f α μ ≡ f μ α

fetch : ∀ {τ} {{_ : Monad τ}} → Addr → ▸(D (ByNeed τ))
fetch {τ} a = map▸ mkByNeed (unsafe-swap-tick (λ μ →
  let d▸ = HeapD.get (fst (well-addressed μ a)) in
  (λ α → ByNeed.get (d▸ α) μ)))

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
  mkByNeed (λ μ → return (42 , μ [ a ↦ heapD (memo a (λ α → rhs α (fetch a))) ]))
  step let1 (λ _α → body (fetch a))

instance
  has-bind-ByNeed : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}} → HasBind (D (ByNeed τ))
  has-bind-ByNeed = record { bind = bind-ByNeed }

eval-by-need : Exp → T (Value (ByNeed T) × Heap (ByNeed T))
eval-by-need e = ByNeed.get (S⟦ e ⟧ empty-pfun) empty-pfun
\end{code}
