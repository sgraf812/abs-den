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
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (T; _∧_; _∨_)
open import Function
open import PartialFunction
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Foundations.Isomorphism
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
  step-T : Event → ▸ T A → T A

data Value (τ : Set → Set) : Set

D : (Set → Set) → Set
D τ = τ (Value τ)
\end{code}

As explained in \Cref{sec:totality-formal}, a notable difference to the
definition of \AgdaDatatype{Value} in the main body is that I need to break the
negative occurrence in \AgdaField{fun} by the use of \emph{later} $▸$.
Unfortunately, Agda's positivity checker does not currently support
the later modality, so I have to deactivate it via a potentially
dangerous-looking pragma in the definition that follows.
Note that the use of this pragma is solely so that the positivity
checker does not try to recurse through the occurrence of $▸ D$.

\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data EnvD (D : Set) : Set where
  stepLookup : Var → ▸ D → EnvD D
\end{code}

I have reported this bug to the Agda maintainers.%
\footnote{\url{https://github.com/agda/agda/issues/6587}}

Note that $\AgdaDatatype{EnvD}~D$ is effectively the subtype of $D$
of denotations that go into the environment $ρ$.
One should think of $\AgdaField{stepLookup}~x~d'$ as a $d$ such that
$d = \AgdaField{step}~(\AgdaInductiveConstructor{lookup}~x)~d'$.

Actually, I would prefer to simply \emph{express} the subtyping relationship via
$\AgdaFunction{Σ}~D~\AgdaFunction{is-env}$, as in the type of \AgdaField{fun},
but the use of
$\AgdaFunction{is-env} : \AgdaFunction{D}~T \to \AgdaPrimitiveType{Set}$
requires an instance of $\AgdaDatatype{Trace}~(\AgdaFunction{D}~T)$
\emph{in the type} of $\AgdaField{fun-V}$, leading to a circular
definition.

Defining the bijection to $\AgdaDatatype{EnvD}$ is easy, enough, though:

\begin{code}
toSubtype : ∀ {D} {{_ : Trace D}} → EnvD D → Σ D is-env
toSubtype {{_}} (stepLookup x d▸) = (step (lookup x) d▸ , x , d▸ , refl)

fromSubtype : ∀ {D} {{_ : Trace D}} → Σ D is-env → EnvD D
fromSubtype {{_}} (_ , x , d▸ , _) = stepLookup x d▸
\end{code}

I can also prove that the pair indeed forms a bijection:

\begin{code}
env-iso : ∀ {D} {{_ : Trace D}} → Iso (EnvD D) (Σ D is-env)
env-iso = iso toSubtype fromSubtype from-to to-from
  where
    from-to : ∀ d → toSubtype (fromSubtype d) ≡ d
    from-to (d , x , d▸ , prf) i = (prf (~ i) , x , d▸ , λ i₁ → prf (i₁ ∨ (~ i)))
    to-from : ∀ d → fromSubtype (toSubtype d) ≡ d
    to-from (stepLookup x d▸) = refl
\end{code}

Hence I define the data constructors \AgdaInductiveConstructor{fun-V} and
\AgdaInductiveConstructor{con-V} of \AgdaDatatype{Value} in terms of
\AgdaDatatype{EnvD} and apply the bijection when defining the
type class instance for \AgdaDatatype{Domain}.
The rest is exactly as in \Cref{sec:interp}.

\begin{code}
data Value T where
  stuck-V : Value T
  fun-V : (EnvD (D T) → D T) → Value T
  con-V : Con → List (EnvD (D T)) → Value T

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
fun-Value f = return (fun-V (f ∘ toSubtype))

apply-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
               → D τ → Σ (D τ) is-env → D τ
apply-Value {τ} dv da = dv >>= aux
  where
    aux : Value τ → D τ
    aux (fun-V f) = f (fromSubtype da)
    aux _         = stuck-Value

con-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
             → Con → List (Σ (D τ) is-env) → D τ
con-Value K ds = return (con-V K (List.map fromSubtype ds))

select-Value :  ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}}
                → D τ → List (Con × (List (Σ (D τ) is-env) → D τ)) → D τ
select-Value {τ} dv alts = dv >>= aux alts
  where
    aux : List (Con × (List (Σ (D τ) is-env) → D τ)) → Value τ → D τ
    aux ((K' , alt) ∷ alts) (con-V K ds) with decEq-ℕ K K'
    ... | yes _ = alt (List.map toSubtype ds)
    ... | no _  = aux alts (con-V K ds)
    aux _ _ = stuck-Value

instance
  domain-Value : ∀ {τ} {{_ : Monad τ}} {{_ : Trace (D τ)}} → Domain (D τ) is-env
  domain-Value = record {  stuck = stuck-Value;
                           fun = fun-Value;  apply = apply-Value;
                           con = con-Value;  select = select-Value }
\end{code}

This suffices to define the \AgdaDatatype{ByName} interpreter.
The instance of \AgdaDatatype{HasBind} is particularly interesting, because it
employs the guarded fixpoint combinator \AgdaPrimitive{fix}:

\begin{code}
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
    record { bind = λ rhs body → body (λ α → fix (λ rhs▸ → rhs α rhs▸)) }

eval-by-name : Exp → D (ByName T)
eval-by-name e = S⟦ e ⟧ empty-pfun
\end{code}

For the \AgdaDatatype{ByNeed} instance, I need to define heaps.
Heaps represent higher-order state, the total modelling of which is one of the
main motivations for guarded type theory.
As such, the heap is also the place where I need to break another negative
recursive occurrence through the use of the \emph{later} modality and
locally deactivate the positivity checker.

Furthermore, I postulate the existence of a bump allocator \AgdaFunction{nextFree}
as well as the well-addressedness invariant from \Cref{sec:op-sem}, that is,
any address allocated is in the domain of the heap.
These postulates could well be factored into module parameters of the
development, but it is simpler to postulate them here.

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

The definition of \AgdaDatatype{ByNeed} and its type class instances
are exactly as in the main body, with the small exception of
\AgdaFunction{step-ByNeed}, which needs to pass around the \AgdaPrimitive{Tick}
variable $α$.

\begin{code}
record ByNeed τ v where
  constructor mkByNeed
  field get : Heap (ByNeed τ) → τ (v × Heap (ByNeed τ))

return-ByNeed : ∀ {τ} {{_ : Monad τ}} {v} → v → ByNeed τ v
return-ByNeed v = mkByNeed (λ μ → return (v , μ))

_>>=-ByNeed_ :  ∀ {τ} {{_ : Monad τ}} {a} {b}
                → ByNeed τ a → (a → ByNeed τ b) → ByNeed τ b
_>>=-ByNeed_ {τ} {a} {b} m k = mkByNeed (λ μ → ByNeed.get m μ >>= aux)
  where
    aux : (a × Heap (ByNeed τ)) → τ (b × Heap (ByNeed τ))
    aux (a , μ') = ByNeed.get (k a) μ'

instance
  monad-ByNeed : ∀ {τ} {{_ : Monad τ}} → Monad (ByNeed τ)
  monad-ByNeed = record { return = return-ByNeed; _>>=_ = _>>=-ByNeed_ }

step-ByNeed :  ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}}
               → Event → ▸(ByNeed τ v) → ByNeed τ v
step-ByNeed {τ} {v} e m = mkByNeed (λ μ → step e (λ α → ByNeed.get (m α) μ))

instance
  trace-ByNeed : ∀ {τ} {v} {{_ : ∀ {V} → Trace (τ V)}} → Trace (ByNeed τ v)
  trace-ByNeed = record { step = step-ByNeed  }
\end{code}

The next step is to define \AgdaFunction{fetch}, the function that accesses the
heap.
Unfortunately, my definition needs to appeal to a postulate that would generally
be unsafe to use.
To see why this postulate is necessary and why my use of it is actually safe,
consider the following definition:

\begin{code}
stepLookupFetch :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
                   → Var → Addr → D (ByNeed τ)
stepLookupFetch {τ} x a = mkByNeed (λ μ →
  let d▸ = HeapD.get (fst (well-addressed μ a)) in
  step (lookup x) (λ α → ByNeed.get (d▸ α) μ))
\end{code}

(Note that $\AgdaFunction{fst}~(\AgdaPostulate{well-addressed}~μ~a)$ simply
returns the heap entry in $μ$ at address $a$, which must be present by
my assumption of well-addressedness.)

This definition constructs the total Agda equivalent of the Haskell expression
$\varid{step}~(\conid{Lookup}~\varid{x})~(\varid{fetch}~\varid{a})$, for the
given variable $\varid{x}$ and address $\varid{a}$.
Ultimately, all denotations in the interpreter environment $ρ$ will take this
form under by-need evaluation. (In \Cref{defn:syn-heap} I define an even sharper
characterisation.)
In fact, \emph{all} uses of \AgdaFunction{fetch} will take this form!

Unfortunately, it is hard to decompose \AgdaFunction{stepLookupFetch} into
separate function calls to \AgdaFunction{step} and
$\AgdaFunction{fetch} : \AgdaFunction{Addr} \to \AgdaPrimitive{▸}(\AgdaFunction{D}~(\AgdaDatatype{ByNeed}~\AgdaDatatype{T}))$,
because the latter will then need to bind the tick variable $α$ (part of \AgdaPrimitive{▸})
before the heap $μ$ (part of $\AgdaFunction{D}~(\AgdaDatatype{ByNeed}~\AgdaDatatype{T})$).
This is in contrast to the order of binders in \AgdaFunction{stepLookupFetch},
which may bind $μ$ before $α$, because lookup steps leave the heap unchanged.
(See \AgdaFunction{step-ByNeed} above for confirmation, which is inlined into
\AgdaFunction{stepLookupFetch}).

The flipped argument order is problematic for my definition of
\AgdaFunction{fetch}, because ticked type theory conservatively assumes
that $μ$ might depend on $α$ --- when in reality it does not in
\AgdaFunction{stepLookupFetch}!
The result is that the subexpression $\AgdaField{ByNeed.get}~(d▸~α)~μ$ would
not be well-typed under the flipped order, because
\begin{itemize}
\setlength{\itemsep}{0pt}
\item $d▸$ comes from $μ$, and
\item $μ$ might already depend on $α$, because
\item $μ$ was introduced after $α$, and hence
\item $d▸$ may not be applied to $α$ again in ticked type theory.
\end{itemize}
I currently know of no way to encode this knowledge without a postulate of
the following form:
\begin{code}
postulate
  flip-tick       : ∀ {A B : Set} → (A → ▸ B) → ▸ (A → B)
  flip-tick-beta  :  ∀ {A B : Set} {f : A → ▸ B} {μ : A} {@tick α : Tick}
                     → flip-tick f α μ ≣ f μ α
{-# REWRITE flip-tick-beta #-}
\end{code}
It is most helpful to look at the postulated ``implementation rule''
\AgdaPostulate{flip-tick-beta} to see when use of \AgdaPostulate{flip-tick} is
safe:
Given some $f$ and a heap $μ$ that \emph{does not depend} on some tick variable
$α$, call $f$ with $μ$ first instead of $α$.
So \AgdaPostulate{flip-tick} literally flips around the arguments it receives
before calling $f$, and unless $μ$ does not depend on $α$, the application of
\AgdaPostulate{flip-tick} is stuck because the rule does not apply.

I use \AgdaPostulate{flip-tick} in the implementation of \AgdaFunction{fetch}
exactly to flip back the binding order to what it will be in the use site
\AgdaFunction{stepLookupFetch}:

\begin{code}
fetch : ∀ {τ} {{_ : Monad τ}} → Addr → ▸(D (ByNeed τ))
fetch {τ} a = map▸ mkByNeed (flip-tick (λ μ →
  let d▸ = HeapD.get (fst (well-addressed μ a)) in
  (λ α → ByNeed.get (d▸ α) μ)))
\end{code}

Agda is able to calculate that this definition of \AgdaFunction{fetch}
is equivalent to the one inlined into \AgdaFunction{stepLookupFetch}:

\begin{code}
postulate-ok :  ∀ {τ x a} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
                → step (lookup x) (fetch {τ} a) ≡ stepLookupFetch x a
postulate-ok = refl
\end{code}

(Note that this proof automatically applies \AgdaPostulate{flip-tick-beta} by
the \AgdaKeyword{REWRITE} pragma above.)

This should be sufficient justification for my use of
\AgdaPostulate{flip-tick}.
The definition of \AgdaFunction{memo} is a bit more involved
but does not need any postulates at all:

\begin{code}
memo :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
        → Addr → ▸(D (ByNeed τ)) → ▸(D (ByNeed τ))
memo {τ} a d▸ = fix memo' d▸
  where
    memo' : ▸(▸(D (ByNeed τ)) → ▸(D (ByNeed τ)))
          →   ▸(D (ByNeed τ)) → ▸(D (ByNeed τ))
    memo' rec▸ d▸ α₁ = do
      v ← d▸ α₁
      step update (λ _α₂ → mkByNeed (λ μ →
        return (v , μ [ a ↦ heapD (rec▸ α₁ (λ _ → return v)) ])))
\end{code}

Building on \AgdaFunction{fetch} and \AgdaFunction{memo}, I define the
\AgdaDatatype{HasBind} instance as follows

\hfuzz=2.5em
\begin{code}
bind-ByNeed :  ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
               → ▸  (▸(D (ByNeed τ)) → D (ByNeed τ))
               →    (▸(D (ByNeed τ)) → D (ByNeed τ))
               →    D (ByNeed τ)
bind-ByNeed {τ} rhs body = do
  a ← mkByNeed (λ μ → return (nextFree μ , μ))
  mkByNeed (λ μ →
    return (tt , μ [ a ↦ heapD (memo a (λ α → rhs α (fetch a))) ]))
  step let1 (λ _α → body (fetch a))

instance
  has-bind-ByNeed  : ∀ {τ} {{_ : Monad τ}} {{_ : ∀ {V} → Trace (τ V)}}
                   → HasBind (D (ByNeed τ))
  has-bind-ByNeed = record { bind = bind-ByNeed }

eval-by-need : Exp → T (Value (ByNeed T) × Heap (ByNeed T))
eval-by-need e = ByNeed.get (S⟦ e ⟧ empty-pfun) empty-pfun
\end{code}

This completes the definition of \AgdaFunction{eval-by-need} which is thus
proven total.

\begin{code}[hide]
exp1 : Exp
exp1 = let' 0 (app (lam 1 (lam 2 (ref 2))) 0) (app (ref 0) 0)
-- A translation of `let i = (λy.λx.x) i in i i`

res1 = eval-by-need exp1
\end{code}
