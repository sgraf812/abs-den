\pagebreak
\subsection*{Denotational Interpreter}

Finally, I can define the generic denotational interpreter from \Cref{fig:eval}
in Agda.
I do so without defining any concrete instances; the $\conid{ByName}$ and
$\conid{ByNeed}$ variants will follows in another module.

\begin{code}
{-# OPTIONS --cubical --guarded --rewriting #-}
module Semantics where

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
\end{code}

First I define the $\AgdaDatatype{Event}$ data type and the type class definitions for
$\AgdaDatatype{Trace}$, $\AgdaDatatype{Domain}$ and $\AgdaDatatype{HasBind}$.
Note the use of $\AgdaFunction{Σ}~D~p$
in $\AgdaField{fun}$, $\AgdaField{apply}$ and $\AgdaField{select}$ to characterise the
subtype of denotations that will end up in the environment.
Also mind the use of the later modality in $\AgdaField{step}$ as well as
$\AgdaField{bind}$.

\begin{code}
data Event : Set where
  lookup : Var → Event
  update : Event
  app1 : Event
  app2 : Event
  case1 : Event
  case2 : Event
  let1 : Event

record Trace (T : Set) : Set where
  field
    step : Event → ▸ T → T
open Trace {{...}} public

record Domain (D : Set) (p : D → Set) : Set where
  field
    stuck : D
    fun : (Σ D p → D) → D
    apply : D → Σ D p → D
    con : Var → List (Σ D p) → D
    select : D → List (Var × (List (Σ D p) → D)) → D
open Domain {{...}} public

record HasBind (D : Set) : Set where
  field
    bind : ▸(▸ D → D) → (▸ D → D) → D
open HasBind {{...}} public
\end{code}

I will instantiate this predicate with the following predicate
\AgdaFunction{is-look}, which simply expresses that any $d$ that ends
up in an environment must be of the form $\AgdaField{step}~(\AgdaInductiveConstructor{lookup}~x)~\mathit{d▸}$ for some $x$ and
$\mathit{d▸}$.

\begin{code}
is-look : ∀ {D} {{trc : Trace D}} → D → Set
is-look {D} d = ∃[ x ] ∃[ d▸ ] (d ≡ step {D} (lookup x) d▸)
\end{code}

\pagebreak
And finally, I can encode $\AgdaFunction{S$\llbracket\_\rrbracket$}$ in this
type class algebra, pretty much as in \Cref{fig:eval}.
The definition differs in three ways:
\begin{itemize}
\setlength{\itemsep}{0pt}
\item
  I need to prove \AgdaFunction{is-look} when a let binding introduces new
  bindings to the environment.
\item
  I omit tests comparing data constructor arity because that is not particularly
  interesting here; the mismatching cases would just return \AgdaField{stuck}.
\item
  The definition is a bit more involved than in Haskell because of the diligent
  passing of \AgdaPrimitiveType{Tick}s.
  This is in order to convince Agda that
  $\AgdaFunction{S$\llbracket\_\rrbracket$}$ is productive by construction, so
  that no separate proof of totality is necessary.
\end{itemize}

\hfuzz=2.5em
\begin{code}
S⟦_⟧_ :  ∀ {D} {{_ : Trace D}} {{_ : Domain D is-look}} {{_ : HasBind D}}
         → Exp → (Var ⇀ Σ D is-look) → D
S⟦_⟧_ {D} e ρ = fix sem e ρ
  where
    sem : ▸(Exp → (Var ⇀ Σ D is-look) → D) → Exp → (Var ⇀ Σ D is-look) → D
    sem recurse▸ (ref x) ρ with ρ x
    ... | nothing      = stuck
    ... | just (d , _) = d
    sem recurse▸ (lam x body) ρ =
      fun (λ d → step app2 (λ α → recurse▸ α body (ρ [ x ↦ d ])))
    sem recurse▸ (app e x) ρ with ρ x
    ... | nothing = stuck
    ... | just d  = step app1 (λ α → apply (recurse▸ α e ρ) d)
    sem recurse▸ (let' x e₁ e₂) ρ =
      bind  (λ α d₁ →
              recurse▸ α e₁ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ]))
            (λ d₁ → step let1 (λ α →
              recurse▸ α e₂ (ρ [ x ↦ (step (lookup x) d₁ , x , d₁ , refl) ])))
    sem recurse▸ (conapp K xs) ρ with pmap ρ xs
    ... | nothing = stuck
    ... | just ds = con K ds
    sem recurse▸ (case' eₛ alts) ρ =
      step case1 (λ α → select (recurse▸ α eₛ ρ) (List.map alt alts))
        where
          alt : Con × List Var × Exp → Con × (List (Σ D is-look) → D)
          alt (k , xs , eᵣ) = (k , (λ ds →
            step  case2 (λ α → recurse▸ α eᵣ (ρ [ xs ↦* ds ]))))
\end{code}
