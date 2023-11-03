%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Abstractions where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.List as List
import Expr
import Order
import Interpreter
\end{code}
%endif

\section{Soundness}
\label{sec:soundness}

We will now give three important meta-theoretic results:
The first is that |eval| instantiated at |D τ| is a total, coinductive function
whenever the |step| method of |τ| suspends evaluation of its argument.
Furthermore, we show that |D (ByNeed T)| is adequate \wrt the Lazy Krivine
machine in \Cref{fig:lk-semantics}.
We expect that similar adequacy results can be shown for the |ByName| and
|ByValue| trace transformers.
Finally, in the spirit of \Cref{Keidel:18}, we utilise parametricity to
derive sufficient soundness criterions for abstract instantiations that are
comparatively small and compositional.\sg{improve}

\subsection{Totality of |D|}
\label{sec:totality}

As we have discussed in \Cref{sec:continuity}, there are a few strings attached
to working with continuity and partiality in the context of denotational
semantics.

\sg{Can probably cut out much of this introduction as space becomes lacking}
The key to getting rid of partiality and thus denoting infinite computations
with total elements is to avoid working with algebraic domains directly and
instead work in a total type theory with \emph{guarded recursive types}, such as
Ticked Cubical Type Theory~(TCTT)~\citep{tctt}.%
\footnote{Of course, in reality we are just using guarded type theory as a meta
language~\citep{Moggi:07} with a domain-theoretic model in terms of the topos of
trees~\citep{gdtt}.
This meta language is sufficiently expressive as a logic to
express proofs, though, justifying the view that we are extending ``math''
with the ability to conveniently reason about computable functions on infinite
data without needing to think about topology and approximation directly.}
The fundamental innovation of these theories is the integration of the
``later'' modality $\later$ which allows to define coinductive data types
with negative recursive occurrences such in our ``data type'' $D$ from
\Cref{sec:domain-theory}, as first realised by \citet{Nakano:00}.

Whereas previous theories of coinduction require syntactic productivity
checks~\citep{Coquand:94}, requiring tiresome constraints on the form of guarded
recursive functions, the appeal of TCTT is that productivity is instead proven
semantically, in the type system.

The way that TCTT achieves this is roughly as follows: The type $\later T$
represents data of type $T$ that will become available after a finite amount
of computation, such as unrolling one layer of a fixpoint definition.
It comes with a general fixpoint combinator $\fix : \forall A.\ (\later A \to
A) \to A$ that can be used to define both coinductive \emph{types} (via guarded
recursive functions on the universe of types~\citep{BirkedalMogelbergEjlers:13})
as well as guarded recursive \emph{terms} inhabiting said types.
The classic example is that of coinductive streams:
\[
  Str = ℕ \times \later Str \qquad ones = \fix (r : \later Str).\ (1,r),
\]
where $ones : Str$ is the constant stream of $1$.
In particular, $Str$ is the fixpoint of a locally contractive functor $F(X) =
ℕ \times \later X$.
According to \citet{BirkedalMogelbergEjlers:13}, any type expression in simply
typed lambda calculus defines a locally contractive functor as long as any
occurrence of $X$ is under a $\later$, so we take that as the well-formedness
criterion of coinductive types in this work.
The most exciting consequence is that
$D ::= \FunV(f ∈ \later D \to \later D) \mid \bot$ (where $\bot$ is interpreted
as a plain nullary data constructor rather than as the least element of
some partial order) is a sound coinductive encoding of the data type in
\Cref{sec:domain-theory}.
Even unguarded positive occurrences as in
$D ::= \FunV(f ∈ \later D \to D) \mid \bot$ are permissible as

As a type constructor, $\later$ is an applicative
functor~\citep{McBridePaterson:08} via functions
\[
  \purelater : \forall A.\ A \to \later A \qquad \wild \aplater \wild : \forall A,B.\ \later (A \to B) \to \later A \to \later B,
\]
allowing us to apply a familiar framework of reasoning around $\later$.

We will now outline the changes necessary to encode |eval| in Guarded Cubical
Agda, a system implementing Ticked Cubical Type Theory~\citep{tctt}.
The very basic idea is that |step|s doing variable |Lookup| need to suspend
evaluation of the argument denotation in order to yield a guarded recursive definition.

\begin{itemize}
  \item There's a negative occurrence in the type of
\end{itemize}
This requirement
Thus, we need to change its type to |step :: Event -> Later (τ v) -> τ v|.


In doing so, we will have proven that |eval| is a total function, thus
fast and loose equational reasoning about |eval| is not only \emph{morally}
correct~\citep{Danielsson:06}, but correct.
Furthermoe, since evaluation order doesn't matter for |eval|, we could have
defined it in a strict language (with thunk suspension just as well.


