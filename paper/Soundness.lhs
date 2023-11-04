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

\subsection{Totality of |eval|}
\label{sec:totality}

The essential idea to prove totality of concrete semantic instantiations of our
shared interpreter is that \emph{there is only a finite number of steps between
every $\LookupT$ transition}.%
\footnote{Our experiments with a denotational interpreter for
PCF~\citep{Plotkin:77} indicate that this statement holds for PCF as well if
$\UnrollT$ transitions introduced by the fixpoint operator were included.}
In other words, if every environment lookup produces a |Step| constructor, then
our semantics is total by coinduction.

We make this argument precise by encoding |eval| in Guarded Cubical Agda,
implementing a total type theory with
\emph{guarded recursive types}~\citet{tctt}.
In contrast to traditional denotational semantics based on algebraic domain
theory, guarded recursive type theory avoids issues of continuity and partiality
discussed in \Cref{sec:continuity}, quite like programming in Rust ensures
a sound stack and register discipline compared to writing Assembler code
directly.%
\footnote{Of course, the underlying model of guarded recursive type
theories is the topos of trees~\citep{gdtt}, which very much enjoys an
approximation order and partiality; the point is that any type safe program
(Rust) ``compiles'' to a well-defined topos model (Assembler) without needing to
think about topology and approximation directly.
In essence, we are using guarded type theory as a meta language in the sense of
\citeauthor{Moggi:07}.}

\sg{Can probably cut out much of this introduction as space becomes lacking}
The fundamental innovation of guarded recursive type theory is the integration
of the ``later'' modality $\later$ which allows to define coinductive data
types with negative recursive occurrences such as in the data constructor |Fun
:: (highlight (D τ) -> D τ) -> Value τ| (recall that |D τ = τ (Value τ)|), as
first realised by \citet{Nakano:00}.

Whereas previous theories of coinduction require syntactic productivity
checks~\citep{Coquand:94}, requiring tiresome constraints on the form of guarded
recursive functions, the appeal of a guarded type theories is that productivity
is instead proven semantically, in the type system.

The way that is achieved is roughly as follows: The type $\later T$
represents data of type $T$ that will become available after a finite amount
of computation, such as unrolling one layer of a fixpoint definition.
It comes with a general fixpoint combinator $\fix : \forall A.\ (\later A \to
A) \to A$ that can be used to define both coinductive \emph{types} (via guarded
recursive functions on the universe of types~\citep{BirkedalMogelbergEjlers:13})
as well as guarded recursive \emph{terms} inhabiting said types.
The classic example is that of infinite streams:
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
The most exciting consequence is that changing the |Fun| data constructor to
|Fun :: (Later (D τ) -> D τ) -> Value τ| makes |Value τ| a well-defined
coinductive data type,%
\footnote{The reason why the positive occurrence of |D τ| does not need to be
guarded is that the type of |Fun| can more formally be encoded by a mixed
inductive-coinductive type, \eg,
$|Value τ| = \fix X.\ \lfp Y.\ ... || |Fun|~(X \to Y) || ...$ }
whereas syntactic approaches to coinduction reject any negative recursive
occurrence.

%As a type constructor, $\later$ is an applicative
%functor~\citep{McBridePaterson:08} via functions
%\[
%  \purelater : \forall A.\ A \to \later A \qquad \wild \aplater \wild : \forall A,B.\ \later (A \to B) \to \later A \to \later B,
%\]
%allowing us to apply a familiar framework of reasoning around $\later$.

We will now outline the changes necessary to encode |eval| in Guarded Cubical
Agda, a system implementing Ticked Cubical Type Theory~\citep{tctt}, as well
as the concrete instances |D (ByName T)| and |D (ByNeed T)| from
\Cref{fig:trace-instances,fig:by-need}.
The full, type-checked development is available in the Supplement.
\begin{itemize}
  \item We need to delay in |step|; thus its definition in |Trace| changes to
    |step :: Event -> Later (τ v) -> τ v|.
  \item
    All |D|s that will be passed to lambdas, put into the environment or
    stored in fields need to have the form |step (Lookup x) d| for some
    |x::Name| and a delayed |d :: Later (D τ)|.
    This is enforced as follows:
    \begin{enumerate}
      \item
        The |Domain| type class gains an additional predicate parameter |p :: D -> Set|
        that will be instantiated by the semantics to a predicate that checks
        that the |D| has the required form |step (Lookup x) d| for some
        |x::Name|, |d :: Later (D τ)|.
      \item
        Then the method types of |Domain| use a Sigma type to encode conformance
        to |p|.
        For example, the type of |Fun| changes to |(Σ D p -> D) -> D|.
      \item
        The reason why we need to encode this fact is that the guarded recursive
        data type |Value| has a constructor the type of which amounts to
        |Fun :: (Name times Later (D τ) -> D τ) -> Value τ|, breaking the
        previously discussed negative recursive cycle by a $\later$ and
        expecting |x::Name|, |d::Later (D τ)| such that the original |D τ| can
        be recovered as |step (Lookup x) d|.
        This is in contrast to the original definition |Fun :: (D τ -> D τ) ->
        Value τ| which would \emph{not} type-check.
    \end{enumerate}
  \item
    Expectedly, |HasBind| becomes more complicated because it encodes the
    fixpoint combinator.
    We settled on |bind :: Later (Later D → D) → (Later D → D) → D|.
  \item
    Higher-order mutable state is among the classic motivating examples for
    guarded recursive types.
    As such it is no surprise that the state-passing of the mutable |Heap| in
    the implementation of |ByNeed| requires breaking of a recursive cycle
    by delaying heap entries, |Heap τ = Addr :-> Later (D τ)|.
\end{itemize}

We find it remarkable how non-invasive these adjustments were \wrt the
definition of the interpreter |eval|!

Thus we have proven that |eval| is a total function, and fast and
loose equational reasoning about |eval| is not only \emph{morally}
correct~\citep{Danielsson:06}, but simply \emph{correct}.
Furthermore, since evaluation order doesn't matter for |eval|, we could have
defined it in a strict language (lowering |Later a| as |() -> a|) just as well.
