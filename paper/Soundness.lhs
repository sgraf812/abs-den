%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Soundness where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.List as List
import Exp
import Order
import Interpreter
import Abstractions

instance Eq (D (ByName T)) where
  (==) = undefined
instance Ord (D (ByName T)) where
  compare = undefined
powMap :: (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ undefined $ map f $ Set.toList s
set = P . Set.singleton
\end{code}
%endif

\section{Soundness}
\label{sec:soundness}

%if False
We will now give three important meta-theoretic results:
The first is that |eval| instantiated at |D τ| is a total, coinductive function
whenever the |step| method of |τ| suspends evaluation of its argument.
Furthermore, we show that |D (ByNeed T)| is adequate \wrt the Lazy Krivine
machine in \Cref{fig:lk-semantics}.
We expect that similar adequacy results can be shown for the |ByName| and
|ByValue| trace transformers.
Finally, in the spirit of \Cref{Keidel:18}, we utilise parametricity to
derive sufficient soundness criterions for abstract instantiations that are
comparatively small and compositional.\sg{revisit}

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
a sound stack and register discipline in the produced Assembler code compared
to writing Assembler code directly.%
\footnote{Of course, the underlying model of guarded recursive type
theories is the topos of trees~\citep{gdtt}, which very much enjoys an
approximation order and partiality; the point is that any type safe program
(Rust) ``compiles'' to a well-defined topos model (Assembler) without needing to
think about topology and approximation directly.
In essence, we are using guarded type theory as a meta language in the sense of
\citeauthor{Moggi:07}.}

Whereas traditional theories of coinduction require syntactic productivity
checks~\citep{Coquand:94}, imposing tiresome constraints on the form of guarded
recursive functions, the appeal of guarded type theories is that productivity
is instead proven semantically, in the type system.
Compared to the alterntaive of \emph{sized types}~\citep{Hughes:96}, guarded
types don't require complicated algebraic manipulations of size parameters;
however perhaps sized types would work just as well.

The fundamental innovation of guarded recursive type theory is the integration
of the ``later'' modality $\later$ which allows to define coinductive data
types with negative recursive occurrences such as in the data constructor |Fun
:: (highlight (D τ) -> D τ) -> Value τ| (recall that |D τ = τ (Value τ)|), as
first realised by \citet{Nakano:00}.
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

\begin{toappendix}
As a type constructor, $\later$ is an applicative
functor~\citep{McBridePaterson:08} via functions
\[
  \purelater : \forall A.\ A \to \later A \qquad \wild \aplater \wild : \forall A,B.\ \later (A \to B) \to \later A \to \later B,
\]
allowing us to apply a familiar framework of reasoning around $\later$.
In order not to obscure our work with pointless symbol pushing
in, \eg, \Cref{fig:sem}, we will often omit the idiom
brackets~\citep{McBridePaterson:08} $\idiom{\wild}$
to indicate where the $\later$ ``effects'' happen.
\end{toappendix}

We will now outline the changes necessary to encode |eval| in Guarded Cubical
Agda, a system implementing Ticked Cubical Type Theory~\citep{tctt}, as well
as the concrete instances |D (ByName T)| and |D (ByNeed T)| from
\Cref{fig:trace-instances,fig:by-need}.
The full, type-checked development is available in the Supplement.
\begin{itemize}
  \item We need to delay in |step|; thus its definition in |Trace| changes to
    |step :: Event -> Later d -> d|.
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
  \item
    We need to pass around |Tick| binders in |eval| in a way that the type
    checker is satisfied; a simple exercise.
    We find it remarkable how non-invasive these adjustment are!
\end{itemize}

Thus we have proven that |eval| is a total function, and fast and
loose equational reasoning about |eval| is not only \emph{morally}
correct~\citep{Danielsson:06}, but simply \emph{correct}.
Furthermore, since evaluation order doesn't matter for |eval|, we could have
defined it in a strict language (lowering |Later a| as |() -> a|) just as well.

\subsection{Adequacy of |eval| at |D (ByNeed T)|}
\label{sec:adequacy}

Proving adequacy of |eval| amounts to showing that the traces generated by
concrete semantic instances such as |D (ByName T)| and |D (ByNeed T)| correspond
one-to-one to the set of what we call the \emph{maximal} small-step traces of
the corresponding (lazy) Krivine machine.
We will show adequacy in this manner at |D (ByNeed T)|; adequacy at |D (ByName
T)| should be simpler, and adequacy at |D (ByVInit T)| \wrt a by-value
small-step semantics should be similar to what we show.

\citet{Sestoft:97} has shown a similar statement relating the derivations of
\citeauthor{Launchbury:93}'s big-step natural semantics for our language to
the subset of \emph{balanced} small-step lazy Krivine (LK) traces, itself a
proper subset of the maximal small-step LK traces that --- by nature of big-step
semantics --- excludes stuck and diverging traces.

More formally, an LK trace is a trace in $(\smallstep)$ from
\Cref{fig:lk-semantics}, \ie, a non-empty and potentially infinite sequence of
LK states $(σ_i)_{i∈\overline{n}}$ (where $\overline{n} = \{ m ∈ ℕ \mid m < n
\}$ when $n∈ℕ$, $\overline{ω} = ℕ$), such that $σ_i \smallstep σ_{i+1}$ for
$i,(i+1)∈\overline{n}$.
The \emph{source} state $σ_0$ exists for finite and infinite traces, while the
\emph{target} state $σ_n$ is only defined when $n \not= ω$ is finite.
When the control expression of a state $σ$ (selected via $\ctrl(σ)$) is a value
$\pv$, we call $σ$ a \emph{return} state and say that the continuation (selected
via $\cont(σ)$) drives evaluation.
Otherwise, $σ$ is an \emph{evaluation} state and $\ctrl(σ)$ drives evaluation.

An important kind of trace is one that never leaves the evaluation context of
its source state:

\begin{definition}[Deep, interior and balanced traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is
  \emph{$κ$-deep} if every intermediate continuation
  $κ_i \triangleq \cont(σ_i)$ extends $κ$ (so $κ_i = κ$ or $κ_i = ... \pushF κ$,
  abbreviated $κ_i = ...κ$).

  \noindent
  A trace $(σ_i)_{i∈\overline{n}}$ is called \emph{interior} if it is
  $\cont(σ_0)$-deep.
  Furthermore, an interior trace $(σ_i)_{i∈\overline{n}}$ is
  \emph{balanced}~\citep{Sestoft:97} if the target state exists and is a return
  state with continuation $\cont(σ_0)$.

  \noindent
  We notate $κ$-deep and interior traces as
  $\deep{κ}{(σ_i)_{i∈\overline{n}}}$ and $\interior{(σ_i)_{i∈\overline{n}}}$, respectively.
\end{definition}

\begin{example}
  Let $ρ=[x↦\pa_1],μ=[\pa_1↦([], \Lam{y}{y})]$ and $κ$ an arbitrary
  continuation. The trace
  \[
     (x, ρ, μ, κ) \smallstep (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is interior and balanced. Its prefixes are interior but not balanced.
  The trace suffix
  \[
     (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is neither interior nor balanced.
\end{example}

%We will say that the transition rules $\LookupT$, $\AppIT$, $\CaseIT$ and $\LetIT$
%are interior, because the lifting into a trace is, whereas the returning
%transitions $\UpdateT$, $\AppET$ and $\CaseET$ are not.

As shown by \citeauthor{Sestoft:97}, a balanced trace starting at a control
expression $\pe$ and ending with $\pv$ loosely corresponds to a derivation of
$\pe \Downarrow \pv$ in a natural big-step semantics or a non-$⊥$ result in a
traditional denotational semantics.
It is when a derivation in a natural semantics does \emph{not} exist that a
small-step semantics shows finesse, in that it differentiates two different
kinds of \emph{maximally interior} (or, just \emph{maximal}) traces:

\begin{definition}[Maximal, diverging and stuck traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is \emph{maximal} if and only if it is
  interior and there is no $σ_{n+1}$ such that $(σ_i)_{i∈\overline{n+1}}$ is
  interior.
  More formally (and without a negative occurrence of ``interior''),
  \[
    \maxtrace{(σ_i)_{i∈\overline{n}}} \triangleq \interior{(σ_i)_{i∈\overline{n}}} \wedge (\not\exists σ_{n+1}.\ σ_n \smallstep σ_{n+1} \wedge \cont(σ_{n+1}) = ...\cont(σ_0))
  \]
  We notate maximal traces as $\maxtrace{(σ_i)_{i∈\overline{n}}}$.
  Infinite and interior traces are called \emph{diverging}.
  A maximally finite, but unbalanced trace is called \emph{stuck}.
\end{definition}

Note that usually stuckness is associated with a state of a transition
system rather than a trace.
That is not possible in our framework; the following example clarifies.

\begin{example}[Stuck and diverging traces]
Consider the interior trace
\[
             (\ttrue~x, [x↦\pa_1], [\pa_1↦...], κ)
  \smallstep (\ttrue, [x↦\pa_1], [\pa_1↦...], \ApplyF(\pa_1) \pushF κ)
\]
It is stuck, but its singleton suffix is balanced.
An example for a diverging trace where $ρ=[x↦\pa_1]$ and $μ=[\pa_1↦(ρ,x)]$ is
\[
  (\Let{x}{x}{x}, [], [], κ) \smallstep (x, ρ, μ, κ) \smallstep (x, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep ...
\]
\end{example}

\begin{lemmarep}[Characterisation of maximal traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is maximal if and only if it is balanced,
  diverging or stuck.
\end{lemmarep}
\begin{proof}
  $\Rightarrow$: Let $(σ_i)_{i∈\overline{n}}$ be maximal.
  If $n=ω$ is infinite, then it is diverging due to interiority, and if
  $(σ_i)_{i∈\overline{n}}$ is stuck, the goal follows immediately.
  So we assume that $(σ_i)_{i∈\overline{n}}$ is maximal, finite and not stuck,
  so it must be balanced by the definition of stuckness.

  $\Leftarrow$: Both balanced and stuck traces are maximal.
  A diverging trace $(σ_i)_{i∈\overline{n}}$ is interior and infinite,
  hence $n=ω$.
  Indeed $(σ_i)_{i∈\overline{ω}}$ is maximal, because the expression $σ_ω$
  is undefined and hence does not exist.
\end{proof}

Interiority guarantees that the particular initial stack $κ$ of a maximal trace
is irrelevant to execution, so maximal traces that differ only in the initial
stack are bisimilar.

One class of maximal traces is of particular interest:
The maximal trace starting in $\inj(\pe)$!
Whether it is infinite, stuck or balanced is the defining operational
characteristic of $\pe$.
If we can show that |eval e emp| distinguishes these behaviors of $\pe$, we
have proven it an adequate replacement for the LK transition system.

\begin{toappendix}
\Cref{fig:eval-correctness} shows the correctness predicate $\correct$ in
our endeavour to prove |eval| adequate at |D (ByNeed T)|.
It encodes that an \emph{abstraction} of every maximal LK trace can be recovered
by running |eval| starting from the abstraction of an initial state.

The family of abstraction functions makes precise the intuitive connection
between the semantic objects in |eval| and the syntactic objects in
the transition system.

We will sometimes need to disambiguate the clashing definitions from
\Cref{sec:interp} and \Cref{sec:problem}.
We do so by adorning semantic objects with a tilde, so |tm := αHeap μ :: Heap (ByNeed τ)|
denotes a semantic heap which in this instance is defined to be the abstraction
of a syntactic heap |μ|.
In a slight abuse of notation, we write |eval e tr tm| to mean |case eval e tr
of ByNeed (StateT m) -> m tm|, as if |ByNeed| and |StateT| were type synonyms.

Note first that $α_{\STraces}$ is defined by guarded recursion over
the LK trace, in the following sense:
We regard $(σ_i)_{i∈\overline{n}}$ as a Sigma type $\STraces \triangleq
∃n∈ℕ_ω.\ \overline{n} \to \States$, where $ℕ_ω$ is defined by guarded recursion
as |data ℕ_ω = Z || S (Later ℕ_ω)|.
Now $ℕ_ω$ contains all natural numbers (where $n$ is encoded as
|(S . pure{-"\!)^n "-} Z|) and the transfinite limit ordinal
|ω = S (pure (S (pure ...)))|.
We will assume that addition and subtraction are defined as on peano numbers,
where |ω + _ = _ + ω = ω|.
When $(σ_i)_{i∈\overline{n}} ∈ \STraces$ is an LK trace and $n > 1$, then
$(σ_{i+1})_{i∈\overline{n-1}} ∈ \later \STraces$ is the guarded tail of the
trace with an associated coinduction principle.

As such, the expression $\idiom{α_{\STraces}((σ_{i+1})_{i∈\overline{n-1}},κ)}$
has type |Later (T (Value (ByNeed T), Heap (ByNeed T)))|
(the $\later$ in the type of $(σ_{i+1})_{i∈\overline{n-1}}$ maps through
$α_{\STraces}$ via the idiom brackets).
Definitional equality $=$ on |T (Value (ByNeed T), Heap (ByNeed T))| is defined
in the obvious structural way by guarded recursion (as it would be if it was a
finite, inductive type).

\begin{figure}
\[\begin{array}{rcl}
  α_\Environments([\many{\px ↦ \pa_{\py,i}}]) & = & [\many{|x| ↦ |step (Lookup y) (fetch a_yi)|}] \\
  α_\Heaps([\many{\pa ↦ (ρ,\pe)}]) & = & [\many{|a| ↦ |memo a (eval e (αEnv ρ))|}] \\
  α_\States(\Lam{\px}{\pe},ρ,μ,κ) & = & |(Fun (\d -> eval e (ext (αEnv ρ) x d)), αHeap μ)| \\
  α_\States(K~\overline{\px},ρ,μ,κ) & = & |(Con k (map (αEnv ρ !) xs), αHeap μ)| \\
  α_\Events(σ) & = & \begin{cases}
    |Let1| & σ = (\Let{\px}{\wild}{\wild},\wild,μ,\wild), \pa_{\px,i} \not∈ \dom(μ) \\
    |App1| & σ = (\wild~\px,\wild,\wild,\wild) \\
    |Case1| & σ = (\Case{\wild}{\wild},\wild,\wild, \wild)\\
    |Lookup y| & σ = (\px,ρ,\wild,\wild), ρ(\px) = \pa_{\py,i} \\
    |App2| & σ = (\Lam{\wild}{\wild},\wild,\wild,\ApplyF(\wild) \pushF \wild) \\
    |Case2| & σ = (K~\wild, \wild, \wild, \SelF(\wild,\wild) \pushF \wild) \\
    |Update| & σ = (\pv,\wild,\wild,\UpdateF(\wild) \pushF \wild) \\
  \end{cases} \\
  α_{\STraces}((σ_i)_{i∈\overline{n}},κ) & = & \begin{cases}
    |Step ({-" α_\Events(σ_0) "-}) (idiom (αSTraces (lktrace, κ)))| & n > 0 \\
    |Ret ({-" α_\States(σ_0) "-})| & \ctrl(σ_0) \text{ value } \wedge \cont(σ_0) = κ \\
    |Ret Stuck| & \text{otherwise} \\
  \end{cases} \\
  \correct((σ_i)_{i∈\overline{n}}) & = & \maxtrace{(σ_i)_{i∈\overline{n}}} \Longrightarrow ∀((\pe,ρ,μ,κ) = σ_0).\ α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |eval e (αEnv ρ) (αHeap μ)| \\
\end{array}\]
\vspace{-1em}
\caption{Correctness predicate for |eval|}
  \label{fig:eval-correctness}
\end{figure}

The event abstraction function $α_\Events(σ)$ encodes how intensional
information from small-step transitions is retained as |Event|s.
Its semantics is entirely inconsequential for the adequacy result and we imagine
that this function is tweaked on an as-needed basis depending on the particular
trace property one is interested in capturing.
In our example, we focus on |Loookup| events that carry with them the |Name| of
the let binding from whence a heap binding came -- in a somewhat informal way,
we imagine that the semantics allocates addresses $\pa_{\px,i}$ in one arena per
syntactic let binding $\px$, so that we can find the name of the let binding
from the address at lookup sites.
Again, the neglect in formalism has no effect on the adequacy result, but we
will need to be more precise here when proving soundness of usage analysis,
where the contents of the |Name| are interpreted semantically.

Our first goal is to establish a few auxiliary lemmas showing what kind of
properties of LK traces are preserved by $α_{\STraces}$ and in which way.
Let us warm up by defining a length function on traces:
\begin{spec}
  len :: T a -> ℕ_ω
  len (Ret _)     = Z
  len (Step _ tl) = S (idiom (len tl))
\end{spec}
\begin{lemmarep}[Preservation of length]
  \label{thm:abs-length}
  Let $(σ_i)_{i∈\overline{n}}$ be a trace.
  Then $|len ({-" α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0)) "-})| = n$.
\end{lemmarep}
\begin{proof}
  This is quite simple to see and hence a good opportunity to familiarise
  ourselves with the concept of \emph{Löb induction}, the induction principle of
  guarded recursion.
  Löb induction arises simply from applying the guarded recursive fixpoint
  combinator to a proposition:
  \[
    \textsf{löb} = \fix : \forall P.\ (\later P \Longrightarrow P) \Longrightarrow P
  \]
  That is, we assume that our proposition holds \emph{later}, \eg
  \[
    IH ∈ (\later P \triangleq \later (
        \forall n ∈ ℕ_ω.\
        \forall (σ_i)_{i∈\overline{n}}.\
        |len ({-" α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0)) "-})| = n
      ))
  \]
  and use $IH$ to prove $P$.
  Let us assume $n$ and $(σ_i)_{i∈\overline{n}}$ are given, define
  $τ \triangleq α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0))$ and proceed by case analysis
  over $n$:
  \begin{itemize}
    \item \textbf{Case |Z|}: Then we have either
      |τ = Ret ({-" α_\States(σ_0) "-})| or |τ = Ret Stuck|, both of which map
      to |Z| under |len|.
    \item \textbf{Case |S (idiom m)|}: Then the
      first case of $α_\States$ applies, hence $τ = σ \cons τ^{\later}$ for some
      $σ∈\States, τ^{\later}∈\later \VTraces$.
      Now we apply the inductive hypothesis, as follows:
      Let $(σ_{i+1})_{i∈\overline{m}} ∈ \later \STraces$ be the guarded
      tail of the LK trace $(σ_i)_{i∈\overline{n}}$.
      Then we can apply $IH \aplater m \aplater (σ_{i+1})_{i∈\overline{m}}$ and
      get a proof for $\later (|len tl| = m)$.
      Now we can prove $n = |S (idiom m)| = |S (len tl)| = |len τ|$.
  \end{itemize}
\end{proof}

\begin{lemmarep}[Preservation of characteristic]
  \label{thm:abs-max-trace}
  Let $(σ_i)_{i∈\overline{n}}$ be a maximal trace.
  Then $α_{\STraces}((σ_i)_{i∈\overline{n}}, cont(σ_0))$ is ...
  \begin{itemize}
    \item ... infinite if and only if $(σ_i)_{i∈\overline{n}}$ is diverging
    \item ... ending with |Ret (Fun _)| or |Ret (Con _ _)| if and only if
          $(σ_i)_{i∈\overline{n}}$ is balanced
    \item ... ending with |Ret Stuck| if and only if $(σ_i)_{i∈\overline{n}}$ is stuck
  \end{itemize}
\end{lemmarep}
\begin{proof}
  The first point follows by a similar inductive argument as in \Cref{thm:abs-length}.

  In the other cases, we may assume that $n$ is finite.
  If $(σ_i)_{i∈\overline{n}}$ is balanced, then $σ_n$ is a return state with
  continuation $\cont(σ_0)$, so its control expression is a value.
  Then $α_{\STraces}$ will conclude with |Ret (αState _)|, and the latter is
  never |Ret Stuck|.
  Conversely, if the trace ended with |Ret (Fun _)| or |Ret (Con _ _)|,
  then $\cont(σ_n) = \cont(σ_0)$ and $\ctrl(σ_n)$ is a value, so
  $(σ_i)_{i∈\overline{n}}$ forms a balanced trace.
  The stuck case is similar.
\end{proof}

The previous lemma is interesting as it allows us to apply the classifying
terminology of interior traces to a |τ :: T a| that is an abstraction of a
\emph{maximal} LK trace.
For such a maximal |τ| we will say that it is balanced when it ends with
|Ret v| for a |v /= Stuck|, stuck if ending in |Ret Stuck| and diverging if
infinite.

We are now ready to prove the main correctness predicate:

\begin{theoremrep}[Correctness of |eval|]
  \label{thm:sem-correct}
  $\correct$ from \Cref{fig:sem-correctness} holds.
  That is, whenever $(σ_i)_{i∈\overline{n}}$ is a maximal LK trace with source
  state $(\pe,ρ,μ,κ)$, we have
  $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |eval e (αEnv ρ) (αHeap μ)|$.
\end{theoremrep}
\begin{proof}
By Löb induction, with $IH ∈ \later C$ as the hypothesis.

We will say that an LK state $σ$ is stuck if there is no applicable rule in the
transition system (\ie, the singleton LK trace $σ$ is maximal and stuck).

Now let $(σ_i)_{i∈\overline{n}}$ be a maximal LK trace with source state
$σ_0=(\pe,ρ,μ,κ)$ and let |τ = eval e (αEnv ρ) (αHeap μ)|.
Then the goal is to show $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |τ|$.
We do so by cases over $\pe$, abbreviating |tm := αHeap μ| and |tr := αEnv ρ|:
\begin{itemize}
  \item \textbf{Case $\px$}:
    Let us assume first that $σ_0$ is stuck. Then $\px \not∈ \dom(ρ)$ (because
    $\LookupT$ is the only transition that could apply), so
    |τ = Ret Stuck| and the goal follows from
    \Cref{thm:abs-max-trace}.

    Otherwise, $σ_1 \triangleq (\pe', ρ1, μ, \UpdateF(\pa) \pushF κ), σ_0 \smallstep σ_1$
    via $\LookupT$, and $ρ(\px) = \pa_{\py,i}, μ(\pa) = (ρ1, \pe')$.
    This matches the head of the action of |tr x|, which is of the form
    |step (Lookup y) (fetch a_yi)|.

    To show that the tails equate, it suffices to show that they equate \emph{later}.

    We can infer that |tm a_yi = memo a_yi (eval e' tr')| from the definition of
    $α_\Heaps$, so
    \begin{spec}
      fetch a_yi tm = tm a_yi tm = eval e' tr' tm >>= \case
        (Stuck,  tm') -> Ret (Stuck, tm')
        (val,    tm') -> Step Update (Ret (val, ext tm' a_yi (memo a_yi (return val))))
    \end{spec}

    (Recall that we don't bother mentioning |StateT| and |ByNeed| wrappings.)
    Let us define |tl := (idiom (eval e' tr' tm))| and apply the induction
    hypothesis $IH$ to the maximal trace starting at $σ_1$.
    This yields an equality
    \[
      IH \aplater (σ_{i+1})_{i∈\overline{m}} ∈ \idiom{α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\UpdateF(\pa) \pushF κ) = τ^{\later}}
    \]
    When |tl| is infinite, we are done. Similarly, if |tl| ends
    in |Ret Stuck| then the continuation of |>>=| will return |Ret Stuck|,
    indicating by \Cref{thm:abs-length} and \Cref{thm:abs-max-trace} that
    $(σ_{i+1})_{i∈\overline{n-1}}$ is stuck and hence $(σ_i)_{i∈\overline{n}}$
    is, too.

    Otherwise |tl| ends after $m-1$ |Step|s with |Ret (val,tmm)| and
    by \Cref{thm:abs-max-trace} $(σ_{i+1})_{i∈\overline{m}}$ is balanced; hence
    $\cont(σ_m) = \UpdateF(\pa) \pushF κ$ and $\ctrl(σ_m)$ is a value.
    So $σ_m = (\pv,ρ_m,μ_m,\UpdateF(\pa) \pushF κ)$ and the
    $\UpdateT$ transition fires, reaching $(\pv,ρ_m,μ_m[\pa ↦ (ρ_m, \pv)],κ)$
    and this must be the target state $σ_n$ (so $m = n-2$), because it remains
    a return state and has continuation $κ$, so $(σ_i)_{i∈\overline{n}}$ is
    balanced.
    Likewise, the continuation argument of |>>=| does a |Step Update| on
    |Ret (val,tmm)|, updating the heap.
    By cases on $\pv$ and the |Domain (D (ByNeed T))| instance we can see that
    \begin{spec}
         Ret (val,ext tmm a_yi (memo a_yi (return val)))
      =  Ret (val,ext tmm a_yi (memo a_yi (eval v trm)))
      =  αState σ_n
    \end{spec}
    and this equality concludes the proof.

  \item \textbf{Case $\pe~\px$}:
    The cases where $τ$ gets stuck or diverges before finishing evaluation of
    $\pe$ are similar to the variable case.
    So let us focus on the situation when |tl := (idiom (eval e tr tm))|
    returns and let $σ_m$ be LK state at the end of the balanced trace
    $(σ_{i+1})_{i∈\overline{m-1}}$ through $\pe$ starting in stack
    $\ApplyF(\pa) \pushF κ$.

    Now, either there exists a transition $σ_m \smallstep σ_{m+1}$, or it does
    not.
    When the transition exists, it must must leave the stack $\ApplyF(\pa)
    \pushF κ$ due to maximality, necessarily by an $\AppET$ transition.
    That in turn means that the value in $\ctrl(σ_m)$ must be a lambda
    $\Lam{\py}{\pe'}$, and $σ_{m+1} = (\pe',ρ_m[\py ↦ ρ(\px)],μ_m,κ)$.

    Likewise, |tl| ends in
    |αState σ_m = Ret (Fun (\d -> step App2 (eval e' (ext trm y d))), tmm)|
    (where $\tm_m$ corresponds to the heap in $σ_m$ in the usual way).
    The |fun| implementation of |Domain (D (ByNeed T))| applies the |Fun| value
    to the argument denotation |tr x|, hence it remains to show that
    |tl2 := eval e' (ext trm y (tr x)) tmm| is equal to
    $α_{\STraces}((σ_{i+m+1})_{i∈\overline{k}}, κ)$ \emph{later},
    where $(σ_{i+m+1})_{i∈\overline{k}}$ is the maximal trace starting at
    $σ_{m+1}$.

    We can apply the induction hypothesis to this situation.
    From this and our earlier equalities, we get
    $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |τ|$, concluding the proof of
    the case where there exists a transition $σ_m \smallstep σ_{m+1}$.

    When $σ_m \not\smallstep$, then $\ctrl(σ_m)$ is not a lambda, otherwise
    $\AppET$ would apply.
    In this case, |fun| gets to see a |Stuck| or |Con _ _| value, for which it
    is |Stuck| as well.

  \item \textbf{Case $\Case{\pe_s}{\Sel[r]}$}:
    Similar to the application and lookup case.

  \item \textbf{Cases $\Lam{\px}{\pe}$, $K~\many{\px}$}:
    The length of both traces is $n = 0$ and the goal follows by simple calculation.

  \item \textbf{Case $\Let{\px}{\pe_1}{\pe_2}$}:
    Let $σ_0 = (\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ)$.
    Then $σ_1 = (\pe_2, ρ1, μ',κ)$ by $\LetIT$, where $ρ1 = ρ[\px↦\pa_{\px,i}],
    μ' = μ[\pa_{\px,i}↦(ρ1,\pe_1)]$.
    Since the stack does not grow, maximality from the tail $(σ_{i+1})_{i∈\overline{n-1}}$
    transfers to $(σ_{i})_{i∈\overline{n}}$.
    Straightforward application of the induction hypothesis to
    $(σ_{i+1})_{i∈\overline{n-1}}$ yields the equality for the tail (after a bit
    of calculation for the updated environment and heap), which concludes the
    proof.
\end{itemize}
\end{proof}

\Cref{thm:sem-correct} and \Cref{thm:abs-max-trace} are the key to proving a
strong version of adequacy for |eval|, where $σ$ is defined to be a
\emph{final} state if $\ctrl(σ)$ is a value and $\cont(σ) = \StopF$.

\end{toappendix}

\begin{theoremrep}[Total adequacy of |eval|]
  \label{thm:sem-adequate}
  Let |τ := fmap fst (runByNeed (eval e emp)) :: T (Value (ByNeed T))|.
  \begin{itemize}
    \item
      |τ| ends with |Ret (Fun _)| or |Ret (Con _ _)| (is balanced) iff there
      exists a final state $σ$ such that $\inj(\pe) \smallstep^* σ$.
    \item
      |τ| ends with |Ret Stuck| (is stuck) iff there exists a non-final
      state $σ$ such that $\inj(\pe) \smallstep^* σ$ and there exists no $σ'$
      such that $σ \smallstep σ'$.
    \item
      |τ| is infinite |Step _ (Step _ ^^ ...)| (is diverging) iff for all $σ$ with
      $\inj(\pe) \smallstep^* σ$ there exists $σ'$ with $σ \smallstep σ'$.
    \item
      The |e :: Event| in every |Step e ^^ ...| occurrence in |τ| corresponds in
      the intuitive way to the matching small-step transition rule that was
      taken.
  \end{itemize}
\end{theoremrep}
\begin{proofsketch}
The main idea is to define an abstraction function $α_{\STraces}$ on maximal
small-step traces and show by coinduction that it distributes over |eval|, \eg,
the correctness relation
\[
  \correct((σ_i)_{i∈\overline{n}}) = \maxtrace{(σ_i)_{i∈\overline{n}}} \Longrightarrow ∀((\pe,ρ,μ,κ) = σ_0).\ α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |eval e (αEnv ρ) (αHeap μ)| \\
\]
holds for every small-step trace.
The abstraction function is exact regarding the diverging, balanced and stuck
characteristic.
The full proof is in the Appendix.
\end{proofsketch}
\begin{proof}
  There exists a maximal trace $(σ_i)_{i∈\overline{n}}$ starting
  from $σ_0 = \inj(\pe)$, and by \Cref{thm:sem-correct} we have
  $α_{\STraces}((σ_i)_{i∈\overline{n}},\StopF) = τ$.
  The correctness of |Event|s emitted follows directly from $α_\Events$.
  \begin{itemize}
    \item[$\Rightarrow$]
      \begin{itemize}
        \item
          If $(σ_i)_{i∈\overline{n}}$ is balanced, its target state $σ_n$
          is a return state that must also have the empty continuation, hence it
          is a final state.
        \item
          If $(σ_i)_{i∈\overline{n}}$ is stuck, it is finite and maximal, but not balanced, so its
          target state $σ_n$ cannot be a return state;
          otherwise maximality implies $σ_n$ has an (initial) empty continuation
          and the trace would be balanced. On the other hand, the only returning
          transitions apply to return states, so maximality implies there is no
          $σ'$ such that $σ \smallstep σ'$ whatsoever.
        \item
          If $(σ_i)_{i∈\overline{n}}$ is diverging, $n=ω$ and for every $σ$ with
          $\inj(\pe) \smallstep^* σ$ there exists an $i$ such that $σ = σ_i$ by
          determinism.
      \end{itemize}

    \item[$\Leftarrow$]
      \begin{itemize}
        \item
          If $σ_n$ is a final state, it has $\cont(σ) = \cont(\inj(\pe)) = []$,
          so the trace is balanced.
        \item
          If $σ$ is not a final state, $τ'$ is not balanced. Since there is no
          $σ'$ such that $σ \smallstep^* σ'$, it is still maximal; hence it must
          be stuck.
        \item
          Suppose that $n∈ℕ_ω$ was finite.
          Then, if for every choice of $σ$ there exists $σ'$ such that $σ
          \smallstep σ'$, then there must be $σ_{n+1}$ with $σ_n \smallstep
          σ_{n+1}$, violating maximality of the trace.
          Hence it must be infinite.
          It is also interior, because every stack extends the empty stack,
          hence it is diverging.
      \end{itemize}
  \end{itemize}
\end{proof}

\subsection{Sound Abstract Interpretation via Parametricity}

Given a ``concrete'' (but perhaps undecidable, infinite or coinductive)
semantics and a more ``abstract'' (but perhaps decidable, finite and inductive)
semantics, when does the latter \emph{conservatively approximate} the former?
This question of \emph{soundness} is a prominent in program analysis,
and \emph{Abstract Interpretation}~\citet{Cousot:21} provides a generic
framework to understand it via construction of a Galois connection
$(|D|, ≤) \galois{|α|}{|γ|} (|hat D|,⊑)$ between concrete and abstract partial
orders $≤,⊑$ that encodes the soundness condition.
E.g., when |α d ⊑ hat d| --- or, equivalently, |d ≤ γ (hat d)| --- then
this Galois connection expresses that |hat d| is a sound abstraction of |d|.
This theory comes to life when instantiating the concrete lattice to the set of
program traces, in which the set |set (eval e ρ :: D (ByName T))| can be
regarded as the most precise property of traces characterising the
evaluation of an expression |e| in an environment |ρ|.
In this case, the concrete order $≤$ really is subset inclusion $⊆$ and
soundness of the analysis is expressed as
\[\begin{array}{ll}
                      & |forall e ρ. (set (eval e ρ :: D (ByName T))) ⊆ γ (eval e (α << set << ρ) :: hat D)| \\
  \Longleftrightarrow & |forall e ρ. α (set (eval e ρ :: D (ByName T))) ⊑ eval e (α << set << ρ) :: hat D|.
\end{array}\]
This statement should be read as ``The concrete semantics implies the abstract
semantics up to concretisation''~\citet[p. 26]{Cousot:21}.
Note that this statement is conceivably more complex to show than the simple
statement |α d ⊑ hat d| that we derived it from, yet the process is almost
entirely mechanical, given that both applications of |eval| share a lot of
structure!

There are at least two ways to exploit this similarity in structure.
The first is to let the soundness criterion drive us to \emph{construct} a
abstract semantics from the concrete one and the Galois connection; Cousot calls
this process \emph{calculational design}~\citet{Cousot:21}.

But in our case, we already have a shared interpreter.
It would be far more economical to derive a Galois connection from concrete and
abstract class instances, prove sound approximation lemmas for each method of
these type class instances individually and get the soundness proof on |eval|
for free, without ever reasoning about shared structure!

What sounds to good to be true has first been demonstrated by
\citet{Backhouse:04}.
Their contribution is threefold:
\begin{itemize}
  \item
    The first is that they have shown how to systematically construct Galois
    connections of higher-order types (such as for |ρ :: Name :-> D| above) from
    Galois connections for base types (such as |D|).
    For example, given a Galois connection
    $(|D|, ≤) \galois{|α|}{|γ|} (|hat D|,⊑)$, there is a canonical way to
    construct a Galois connection
    $(|D -> D|, \dot{≤}) \galois{\dot{|α|}}{\dot{|γ|}} (|hat D -> hat D|, \dot{⊑})$
    simply by following the structure of types, in this case as
    |αdot f := α . f . γ|, which coincides with the canonical way for how to
    lift a Galois connection to monotone functions~\citet[TODO]{Nielson:99}.
    Similar constructions can be given for products, sums, polymorphic types and
    thus for the dictionary desugaring of Haskell 98 type class
    declarations~\citet{Hall:96}.
    We will denote abstraction functions thus derived with |αup| and omit |α| as
    well as its type when it is clear from context (\eg, its argument).
  \item
    Secondly, by appealing to parametricity~\citet{Reynolds:83} of Haskell's
    type system (its total subset we have used to define our framework in
    particular), the proof that the Galois connection thus systematically
    constructed is in fact a Galois connection follows by the \emph{Free
    Theorem}~\citet{Wadler:89,Ghani:16} of its type.
    I.e., defining $\mathcal{D} \triangleq |set ((d,hat d) || α d ⊑ hat d)|$,
    the Identity Extension Lemma~\citet[Lemma 3.2]{Ghani:16} applied to an
    arbitrary function pairing $(|f :: D -> D|, |hat f :: hat D -> hat D|)$ yields
    $(|f|,|hat f|) ∈ \denot{|d -> d|}_r(\mathcal{D})$, so for all |d|, |hat d| such
    that $(|d|, |hat d|) ∈ \mathcal{D}$, we have
    $(|f d|, |hat f (hat d)|) ∈ \mathcal{D}$.
    This proves that $(|αdot|,|γdot|)$ forms a Galois connection:
    \[\begin{array}{rllll}
      |αdot f|\mathrel{\dot{⊑}} |hat f| \Longleftrightarrow & |forall (hat d). f (γ (hat d)) ≤ γ ((hat f (hat d)))| \Longrightarrow |forall d. f (γ (α d)) ≤ γ ((hat f (α d)))| \\
                               \Longrightarrow     & |forall d. f d ≤ γ ((hat f (α d)))| \Longleftrightarrow |f| \mathrel{\dot{≤}} |γdot (hat f)| \\
    \end{array}\]
    Similar results follow for products, sums and polymorphic types, thus
    Haskell 98 type classes.
  \item
    When it is possible to extract a generic component that is shared by
    both abstract and concrete semantics, the soundness theorem follows
    from showing soundness for the non-shared components (\ie, type class
    instances) only.
\end{itemize}

The third point has recently been used to great effect in \citet{Keidel:18}.
Alas, the correctness criterion provided by parametricity is too weak, because
it goes just by the type and thus can't consider how the type class methods are
used.
The soundness criterion yielded by parametricity is a good starting point when
adjusting writing a denotational interpreter for a different language, though.
\sg{Clean up this bit about parametricity; what's it worth if we end up needing
a stronger lemma? A short para should be enough.}
Our soundness criterion can be stated as follows, using notation |eval3 c| to
indicate the invisible application of |eval| to the type class dictionary
|c :: C d|:

\begin{theoremrep}[Sound Abstract Interpretation]
\label{thm:sound-abs-int}
Let |D1|, |D2| be two domains such that there are instances |c1 :: C D1|,|c2 ::
C D2| for the constraint tuple |C d := (Trace d, Domain d, HasBind d)|,
and $(|D1|,≤) \galois{|α|}{|γ|} (|D2|,⊑)$ a Galois connection.
If the following soundness lemmas relating |c1| and |c2| hold,
\begin{itemize}
  \item |forall (e :: Event) (d :: D1). α (at step c1 e d) ⊑ at step c2 e (α d)|
  \item |α (at stuck c1) ⊑ at stuck c2|
  \item |forall (f :: D1 -> D1). α (at fun c1 f) ⊑ at fun c2 (α . f . γ)|
  \item |forall (d :: D1) (a :: D1). α (at apply c1 d a) ⊑ at apply c2 (α d) (α a)|
  \item |forall (k :: Tag) (ds :: [D1]). α (at con c1 k ds) ⊑ at con c2 k (map α ds)|
  \item |forall (d :: D1) (fs :: [(Tag, [D1] -> D1)]). α (sel d f) ⊑ sel (α d) [ (k, α . f . map γ) || (k, f) <- fs ]|
  \item |forall (rhs :: D1 -> D1) (body :: D1 -> D1). α (at bind c1 rhs body) ⊑ at bind c2 (α . rhs . γ) (α . body . γ)|%
\end{itemize}
then |eval3 c2 e (α << ρ)| is a sound abstract interpretation of |eval3 c1
e ρ| for all |e :: Exp| and |ρ :: Name :-> D1|, written
\[
  |forall (e :: Exp) (ρ :: Name :-> D1). α (eval3 c1 e ρ :: D1) ⊑ (eval3 c2 e (α << ρ) :: D2)|,
\]
if |αup c1 ⊑ c2|, that is, all methods of |c2| are sound abstractions of |c1|
according to |α|.
\end{theoremrep}
\begin{proof}
The Identity Extension Lemma applied to the type
|C d => Exp -> (Name :-> d) -> d| yields
\[
  (|eval3|,|eval3|) ∈ \denot{|forall d. C d => Exp -> (Name :-> d) -> d|}_r
\]
This simplifies to the following inference rule (note that $\mathcal{D}$ is just
universally quantified like any other variable):
\[
\inferrule*
  {(|c1|,|c2|) ∈ \denot{|C d|}_r(\mathcal{D}) \\
   (|dom ρ1 = dom ρ2| \wedge \forall |x|∈|dom ρ1|.\ (|ρ1 x|,|ρ2 x|) ∈ \mathcal{D})}
  {(|eval3 c1 e ρ1|,|eval3 c2 e ρ2|) ∈ \mathcal{D}}
\]
We instantiate this rule at $\mathcal{D} \triangleq |set ((d1,d2) || α d1 ⊑ d2)|$,
pick |ρ2 := αdot ρ1|, abbreviate |αup c1 ⊑ c2| (recall that |αup| is derived
from $\denot{|C d|}_r(\mathcal{D})$) and simplify to
\[
\inferrule*
  {|αup c1 ⊑ c2|}
  {|α (eval3 c1 e ρ1) ⊑ eval3 c2 e (α << ρ1)|}
\]
\end{proof}

As discussed above, the types dictate the definition of |αup|.
Applied to our type class algebra |C d|, \Cref{thm:sound-abs-int} turns into
the following simplified (\eg, with |αup| expanded) inference rule:
\footnote{We found it handy to double-check our result using the
``Free Theorems'' Web UI provided by
\url{https://free-theorems.nomeata.de/}~\citep{Boehme:07} to generate the free
theorem for the |eval| function, the type of which is simple enough to be
encoded in Haskell98.}
\[
\inferrule
  {%
   |forall (e :: Event) (d :: d1). α (at step c1 e d) ⊑ at step c2 e (α d)|\\\\
   |α (at stuck c1) ⊑ at stuck c2|\\\\
   |forall (f :: d1 -> d1). α (at fun c1 f) ⊑ at fun c2 (α . f . γ)|\\\\
   |forall (d :: d1) (a :: d1). α (at apply c1 d a) ⊑ at apply c2 (α d) (α a)|\\\\
   |forall (k :: Tag) (ds :: [d1]). α (at con c1 k ds) ⊑ at con c2 k (map α ds)|\\\\
   |forall (d :: d1) (fs :: [(Tag, [d1] -> d1)]). α (sel d f) ⊑ sel (α d) [ (k, α . f . map γ) || (k, f) <- fs ]|\\\\
   |forall (rhs :: d1 -> d1) (body :: d1 -> d1). α (at bind c1 rhs body) ⊑ at bind c2 (α . rhs . γ) (α . body . γ)|%
  }
  {|α (eval3 c1 e ρ) ⊑ eval3 c2 e (α << ρ)|}
\]
%if False
Input of https://free-theorems.nomeata.de/:

---

(Trace d, Domain d, HasBind d, Lat d) => Exp -> (Name -> d) -> d

---

type Name = String
type Tag = Int

data Exp = Var Name | App Exp Name | Lam Name Exp  |  ConApp Tag [Name] | Case Exp [Alt]
type Alt = (Tag,[Name],Exp)

data Event  =  Lookup Name | Update | App1 | App2
            |  Let1 | Case1 | Case2 | Let0

class Lat l where
  bottom :: l
  lub :: l -> l -> l

class Trace τ where
  step :: Event -> τ -> τ

class Domain d where
  stuck :: d
  fun :: (d -> d) -> d
  apply :: d -> d -> d
  con :: Tag -> [d] -> d
  select :: d -> [(Tag, [d] -> d)] ->  d

class HasBind d where
  bind :: (d -> d) -> (d -> d) -> d

---

Output:

forall t1,t2 in TYPES(Trace, Domain, HasBind, Lat), R in
REL(t1,t2), R respects (Trace, Domain, HasBind, Lat).
 forall x :: Exp.
  forall p :: [Char] -> t1.
   forall q :: [Char] -> t2.
    (forall y :: [Char]. (p y, q y) in R)
    ==> ((f_{t1} x p, f_{t2} x q) in R)

R respects Trace if
  forall x :: Event.
   forall (y, z) in R. (step_{t1} x y, step_{t2} x z) in R
R respects Domain if
  (stuck_{t1}, stuck_{t2}) in R
  forall p :: t1 -> t1.
   forall q :: t2 -> t2.
    (forall (x, y) in R. (p x, q y) in R)
    ==> ((fun_{t1} p, fun_{t2} q) in R)
  forall (x, y) in R.
   forall (z, v) in R. (apply_{t1} x z, apply_{t2} y v) in R
  forall x :: Int.
   forall (y, z) in lift{[]}(R). (con_{t1} x y, con_{t2} x z) in R
  forall (x, y) in R.
   forall (z, v) in lift{[]}(lift{(,)}(id,lift{[]}(R) -> R)).
    (select_{t1} x z, select_{t2} y v) in R
R respects HasBind if
  forall p :: t1 -> t1.
   forall q :: t2 -> t2.
    (forall (x, y) in R. (p x, q y) in R)
    ==> (forall r :: t1 -> t1.
          forall s :: t2 -> t2.
           (forall (z, v) in R. (r z, s v) in R)
           ==> ((bind_{t1} p r, bind_{t2} q s) in R))
R respects Lat if
  (bottom_{t1}, bottom_{t2}) in R
  forall (x, y) in R.
   forall (z, v) in R. (lub_{t1} x z, lub_{t2} y v) in R
%endif

The bottom line:
It suffices to show a total of 7 Lemmas per instantiation to prove an analysis
correct, and we never need to concern ourselves with the actual definition of
|eval| (unless a proof needs to reason about the context in which a method call
occurs).

%endif
\subsection{Soundness \wrt |D (ByName T)|}

Gist:
\begin{itemize}
  \item
    Recall \citet{Cousot:21} and \citet{Backhouse:04}. That is, given Galois
    connections on base types, one can construct a canonical Galois connections
    for higher-order types such as functions, products and sums, and hence
    type class dictionaries.
  \item
    Furthermore, given a parametrically polymorphic function definition such as
    |eval|, the type's free theorem ensures sound abstract interpretation,
    given that all inputs are proven sound abstract interpretations.
  \item
    We apply that to our setting to get a sufficient soundness condition for
    abstract interpretations of |eval|.
  \item
    We refine this condition for |D (ByName T)|, introducing trace abstraction
  \item
    We prove usage analysis sound \wrt |D (ByName T)| using the aforementioned soundness conditions.
  \item
    Given an analysis domain |hat d| that is sound \wrt |D (ByName T)|, what is a sufficient condition
    for it to be sound \wrt |D (ByNeed T)|?
    This will probably involve heap forcing lemmas and showing that heap forcing is preserved parametricity. ?
    This will be interesting.
\end{itemize}

Story:
\begin{itemize}
  \item
    Parametricity gives us |α (apply d a) ⊑ apply (α d) (α a)|.
    This is not useful for multiple reasons:
    \begin{enumerate}
      \item Lack of full abstraction: Summary mechanism often can't be proven
        correct for arbitrary |d| and |a|; we need to know \emph{at least}
        that |d := eval e ρ| for some |e|,|ρ|.
      \item Better yet: Knowing that |apply d a = d >>= \v -> apply (return v) a| in the concrete,
        we'd rather prove |step ev (apply d a) ⊑ apply (step ev d) a|
        and |α (apply (fun f) a) = α (f a) ⊑ apply (fun (α f)) (α a)|,
        separately.
        Again, to prove that we'd need to know that
        |f d := step App2 (eval body (ext ρ x d))| for some |body|,|ρ|,|x|,
        and also the induction hypothesis |forall e ρ. α (eval e ρ) ⊑ eval e (α << ρ)|.
        Otherwise, it would be impossible to relate |f| to |α f|.
      \item Even with the induction hypothesis thus available. It is inconvenient to conduct this proof with a \emph{concrete} |f|
        and |a|. We'd much rather prove |hat f (hat a) ⊑ apply (hat f) (hat a)|.
    \end{enumerate}
\end{itemize}


We now put the soundness result to bear by instantiating the concrete |D1| to
by-name semantics |D (ByName T)| and deriving an abstraction function capturing
trace properties from it, all the while leaving |D2| abstract.

Following \citet[page 253]{Nielson:99}, every representation function |β :: a -> b| into a
partial order yields a Galois connection between $(|Pow a|,⊆)$ and $(|b|,⊑)$:
\begin{code}
instance Trace τ => Trace (Pow τ) where step e (P ts) = P (setundef (step e τ | τ <- ts))
-- instance Domain τ => Domain (Pow τ) where ...
-- instance HasBind τ => HasBind (Pow τ) where ...
data Galois a b = (a -> b) :<->: (b -> a)
repr :: Lat b => (a -> b) -> Galois (Pow a) b
repr β = α :<->: γ where α (P as) = Lub (β a | a <- as); γ b = P (setundef (a | β a ⊑ b))
\end{code}
(While the concretisation function exists as a mathematical function, it is in
general impossible to compute.)
Every domain |D2| with instances |(Trace D2, Domain D2, Lat D2)| induces a
\emph{trace abstraction} |trace| via the following representation function,
and the |byName| abstraction is the fixpoint of that Galois connection modulo
|ByName| constructors (we write |powMap f| to map |f| over |Pow|ersets):
\begin{code}
type EnvD d = d
trace  ::  (Trace d, Domain d, Lat d)
       =>  Galois (Pow (D r)) d -> Galois (Pow (EnvD (D r))) d -> Galois (Pow (T (Value r))) d
trace (αD :<->: γD) (αE :<->: γE) = repr β where
  β (Ret Stuck)       = stuck
  β (Ret (Fun f))     = fun {-"\iffalse"-}""{-"\fi"-} (αD . powMap f . γE)
  β (Ret (Con k ds))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)
  β (Step e d)        = step e (β d)

env :: (Trace d, Domain d, HasBind d, Lat d) => Galois (Pow (EnvD (D (ByName T)))) d
env = untyped (repr β where β (Step (Lookup x) (eval e ρ)) = step (Lookup x) (eval e (β << ρ)))

byName :: (Trace d, Domain d, HasBind d, Lat d) => Galois (Pow (D (ByName T))) d
byName = (α . powMap unByName) :<->: (powMap ByName . γ) where α :<->: γ = trace byName env
\end{code}
A delightful consequence of fixing |byName| as the Galois connection in
\Cref{thm:soundness-abs-int} is that we rid ourselves of 4 trivial soundness
lemmas (proven by unfolding |byName|), and decomposing the remaining 3 lemmas
further:
\[
\inferrule
  {%
   |αD :<->: γ = byName|\\\\
   |forall d a. αD (apply d a) ⊑ apply (αD d) (αD a)|\\\\
   |forall d fs. αD (sel d fs) ⊑ sel (αD d) (αD << (. map γ) << fs)|\\\\
   |forall rhs body. αD (body (fix rhs)) ⊑ bind (αD . powMap rhs . γ) (αD . powMap body . γ)|%
  }
  {|αD (eval e ρ :: Pow (D (ByName T))) ⊑ (eval e (αD << ρ) :: D2)|}
\]
The reading is as follows: The first two lemmas prove correct the summary
mechanism that comes to fruition in |apply| and |select|, and |bind| implements
a particular fixpointing strategy each of which needs a separate correctness
proof.
(We decided not to inline the instance methods of |C (D (ByName T))|, because
they don't meaningfully simplify any further with |α|.)

Unfortunately, we suffer from a lack of full abstraction~\citet{Plotkin:77}:
Proving |α (apply d a) ⊑ apply (α d) (α a)|
is quite hard, because |f :: D -> D| might be \emph{any} function, introspecting
its argument in all sorts of ways.
But we are only ever using it on an |f| that satisfies $φ(f) \triangleq |exists
e ρ x. forall a. f a = step App2 (eval e (ext ρ x a))|$, and furthermore we may
assume |α (eval e (ext x a)) ⊑ eval e (α << (ext ρ x a))| by Löb induction.
It turns out that this characterisation is crucial for proving the
summary mechanism of usage analysis correct, as it allows us to apply
\Cref{thm:usage-squeezing}.

These assumptions could perhaps be encoded in a dependently-typed language
by formulating |eval| as an open recursive function, refining the type of
|fun| to |fun :: Σ (D -> D) φ -> D| (we did something similar in
\Cref{sec:totality} for the Agda encoding) and deriving the free theorem for
that function.
The recursion could then be closed with guarded/Löb |fix| after the fact.
In general, we could do this refinement for all type class operations,
reflecting ever more information from the definition of |eval| into its type;
the |φ| would thus enumerate all syntactic use sites of |fun|.
At this point, the use of parametricity to conclude the soundness proof is not
too different from writing a custom tactic for a theorem prover.
Alas, parametricity is hard to use without a tool verifying correct extraction
of theorems, so we prove the below lemma by hand.
However, parametricity is a strong argument that our approach can easily be
generalised to other denotational interpreters.

\begin{definition}[Syntactic by-name environments]
  Let |D| be a domain satisfying |Trace|,|Domain|,|HasBind| and |Lat|.
  We write |syn D d| (resp. |syne D ρ|) to say that the denotation |d| (resp.
  environment |ρ|) is \emph{syntactic}, which we define mutually recursive as
  \begin{itemize}
    \item |syn D d| if and only if |d| is of the form |Lub (step (Lookup x) (eval e ρ1 :: D) || Later (syn D ρ1))|, and
    \item |syne D ρ| if and only if for all |x|, |syn D (ρ x)|.
  \end{itemize}
  Furthermore, we take |syn D| to abbreviate the set of syntactic denotations
  |d| satisfying |syn D d|. Hence |d ∈ syn D| if and only if |syn D d|,
  and likewise for |ρ ∈ syne D|.
\end{definition}

Henceforth, we assume a refined definition of |Domain| and |HasBind| that
expects |syn D| where we pass around denotations that end up in an environment.
It is then easy to see that |eval e ρ| preserves |syne D| in recursive
invocations.

\begin{lemma}[By-name evaluation improves trace abstraction]
  \label{thm:eval-improves}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the following properties:
  \begin{itemize}
    \item \textup{\textsc{Step-App}} |forall ev d a. step ev (apply d a) ⊑ apply (step ev d) a|
    \item \textup{\textsc{Step-Sel}} |forall ev d a. step ev (select d a) ⊑ select (step ev d) a|
    \item \textup{\textsc{Beta-App}} |forall e (hat ρ) x (hat a). step App2 (eval e (ext (hat ρ) x (hat a))) ⊑ apply (eval (Lam x e) (hat ρ)) (hat a)|
    \item \textup{\textsc{Beta-Sel}} |forall k xs (hat ρ) alts. cont (alts ! k) (map (hat ρ !) xs) ⊑ sel (eval (ConApp k xs) (hat ρ)) (cont << alts)|
    \item \textup{\textsc{Name-Bind}} For all |x|,|e1|,|e2|,|hat ρ|, it is
      \begin{spec}
          step Let1 (eval e2 (ext (hat ρ) x (step (Lookup x) (kleeneFix (\d1 -> eval e1 (ext (hat ρ) x (step (Lookup x) d1)))))))
      ⊑   bind  (\(hat d1) -> eval e1 (ext (hat ρ) x (step (Lookup x) (hat d1)))) (\(hat d1) -> step Let1 (eval e2 (ext (hat ρ) x (hat d1))))
      \end{spec}
  \end{itemize}

  If |eval e ρ1 = many (step ev) (eval v ρ2)|,
  then |many (step ev) (eval v (αE << set << ρ2)) ⊑ eval e (αE << set << ρ1)|,
  where |αE :<->: γE = env|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    |eval x ρ1 = step (Lookup y) (eval e' ρ3) = many (step ev) (eval v ρ2)|
    for some |y|,|e'|,|ρ3|,
    so that |many ev = Lookup y : many ev1| for some |ev1| by determinism.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = Lookup y : many ev1| -}
        step (Lookup y) (many (step ev1) (eval v (βE << ρ2)))
    ⊑   {- Induction hypothesis at |ev1|, |ρ3| as above -}
        step (Lookup y) (eval e' (βE << ρ3))
    =   {- Refold |βE|, |ρ3 ! x| -}
        βE (ρ1 ! x)
    =   {- Refold |eval x (βE << ρ1)| -}
        eval x (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Lam|,|ConApp|: By reflexivity of $⊑$.
  \item \textbf{Case} |App e x|:
    Then |eval e ρ1 = many (step ev1) (eval (Lam y body) ρ3)|,
    |eval body (ext ρ3 y (ρ1 ! x)) = many (step ev1) (eval v ρ2)|.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    ⊑   {- |many ev = [App1] ++ many ev1 ++ [App2] ++ many ev2|, IH at |ev2| -}
        step App1 (many (step ev1) (step App2 (eval body (ext (βE << ρ3) y (βE << ρ1 ! x)))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        step App1 (many (step ev1) (apply (eval (Lam y body) (βE << ρ3)) (βE << ρ1 ! x)))
    ⊑   {- Assumption \textsc{Step-App} -}
        step App1 (apply (many (step ev1) (eval (Lam y body) (βE << ρ3))) (βE << ρ1 ! x))
    ⊑   {- Induction hypothesis at |ev1| -}
        step App1 (apply (eval e (βE << ρ1)) (βE << ρ1 ! x))
    =   {- Refold |eval (App e x) (βE << ρ1)| -}
        eval (App e x) (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Case e alts|:
    Then |eval e ρ1 = many (step ev1) (eval (ConApp k ys) ρ3)|,
    |eval er (exts ρ1 xs (map (ρ3 !) ys)) = many (step ev2) (eval v ρ2)|,
    where |alts ! k = (xs,er)| is the matching RHS.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    ⊑   {- |many ev = [Case1] ++ many ev1 ++ [Case2] ++ ev2|, IH at |ev2| -}
        step Case1 (many (step ev1) (step Case2 (eval er (βE << (exts ρ1 xs (map (hat ρ3 !) ys))))))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev1) (select (eval (ConApp k ys) (βE << ρ3)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (step ev1 (eval (ConApp k ys) (βE << ρ3))) (cont << alts))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Case1 (select (eval e (βE << ρ1)) (cont << alts))
    =   {- Refold |eval (Case e alts) (βE << ρ1)| -}
        eval (Case e alts) (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Let x e1 e2|:
    First note the following fixpoint abstraction property provable by Löb induction:
    \begin{spec}
        βE (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ1 x (step (Lookup x) d1)))))
    ⊑   {- |fix f = f (fix f)|, unfold |βE| -}
        step (Lookup x) (eval e1 (ext (βE << ρ1) x (βE (step (Lookup x) (fix (\d1 -> ...))))))
    ⊑   {- Property of least fixpoint -}
        step (Lookup x) (kleeneFix (\(hat d1) -> eval e1 (ext (βE << ρ1) x (βE (step (Lookup x) (hat d1))))))
    \end{spec}
    So every fixpoint in the concrete can be approximated by a least fixpoint in
    the abstract.
    We use this fact below:
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = Let1 : many ev1| -}
        step Let1 (many (step ev1) (eval v (βE << ρ2)))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (βE (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ1 x (step (Lookup x) d1))))))))
    ⊑   {- Property of least fixpoint -}
        step Let1 (eval e2 (ext (βE << ρ1) x (step (Lookup x) (kleeneFix (\(hat d1) -> eval e1 (ext (βE << ρ1) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Name-Bind} -}
        bind  (\(hat d1) -> eval e1 (ext ((βE << ρ1)) x (step (Lookup x) (hat d1))))
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE << ρ1)) x (hat d1))))
    =   {- Refold |eval (Let x e1 e2) (βE << ρ1)| -}
        eval (Let x e1 e2) (βE << ρ1)
    \end{spec}
\end{itemize}
\end{proof}

\begin{theoremrep}[Sound By-name Interpretation]
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|.
Then the following inference rule applies, proving |eval e (hat ρ) :: hat D| a
sound abstract by-name interpreter
\[
\inferrule
  {%
   |α :<->: γ = byName|\\ IH = |forall e1 ρ1. α (eval e1 ρ1) ⊑ eval e1 (α << ρ1)| \\\\
   |forall d f. α (d >>= f) ⊑ α d >>= α . f . γ|\\\\
   |forall ev d a. step ev (apply d a) ⊑ apply (step ev d) a|\\\\
   |forall a. stuck ⊑ apply stuck (α a)|\\ |forall fs. stuck ⊑ sel stuck fs|\\\\
   IH \Longrightarrow |forall e ρ a. α (apply (eval e ρ) a) ⊑ apply (eval e (α << ρ)) (α a)| \\\\
   IH \Longrightarrow |forall e ρ fs. α (sel (eval e ρ) fs) ⊑ sel (α (eval e ρ)) [ (k, α . f . map γ) || (k, f) <- fs ]| \\\\
   IH \Longrightarrow |forall rhs body. α (bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
                                                 (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))) ⊑ bind (α . rhs . γ) (α . body . γ)|%
  }
  {|α (eval e (γ << hat ρ) :: Pow (D (ByName T))) ⊑ (eval e (hat ρ) :: hat D)|}
\]
\end{theoremrep}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |α|; the regular case follows
    by |α . γ ⊑ id|.
  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        α (eval (Lam x body) (γ << hat ρ))
    =   {- Unfold |eval|, |α| -}
        fun (\(hat d) -> step App2 (α (eval body (γ << (ext (hat ρ) x (hat d))))))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> step App2 (eval body (ext (hat ρ) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (hat ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k ds|:
    \begin{spec}
        α (eval (ConApp k xs) (γ << hat ρ))
    =   {- Unfold |eval|, |α| -}
        con k (map ((α << γ << hat ρ) !) xs)
    ⊑   {- |α . γ ⊑ id| -}
        con k (map (hat ρ !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (hat ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    The stuck case follows by unfolding |α|.

    Otherwise, by the definition of |trace| in terms of a representation
    function |β|, it suffices to consider each trace in the powerset
    individually, so let us fix some |ρ| such that |β << ρ ⊑ hat ρ| and show the
    proposition for all such |ρ| to show it for |γ << hat ρ|.

    Our proof obligation can be simplified as follows
    \begin{spec}
        β (eval (App e x) ρ)
    =   {- Unfold |eval| -}
        β (apply (eval e ρ) (ρ ! x))
    =   {- Unfold |apply| -}
        β (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    \end{spec}

    When |eval e ρ| diverges, we have
    \begin{spec}
    =   {- |eval e ρ| diverges, unfold |β| -}
        step ev1 (step ev2 (...))
    ⊑   {- Assumption |step ev (apply d a) ⊑ apply (step ev d) a| -}
        apply (step ev1 (step ev2 (...))) (hat ρ ! x)
    =   {- Refold |β|, |eval e ρ| -}
        apply (β (eval e ρ)) (hat ρ ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (hat ρ)) (hat ρ ! x)
    =   {- Refold |eval| -}
        eval (App e x) (hat ρ)
    \end{spec}
    Otherwise, |eval e ρ| must produce a value |v|.
    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
    (resp. |d := con k (map β ds)|) and have
    \begin{spec}
        β (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |β| -}
        many (step ev) (β (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v| not |Fun|, unfold |β| -}
        many (step ev) stuck
    ⊑   {- Assumption |stuck ⊑ apply d a| where |d := stuck| or |d := con k (map β ds)| -}
        many (step ev) (apply d a)
    ⊑   {- Assumption |step ev (apply d a) ⊑ apply (step ev d) a| -}
        apply (many (step ev) d) (hat ρ ! x)
    =   {- Refold |β|, |eval e ρ| -}
        apply (β (eval e ρ)) (hat ρ ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (hat ρ)) (hat ρ ! x)
    =   {- Refold |eval| -}
        eval (App e x) (hat ρ)
    \end{spec}
    In the final case, we have |v = Fun f|, which must be the result of some
    call |eval (Lam y body) ρ1|; hence
    |f := \d -> step App2 (eval body (ext ρ1 y d))|.
    \begin{spec}
        β (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |β| -}
        many (step ev) (β (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v=Fun f|, with |f| as above; unfold |β| -}
        many (step ev) (step App2 (β (eval body (ext ρ1 y (ρ ! x)))))
    ⊑   {- |id ⊑ γ . α| -}
        many (step ev) (step App2 (α (eval body (γ << β (ext ρ1 y (ρ ! x))))))
    ⊑   {- Induction hypothesis, with |hat ρ1 := β << (ext ρ1 y (ρ ! x))| -}
        many (step ev) (step App2 (eval body (β << (ext ρ1 y (ρ ! x)))))
    =   {- |β << ρ ⊑ hat ρ| -}
        many (step ev) (step App2 (eval body (ext (β << ρ1) y (hat ρ ! x))))
    ⊑   {- Assumption |forall e (hat ρ) x (hat d). step App2 (eval e (ext (hat ρ) x (hat d))) ⊑ apply (eval (Lam x e) (hat ρ)) (hat d)| -}
        many (step ev) (apply (eval (Lam y body) (β << ρ1)) (hat ρ ! x))
    ⊑   {- Assumption |step ev (apply d a) ⊑ apply (step ev d) a| -}
        apply (many (step ev) (eval (Lam y body) (β << ρ1))) (hat ρ ! x)
    =   {- \Cref{thm:eval-improves} applied to |hat ρ|,|ρ|,|ρ1| -}
        apply (eval e (hat ρ)) (hat ρ ! x)
    =   {- Refold |eval| -}
        eval (App e x) (hat ρ ! x)
    \end{spec}
    \begin{spec}
        (α (eval e ρ) >> (fun (\(hat d) -> step App2 (eval e (ext (α << ρ1) x (hat d))))))
    ⊑
        eval e (α << ρ)
    \end{spec}

    In the final case, we have |v = Fun f|, which must be the result of some
    call |eval (Lam y body) ρ1|; hence
    |f := \d -> step App2 (eval body (ext ρ1 y d))|.
    \begin{spec}
        α (eval e (γ (hat ρ))) >>= \case Fun f -> f (γ (hat ρ ! x)); _ -> stuck)
    =   {- |eval e (γ (hat ρ)) = many (step ev) (return (Fun f))|, unfold |α| -}
        many (step ev) (α (return v >>= \case Fun f -> f (γ (hat ρ ! x)); _ -> stuck))
    =   {- |v=Fun f|, with |f| as above; unfold |α| -}
        many (step ev) (step App2 (α (eval body (ext ρ1 y (γ (hat ρ ! x))))))
    ⊑   {- |id ⊑ γ . α|, |hat ρ1 := α ρ1| so that |ρ1 ⊆ γ (hat ρ1)| -}
        many (step ev) (step App2 (α (eval body (γ << ext (hat ρ1) y (hat ρ ! x)))))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step App2 (eval body (ext (hat ρ1) y (hat ρ ! x))))
    ⊑   {- Assumption |forall e (hat ρ) x (hat d). step App2 (eval e (ext (hat ρ) x (hat d))) ⊑ apply (fun (\(hat d) -> step App2 (eval e (hat ρ)))) (hat d)| -}
        many (step ev) (apply (fun (\(hat d) -> step App2 (eval body (ext (hat ρ1) y (hat d))))) (hat ρ ! x))
    ⊑   {- Refold |eval (Lam y body) (hat ρ1)| -}
        many (step ev) (apply (eval (Lam y body) (hat ρ1)) (hat ρ ! x))
    ⊑   {- Assumption |step ev (apply d a) ⊑ apply (step ev d) a| -}
        apply (many (step ev) (eval (Lam y body) (hat ρ1))) ((hat ρ) ! x)
    =   {- \Cref{thm:eval-improves} TODO -}
        apply (eval e (hat ρ)) (hat ρ ! x)
    =   {- Refold |eval| -}
        eval (App e x) (hat ρ)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The stuck case follows by unfolding |α|.
    Otherwise, our proof obligation can be simplified as follows
    \begin{spec}
       α (eval (Case e alts) ρ)
    =  {- Unfold |eval| -}
       α (select (eval e ρ) fs)
    ⊑  {- Assumption about |select| -}
       select (eval e (α << ρ)) [ (k, α . f . map γ) || (k, f) <- fs ]
    ⊑  {- Induction hypothesis -}
       select (eval e (α << ρ)) [ (k, hat f . map (α . γ)) || (k, f) <- fs ]
    ⊑  {- |α . γ ⊑ id| -}
       select (eval e (α << ρ)) [ (k, hat f . map (α . γ)) || (k, f) <- fs ]
    =  {- Refold |eval| -}
       eval (Case e alts) (α << ρ)
    \end{spec}
  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
       α (eval (Let x e1 e2) ρ)
    =  {- Unfold |eval| -}
       α (bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
                (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1)))))
    =  {- Unfold |bind|, |α| -}
       step Let1 (α (eval e2 (ext ρ x (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1))))))))
    ⊑  {- Assumption about |bind| -}
       bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
             (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))
    =  {- Rearrange -}
       step Let1 (eval e2 (ext (α << ρ) x (step (Lookup x) (α (fix (\d -> eval e1 (ext ρ x (Step (Lookup x) d))))))))
    ⊑  {- |id ⊑ γ . α| -}
       step Let1 (eval e2 (ext (α << ρ) x (step (Lookup x) (α (fix (\d -> γ (α (eval e1 (ext ρ x (Step (Lookup x) d))))))))))
    \end{spec}
\end{itemize}
\end{proof}

\[
\inferrule
  {%
   |α :<->: γ = byName|\\\\
   |forall a. stuck ⊑ apply stuck (α a)|\\ |forall fs. stuck ⊑ sel stuck fs|\\\\
   |forall v ρ a. α (apply (eval e ρ) a) ⊑ apply (eval v (α << ρ)) (α a)|\\\\
   |forall e d a. step e (apply d a) ⊑ apply (step e d) a|\\\\
   |forall e d fs. step e (select d fs) ⊑ select (step e d) fs|\\\\
   |forall k ds fs. head [ f || (k',f) <- fs, k == k'] ds ⊑ select (con k ds) fs|\\\\
   |forall rhs body. α (body (fix rhs)) ⊑ bind (α . powMap rhs . γ) (α . powMap body . γ)|%
  }
  {|α (eval e ρ :: Pow (D (ByName T))) ⊑ (eval e (α << ρ) :: hat D)|}
\]

It is clear that we can't decompose our proof obligations any further without
fixing a particular instance |C D2|, so we will now prove usage analysis
(|UD| from \Cref{fig:abs-usg}) correct \wrt by-name semantics, by showing the
above three lemmas.

\begin{theoremrep} Usage Analysis as implemented by |UD| in \Cref{fig:abs-usg}
is sound \wrt |D (ByName T)|, that is,
\[
  |forall e ρ. α (set (eval e ρ :: D (ByName T))) ⊑ (eval e (α << set << ρ) :: UD) where α :<->: _ = byName|
\]
\end{theoremrep}
\begin{proofsketch}
It suffices to show the three soundness lemmas above.
It is customary to write |β = α . set|, which is equal to the representation
function in |trace|.
\begin{enumerate}
  \item |forall d a. β (apply d a) ⊑ apply (β d) (β a)|: \\
    By unfolding both definitions, we get the goal
    \[
      |forall d a. β (d >>= \case Fun f -> f a; _ -> stuck) ⊑ β d >> manify (β a)|
    \]
    and we show these by löb induction on |d|.
    \begin{itemize}
      \item \textbf{Case} |Step e d|:
        \begin{DispWithArrows*}[fleqn,mathindent=6em]
              & |β (Step e d >>= \case Fun f -> f a; _ -> stuck)|
              \Arrow{Unfold |β|} \\
          ={} & |step e (β (d >>= \case Fun f -> f a; _ -> stuck))|
              \Arrow{Monotonicity of |step|, IH} \\
          ⊑{} & |step e (manify (β a) >> β d)|
              \Arrow{|step| commutes with |>>|} \\
          ={} & |manify (β a) >> step e (β d)|
              \Arrow{Refold |β|} \\
          ={} & |manify (β a) >> β (Step e d)|
        \end{DispWithArrows*}
      \item \textbf{Case} |Ret v|:
        When |v /= Fun f|, |β (d >> stuck) = β d ⊑ manify (β a) >> β d|.
        Otherwise |v = Fun f| for some |f| and the goal is to prove
        \[
          |β (Ret (Fun f) >>= \case Fun f -> f a; _ -> stuck)| ⊑ |apply (β (Ret (Fun f))) (β a)|
        \]
        By the definition of Galois connections, this is equivalent to
        \[
          \{|Ret (Fun f) >>= \case Fun f -> f a; _ -> stuck|\} ⊆  |γ (apply (β (Ret (Fun f))) (β a))|
        \]
        \begin{DispWithArrows*}[fleqn,mathindent=6em]
              & |β (Ret (Fun f) >>= \case Fun f -> f a; _ -> stuck)|
              \Arrow{Simplify} \\
          ={} & |β (f a)|
              \Arrow{Galois} \\
          ⊑{} & |α (powMap f a)| \\
%              \Arrow{|f a| is of the form |step App2 (eval e (ext ρ x a))|} \\
%          ={} & |β (step App2 (eval e (ext ρ x a)))|
%              \Arrow{Unfold |β|, |step|} \\
%          ={} & |β (eval e (ext ρ x a))|
%              \Arrow{Apply \Cref{thm:usage-squeezing}} \\
%          ⊑{} & |β (step App2 (eval e (ext ρ x a)))|
%              \Arrow{Monotonicity of |step|, IH} \\
%          ⊑{} & |step e (β d >> ...)|
%              \Arrow{|step| associates with |>>|} \\
          ={} & |step e (β d) >> ...|
        \end{DispWithArrows*}
    \end{itemize}
\end{enumerate}
\end{proofsketch}
