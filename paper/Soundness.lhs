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

module Soundness where

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
import Abstractions
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

    Otherwise, $σ_1 \triangleq (\pe', ρ', μ, \UpdateF(\pa) \pushF κ), σ_0 \smallstep σ_1$
    via $\LookupT$, and $ρ(\px) = \pa_{\py,i}, μ(\pa) = (ρ', \pe')$.
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
    Let us define |tl := (idiom (eval e' tr' tm)| and apply the induction
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
    So let us focus on the situation when |tl := (idiom (eval e tr tm)|
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
    Then $σ_1 = (\pe_2, ρ', μ',κ)$ by $\LetIT$, where $ρ' = ρ[\px↦\pa_{\px,i}],
    μ' = μ[\pa_{\px,i}↦(ρ',\pe_1)]$.
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

\subsection{From Trace Property To Sound Abstract Interpreter}

%if style == newcode
\begin{code}
instance Eq (D (ByName T)) where
  (==) = undefined
instance Ord (D (ByName T)) where
  compare = undefined
powMap :: Ord b => (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ Set.fromList $ map f $ Set.toList s
\end{code}
%endif

\newcommand{\embAbsImpl}{| ι a || a <- as |}
\newcommand{\embConcImpl}{| a || a <- as, ι a ⊑ b |}
\begin{code}
data Galois a b = (a -> b) :<->: (b -> a)

fromEmbedding :: Lat b => (a -> b) -> Galois (Pow a) b
fromEmbedding ι = abs :<->: conc where
  abs   (P as)  = {-" \Lub \{ \embAbsImpl \} \iffalse "-} undefined {-" \fi "-}
  conc  b       = P {-" \{ \embConcImpl \} \iffalse "-} undefined {-" \fi "-}

byName :: (Trace τ, Domain (τ v), Lat (τ v)) => Galois (Pow (D (ByName T))) (τ v)
byName = g where
  g = fromEmbedding ι
  absF :<->: concF = fromMono g g
  ι (ByName d) = go d
  go (Ret Stuck)       = stuck
  go (Ret (Fun f))     = fun {-"\iffalse"-}""{-"\fi"-} (absF (powMap f))
  go (Ret (Con k ds))  = con {-"\iffalse"-}""{-"\fi"-} k (map ι ds)
  go (Step e τ)        = step e (go τ)

fromMono :: Galois a a' -> Galois b b' -> Galois (a -> b) (a' -> b')
fromMono (absA :<->: concA) (absB :<->: concB) = (\f -> absB . f . concA) :<->: (\f -> concB . f . absA)
\end{code}

\[
  |refold γ (eval e emp :: D (ByName T)) :: UD| ⊑ |eval e emp :: UD|
\]

\[\begin{array}{rcl}
  α([\many{\px ↦ \pa_{\py,i}}]) & = & [\many{|x| ↦ |step (Lookup y) (fetch a_yi)|}] \\
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
\end{array}\]
