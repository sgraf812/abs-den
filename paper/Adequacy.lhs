%if style == newcode
> module Adequacy where
%endif

\section{Totality and Semantic Adequacy}

In this section, I prove that |evalNeed2| produces small-step traces of the
lazy Krivine machine and is indeed a \emph{denotational semantics}.%
\footnote{Similar results for |evalName| and |evalVInit| should be derivative.}
Excitingly, to my knowledge, |evalNeed2| is the first denotational call-by-need
semantics that was proven so!

Specifically, denotational semantics must be total and adequate.
\emph{Totality} says that the interpreter is well-defined for every input expression and \emph{adequacy} says that the interpreter produces similar traces as the reference semantics.
This is an important result because it allows us to switch between operational reference semantics and denotational interpreter as needed, thus guaranteeing compatibility
of definitions such as absence in \Cref{defn:absence}.

I will start with an informal overview of the results in
\Cref{sec:adequacy,sec:totality} before giving a formal account culminating in
\Cref{sec:totality-formal,sec:adequacy-formal}.
As before, all the proofs can be found in the Appendix.

\subsection{Adequacy of |evalNeed2|}
\label{sec:adequacy}
%\sven{Section title makes readers believe that you only proved adequancy of |ByNeed|, but you did it for |ByName| as well, right?}
%\sg{No, just by-need, in fact.
%By-name should be much simpler, so I didn't bother.
%I guess we could very quickly whip something together based on the proof for
%by-need... After all, we'll just omit thunk update.
%But ultimately I think that is too simple an exercise to count as an interesting
%Contribution.}

For proving adequacy of |evalNeed2|, I give an abstraction function%
\footnote{More formally, I give a \emph{representation function}~\citep[Section 4.3]{Nielson:99} which induces a powerset-valued Galois connection.}
$α$ from small-step traces in the lazy Krivine machine (\Cref{fig:lk-semantics}) to
denotational traces |T|, with |Events| and all, such that
\[
  α(\init(\pe) \smallstep ...) = |evalNeed e emp emp|,
\]
where $\init(\pe) \smallstep ...$ denotes the \emph{maximal} (\ie longest
possible) LK trace evaluating the closed expression $\pe$.
For example, for the LK trace \labelcref{ex:trace2} on \cpageref{ex:trace2},
$α$ produces the trace at the end of
\hyperlink{ex:eval-need-trace2}{\Cref*{sec:by-need-instance}}
on \cpageref{ex:eval-need-trace2}.

It turns out that function $α$ preserves a number of important
observable properties, such as termination behavior (\ie stuck, diverging, or
balanced execution~\citep{Sestoft:97}), length of the trace and transition
events, as expressed in the following Theorem:
\pagebreak
\begin{theoremrep}[Strong Adequacy]
  \label{thm:need-adequate-strong}
  Let |e| be a closed expression, |τ := evalNeed e emp emp| the
  denotational by-need trace and $\init(\pe) \smallstep ...$ the maximal LK trace.
  Then
  \begin{itemize}
    \item |τ| preserves the observable termination properties of $\init(\pe) \smallstep ...$~.
    \item |τ| preserves the length of $\init(\pe) \smallstep ...$~.
    \item every |ev :: Event| in |τ = many (Step ev ^^ ...)| refers to a
      transition rule in $\init(\pe) \smallstep ...$~.
  \end{itemize}
\end{theoremrep}
\begin{proofsketch}
  Define $α$ by \emph{guarded recursion} and apply Löb induction to prove
  $α(\init(\pe) \smallstep ...) = |evalNeed e emp emp|$.
  Then it suffices to prove that $α$ preserves the observable properties of
  interest.
  The full proof appealing to \Cref{thm:need-abstracts-lk} can be found on
  \cpageref{proof:need-adequate-strong}.
\end{proofsketch}
\begin{proof}
  \pagetarget{proof:need-adequate-strong}{We} formally define $α(\init(\pe)
  \smallstep ...) \triangleq α_{\STraces}(\init(\pe) \smallstep ..., \StopF)$,
  where $α_{\STraces}$ is defined in \Cref{fig:eval-correctness}.

  Then $|evalNeed e emp emp| = α(\init(\pe) \smallstep ...)$ follows directly
  from \Cref{thm:need-abstracts-lk}.
  The preservation results are a consequence of \Cref{thm:abs-length,thm:need-adequate};
  function $α_\Events$ in \Cref{fig:eval-correctness} encodes the intuition in
  which LK transitions abstract into |Event|s.
\end{proof}

\subsection{Totality of |evalName| and |evalNeed2|}
\label{sec:totality}

\begin{theorem}[Totality]
The interpreters |evalName e ρ| and |evalNeed e ρ μ| are defined for every
|e|, |ρ|, |μ|.
\end{theorem}
\begin{proofsketch}
In the Appendix on \cpageref{sec:agda}, I provide an implementation of the generic
interpreter |eval| and its instances at |ByName| and |ByNeed| in Guarded
Cubical Agda, which offers a total type theory with \emph{guarded recursive
types}~\citep{tctt}.
Agda enforces that all encodable functions are total, therefore |evalName| and
|evalNeed2| must be total as well.

The essential idea of the totality proof is that \emph{there is only a finite
number of transitions between every $\LookupT$ transition}.
%\footnote{Our experiments with a denotational interpreter for
%PCF~\citep{Plotkin:77} indicate that this statement holds for PCF as well if
%$\UnrollT$ transitions introduced by the fixpoint operator were included.}
In other words, if every environment lookup produces a |Step| constructor, then
the semantics is total by coinduction.
Such an argument is quite natural to encode in guarded recursive types, hence
my use of Guarded Cubical Agda is appealing.
\end{proofsketch}

This concludes the high-level, informal discussion of adequacy and totality
results for |evalNeed2|.
We will now take a more in-depth tour to justify these claims.
This tour will start by recalling the limitations of inductive and coinductive
definitions when it comes to formalising programming language semantics in
\Cref{sec:limit-ind-coind}.
\Cref{sec:gtt} then explains how guarded recursive types address these
limitations and hence are a good fit to model denotational semantics.
Finally, \Cref{sec:totality-formal} will describe how |evalNeed2| can be encoded
in Guarded Cubical Agda.
While the previous three subsections motivate and introduce definitions by
guarded recursion in some detail, the adequacy proof in
\Cref{sec:adequacy-formal} showcases associated proofs by Löb induction.
I will use both guarded recursion and Löb induction extensively in many proofs
of \Cref{sec:soundness}.

\pagebreak

\subsection{Limitations of Induction and Coinduction}
\label{sec:limit-ind-coind}

Let us first recall what problem coinductive types solve and why
their use in formalisation is comparatively rare compared to inductive types.

It is common in functional programming languages and theorem provers to define
functions by recursion on an inductive data type parameter.
Such functions are automatically total, because inductive data is always of
finite depth, admitting a termination proof by \emph{well-founded induction} on
that depth.

But many total functions prevalent in lazy programming languages,
such as |map (+ 2) :: [Int] -> [Int]| in Haskell, \emph{are not recursive in
this sense}!
The reason for that is that lazy input data such as the infinite list |[1..]|
which evaluates to |[1,2,3,...]| can be of infinite depth, hence violating the
finite depth precondition.
That is, a direct proof by induction that |list := map (+ 2)
[1..]| is a total definition is not possible!
It \emph{is} total by \emph{coinduction}, though, because the definition
of |map (+ 2)| is \emph{productive}:
To evaluate |head list|, only a finite computation |(1 + 2)| needs to be carried
out, and similarly for |list !! 10|, or any finite prefix of |list|.
This is because the recursive call in the definition of |map| is \emph{guarded}
by the list constructor |(:)|:
\begin{spec}
  map f  (x:xs)  = f x  : map f xs
\end{spec}
While induction defines total objects (\eg functions, proofs) by
\emph{destructing} an inductive \emph{input} value,
coinduction defines total objects by \emph{constructing} a coinductive
\emph{output} value.
Induction permits recursive calls only on the \emph{input's parts} at
\emph{any position} in the function body, while coinduction permits recursive
calls only in \emph{guarded position}, such as in recursive fields of a
coinductive data constructor, but with \emph{any input} whatsoever.

It is fairly simple for a human or a computer to check what constitutes a
part of an inductive value and thus what is a valid inductive definition,
but it is far more complicated to check what constitutes a valid coinductive
definition.
Hence, although most theorem provers \emph{do} admit definitions by coinduction
such as |map| that satisfy simple syntactic productivity
checks~\citep{Coquand:94}, syntactic productivity is easily defeated by
refactorings such as extracting local bindings:
\begin{spec}
  map2 f  []      = []
  map2 f  (x:xs)  = f x  : rest
    where rest = map2 f xs
\end{spec}
Here, |rest| occurs in guarded position and hence the recursive call to
|map2| occurs in guarded position as well, but guardedness of the recursive
call is no longer syntactically evident and hence rejected by theorem provers
such as Rocq\footnote{Formerly Coq.} or Agda.

That is in constrast to inductive definitions, where it is simple to anticipate
the arguments of recursive calls.
The recursive call to |map2| is still decreasing in the input list, and it is
often simple enough to leave the code in a form where the decreasing recursive
call is evident.
So it is fair to say that \textbf{\emph{syntactic productivity checks are a severe
limitation}} of current implementations of coinduction and render coinductive
definitions far less useful than inductive definitions.

This is particularly embarassing for expressing dynamic processes such as
program semantics, because their natural implementation is in terms of
potentially infinite program traces which are best expressed coinductively.

In fact, our data type |T| is exactly such a coinductive data type, and hence
we would like |evalNeed2| to be a coinductive definition as well.
It is however impossible to show that |evalNeed2| syntactically guards all
its recursive calls, because we do not even see the |Step| constructor
syntactically in the definition of |eval|, only calls to the type class
method |step|!
Thus, to prove |evalNeed2| total by coinduction in Rocq or Agda, we would need to
manually specialise and inline many type class methods into |eval|.
Alas, any such manual transformation diminishes the confidence in the proof
method!

There is another limitation why |evalNeed2| cannot easily be proven total by
coinduction:
Recall that |D τ = τ (highlight Value τ)|.
Finite traces in the semantic domain |D (ByNeed T)| end in a |Value (ByNeed T)|,
and the data constructor |Fun :: (highlight (D τ) -> D τ) -> Value τ| has a
\textbf{\emph{negative recursive occurrence}} of |Value τ|!
This constructor is disallowed in inductive as well as traditional coinductive
data type definitions, which one reason why denotational semantics traditionally
made use of algebraic domain theory~\citep{Scott:70}, sized
types~\citep{Hughes:96} or other fuel-based encodings to prove totality.

\subsection{Guarded Type Theory}
\label{sec:gtt}

Fortunately, \emph{guarded type theories} both lift the syntactic productivity
restriction as well as allow restricted forms of negative recursion in data
types.

Guarded type theories postpone the productivity check to the type system, where
it becomes a \emph{semantic} instead of a \emph{syntactic} property.
This enables compositional reasoning about productivity, and of course stability
under type-preserving refactorings such as extraction of the |rest| auxiliary
definition in the revised implementation |map2| above.

The fundamental innovation of guarded recursive type theory is the integration
of the \emph{later} modality $\later$~\citep{Nakano:00} which allows to define
coinductive data types with negative recursive occurrences such as in the data
constructor |Fun| that we have identified as problematic above.

The way that is achieved is roughly as follows: The type $\later T$
represents data of type $T$ that will become available after a finite amount
of computation, such as unrolling one layer of a fixpoint definition or
one |(:)| constructor of an infinite stream such as |map (2 +) [1..]|.
While peeling off one layer is a finite computation, there may be an infinite
number of such layers in turn.
Consuming the entirety of such an infinite layering is impossible, but it
is possible to observe any finite prefix in a total manner.

The \emph{later} modality comes with a general fixpoint combinator
$\fix : \forall A.\ (\later A \to A) \to A$ that can be used to define both
coinductive \emph{types} (via guarded recursive functions on the universe
of types~\citep{BirkedalMogelbergEjlers:13}) as well as guarded recursive
\emph{terms} inhabiting said types.
The classic example is that of infinite streams:
\[
  \mathit{Str} = ℕ \times \later \mathit{Str} \qquad \mathit{ones} = \fix (r : \later \mathit{Str}).\ (1,r),
\]
where $\mathit{ones} : \mathit{Str}$ is the constant stream of $1$.
In particular, $\mathit{Str}$ is the fixpoint of a locally contractive functor $F(X) =
ℕ \times \later X$.
According to \citet{BirkedalMogelbergEjlers:13}, any type expression in simply
typed lambda calculus defines a locally contractive functor as long as any
occurrence of $X$ is under a $\later$.
The most exciting consequence is that changing the |Fun| data constructor to
|Fun :: (Later (D τ) -> D τ) -> Value τ| makes |Value τ| a well-defined type,%
\footnote{The reason why the positive occurrence of |D τ| does not need to be
guarded is that the type of |Fun| can more formally be encoded by a mixed
inductive-coinductive type, \eg
$|Value τ| = \fix X.\ \lfp Y.\ ...~||~|Fun|~(X \to Y)~||~...$ }
whereas traditional coinductive theories reject \emph{any} negative recursive
occurrence.

As a type constructor, $\later$ is an applicative
functor~\citep{McBridePaterson:08} via functions
\[
  \purelater : \forall A.\ A \to \later A \qquad \wild \aplater \wild : \forall A,B.\ \later (A \to B) \to \later A \to \later B,
\]
allowing us to apply a familiar framework of reasoning around $\later$.
In order not to obscure my work with pointless symbol pushing, I will often
omit the idiom brackets~\citep{McBridePaterson:08} $\idiom{\wild}$ to indicate
where the $\later$ ``effects'' happen.

\subsection{Total Encoding in Guarded Cubical Agda}
\label{sec:totality-formal}

The purpose of this subsection is to understand how |evalName| and
|evalNeed2| can be proved total by encoding them in Guarded Cubical Agda, which
implements Ticked Cubical Type Theory~\citep{tctt}.
The Agda code that documents this proof
can be found in the Appendix on \cpageref{sec:agda}.

To understand the Agda code, let me outline the changes necessary to encode
|eval| as well as the concrete instances |D (ByName T)| and |D (ByNeed T)| from
\Cref{fig:trace-instances,fig:by-need}.
\begin{itemize}
  \item We need to delay in |step|; thus its definition in |Trace| changes to
    |step :: Event -> Later d -> d|.
  \item
    All |D|s that will be passed to lambdas, put into the environment or
    stored in fields need to have the form |step (Look x) d| for some
    |x::Name| and a delayed |d :: Later (D τ)|.
    This is enforced as follows:
    \begin{enumerate}
      \item
        The |Domain d| type class gains an additional predicate parameter |p :: d -> Set|
        that will be instantiated by the semantics to a predicate that checks
        that the |d| has the required form |step (Look x) d| for some
        |x::Name|, |d :: Later (D τ)|.
      \item
        Then the method types of |Domain| use a Sigma type to encode conformance
        to |p|.
        For example, the type of |Fun| changes to |(Σ D p -> D) -> D|.
      \item
        The reason why we need to encode this fact is that the guarded recursive
        data type |Value| has a constructor the type of which amounts to
        |Fun :: (Name times Later (D τ) -> D τ) -> Value τ|, breaking the
        previously discussed negative recursive cycle by a $\later$, and
        expecting |x::Name|, |d::Later (D τ)| such that the original |D τ| can
        be recovered as |step (Look x) d|.
        This is in contrast to the original definition |Fun :: (D τ -> D τ) ->
        Value τ| which would \emph{not} type-check.
        One can understand |Fun| as carrying the ``closure'' resulting from
        \emph{defunctionalising}~\citep{Reynolds:72} a |Σ D p|, and that this
        defunctionalisation is presently necessary in Agda to eliminate negative
        cycles.
    \end{enumerate}
  \item
    Expectedly, |HasBind| becomes more complicated because it encodes the
    fixpoint combinator.
    I settled on |bind :: Later (Later D → D) → (Later D → D) → D|.
    (I tried rolling up |step (Look x) _| in the definition of |eval|
    to get a simpler type |bind :: (Σ D p → D) → (Σ D p → D) → D|,
    but then had trouble defining |ByNeed| heaps independently of the concrete
    predicate |p|.)
  \item
    Higher-order mutable state is among the classic motivating examples for
    guarded recursive types.
    As such it is no surprise that the state-passing of the mutable |Heap| in
    the implementation of |ByNeed| requires breaking of a recursive cycle
    by delaying heap entries, |Heap τ = Addr :-> Later (D τ)|.
  \item
    We need to pass around |Tick| binders in |eval| in a way that the type
    checker is satisfied; an exercise that is a bit more involved than one
    might expect, see the Appendix.
    Nevertheless, I find it remarkable how non-invasive these adjustment are!
    I had to conduct almost no proof external to the domain definition.
\end{itemize}

Thus I have proven that |eval| is a total, mathematical function, and
fast and loose equational reasoning about |eval| is not only \emph{morally}
correct~\citep{Danielsson:06}, but simply \emph{correct}.
Furthermore, since evaluation order doesn't matter in Agda or for |eval|,
I could have defined it in a strict language (lowering |Later a| as |() -> a|)
just as well.

\subsection{Proof of Adequacy For |evalNeed2|}
\label{sec:adequacy-formal}

We proceed from the bottom up, beginning with a definition of traces as
mathematical sequences, then defining maximal traces, and then relating
those maximal traces via \Cref{fig:eval-correctness} to |eval|.

Formally, an LK trace is a trace in $(\smallstep)$ from
\Cref{fig:lk-semantics}, \ie a non-empty and potentially infinite sequence of
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

Here is an example for each of the three cases.
We will omit the first component of heap entries in our examples because they
bear no semantic significance apart from instrumenting $\LookupT$ transitions,
and it is confusing when the heap-bound expression is a variable $x$, \eg $(y,ρ,x)$.
\begin{example}
  Let $ρ=[x↦\pa_1],μ=[\pa_1↦(\wild,[], \Lam{y}{y})]$ and $κ$ an arbitrary
  continuation. The trace
  \[
     (x, ρ, μ, κ) \smallstep (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is interior and balanced. Its proper prefixes are interior but not balanced.
  The trace suffix
  \[
     (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is neither interior nor balanced.
\end{example}

%We will say that the transition rules $\LookupT$, $\AppIT$, $\CaseIT$ and $\LetIT$
%are interior, because the lifting into a trace is, whereas the returning
%transitions $\UpdateT$, $\AppET$ and $\CaseET$ are not.

As shown by \citet{Sestoft:97}, a balanced trace starting at a control
expression $\pe$ and ending with $\pv$ loosely corresponds to a derivation of
$\pe \Downarrow \pv$ in a natural big-step semantics or a non-$⊥$ result in a
Scott-style denotational semantics.
It is when a derivation in a natural semantics does \emph{not} exist that a
small-step semantics shows finesse, in that it differentiates two different
kinds of \emph{maximally interior} (or, just \emph{maximal}) traces:

\begin{definition}[Maximal, diverging and stuck traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is \emph{maximal} if and only if it is
  interior and there is no $σ_{n+1}$ such that $(σ_i)_{i∈\overline{n+1}}$ is
  interior.
  More formally,
  \[
    \maxtrace{(σ_i)_{i∈\overline{n}}} \triangleq \interior{(σ_i)_{i∈\overline{n}}} \wedge (\not\exists σ_{n+1}.\ σ_n \smallstep σ_{n+1} \wedge \cont(σ_{n+1}) = ...\cont(σ_0)).
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
  \smallstep (\ttrue, [x↦\pa_1], [\pa_1↦...], \ApplyF(\pa_1) \pushF κ),
\]
where $\ttrue$ is a data constructor.
It is stuck, but its singleton suffix is balanced.
An example for a diverging trace, where $ρ=[x↦\pa_1]$ and $μ=[\pa_1↦(\wild,ρ,x)]$, is
\[
  (\Let{x}{x}{x}, [], [], κ) \smallstep (x, ρ, μ, κ) \smallstep (x, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep ...
\]
\end{example}

\begin{lemma}[Characterisation of maximal traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is maximal if and only if it is balanced,
  diverging or stuck.
\end{lemma}
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
This is very much like the semantics of a called function (\ie big-step
evaluator) may not depend on the contents of the call stack.

One class of maximal traces is of particular interest:
The maximal trace starting in $\init(\pe)$!
Whether it is infinite, stuck or balanced is the defining \emph{termination
observable} of $\pe$.
If we can show that |eval e emp| distinguishes these behaviors of |e|, we have
proven it an adequate replacement for the LK transition system.

\Cref{fig:eval-correctness} shows the correctness predicate $\correct$ in
our endeavour to prove |eval| adequate at |D (ByNeed T)|.
It encodes that an \emph{abstraction} of every maximal LK trace can be recovered
by running |eval| starting from the abstraction of an initial state.

The family of abstraction functions (they are really \emph{representation
functions}, in the sense of \Cref{sec:soundness}) makes precise the intuitive
connection between the definable entities in |eval| and the syntactic objects in
the transition system.

We will sometimes need to disambiguate the clashing definitions from
\Cref{sec:interp} and \Cref{sec:problem}.
We do so by adorning semantic objects with a tilde, so |tm := αHeap μ :: Heap (ByNeed τ)|
denotes a semantic heap which in this instance is defined to be the abstraction
of a syntactic heap |μ|.

Note first that $α_{\STraces}$ is defined by guarded recursion over
the LK trace, in the following sense:
We regard $(σ_i)_{i∈\overline{n}}$ as a Sigma type $\STraces \triangleq
∃n∈ℕ_ω.\ \overline{n} \to \States$, where $ℕ_ω$ is defined by guarded recursion
as |data ℕ_ω = Z || S (Later ℕ_ω)|.
Now $ℕ_ω$ contains all natural numbers (where $n$ is encoded as
|(S . pure{-"\!)^n "-} Z|) and the transfinite limit ordinal
|ω = S (pure (S (pure ...)))|.
We will assume that addition and subtraction are defined as on Peano numbers,
and |ω + _ = _ + ω = ω|.
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
  α_\Environments(μ, [\many{\px ↦ \pa}]) & = & [\many{|x| ↦ |Step (Look y) (fetch a)| \mid μ(\pa) = (\py,\wild,\wild)}] \\
  \hspace{-1em} α_\Heaps([\many{\pa ↦ (\wild,ρ,\pe)}]) & = & [\many{|a| ↦ |memo a (eval e (αEnv μ ρ))|}] \\
  α_\States(\Lam{\px}{\pe},ρ,μ,κ) & = & |(Fun (\d -> Step App2 (eval e (ext (αEnv μ ρ) x d))), αHeap μ)| \\
  α_\States(K~\overline{\px},ρ,μ,κ) & = & |(Con k (map (αEnv μ ρ !) xs), αHeap μ)| \\
  α_\Events(σ) & = & \begin{cases}
    |Let1| & \text{when }σ = (\Let{\px}{\wild}{\wild},\wild,μ,\wild), \pa_{\px,i} \not∈ \dom(μ) \\
    |App1| & \text{when }σ = (\wild~\px,\wild,\wild,\wild) \\
    |Case1| & \text{when }σ = (\Case{\wild}{\wild},\wild,\wild, \wild)\\
    |Look y| & \text{when }σ = (\px,ρ,μ,\wild), μ(ρ(\px)) = (\py,\wild,\wild) \\
    |App2| & \text{when }σ = (\Lam{\wild}{\wild},\wild,\wild,\ApplyF(\wild) \pushF \wild) \\
    |Case2| & \text{when }σ = (K~\wild, \wild, \wild, \SelF(\wild,\wild) \pushF \wild) \\
    |Upd| & \text{when }σ = (\pv,\wild,\wild,\UpdateF(\wild) \pushF \wild) \\
  \end{cases} \\
  α_{\STraces}((σ_i)_{i∈\overline{n}},κ) & = & \begin{cases}
    |Step ({-" α_\Events(σ_0) "-}) (idiom (αSTraces (lktrace, κ)))| & \text{when }n > 0 \\
    |Ret ({-" α_\States(σ_0) "-})| & \text{when }\ctrl(σ_0) \text{ value } \wedge \cont(σ_0) = κ \\
    |Ret Stuck| & \text{otherwise} \\
  \end{cases} \\
  \correct((σ_i)_{i∈\overline{n}}) & = & \maxtrace{(σ_i)_{i∈\overline{n}}} \Longrightarrow ∀((\pe,ρ,μ,κ) = σ_0).\ α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |evalNeed e (αEnv μ ρ) (αHeap μ)| \\
\end{array}\]
\vspace{-1em}
\caption{Correctness predicate for |eval|}
  \label{fig:eval-correctness}
\end{figure}

The event abstraction function $α_\Events(σ)$ encodes how intensional
information from small-step transitions is retained as |Event|s.
Its semantics is entirely inconsequential for the adequacy result and we imagine
that this function is tweaked on an as-needed basis depending on the particular
trace property one is interested in observing.
In our example, we focus on |Look y| events that carry with them the |y ::
Name| of the let binding that allocated the heap entry.
This event corresponds precisely to a $\LookupT(\py)$ transition, so $α_\Events(σ)$
maps $σ$ to |Look y| when $σ$ is about to make a $\LookupT(\py)$ transition.
In that case, the focus expression must be $\px$ and $\py$ is the first
component of the heap entry $μ(ρ(\px))$.
The other cases are similar.

Our first goal is to establish a few auxiliary lemmas showing what kind of
properties of LK traces are preserved by $α_{\STraces}$ and in which way.
Let us warm up by defining a length function on traces:
\begin{spec}
  len :: T a -> ℕ_ω
  len (Ret _)     = Z
  len (Step _ tl) = S (idiom (len tl))
\end{spec}
\begin{lemma}[Preservation of length]
  \label{thm:abs-length}
  Let $(σ_i)_{i∈\overline{n}}$ be a trace.
  Then $|len ({-" α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0)) "-})| = n$.
\end{lemma}
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
    \item \textbf{Case |S (idiom m)|}: Then
      |τ = Step _ ^^{-"\idiom{α_\STraces((σ_{i+1})_{i∈\overline{m}},\cont(σ_0))}"-}|,
      where $(σ_{i+1})_{i∈\overline{m}} ∈ \later \STraces$ is the guarded
      tail of the LK trace $(σ_i)_{i∈\overline{n}}$.
      Now we apply the inductive hypothesis, as follows:
      \[
        (IH \aplater m \aplater (σ_{i+1})_{i∈\overline{m}}) \in \later (|len ({-" α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\cont(σ_0)) "-})| = m).
      \]
      We use this fact and congruence to prove
      \[
         n = |S (idiom m)| = |S (len ({-" α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\cont(σ_0)) "-}))| = |len ({-" α_{\STraces}((σ_{i})_{i∈\overline{n}},\cont(σ_0)) "-})|.
      \]
  \end{itemize}
\end{proof}

\begin{lemma}[Abstraction preserves termination observable]
  \label{thm:abs-max-trace}
  Let $(σ_i)_{i∈\overline{n}}$ be a maximal trace.
  Then $α_{\STraces}((σ_i)_{i∈\overline{n}}, cont(σ_0))$ is ...
  \begin{itemize}
    \item ... ending with |Ret (Fun _)| or |Ret (Con _ _)| if and only if
          $(σ_i)_{i∈\overline{n}}$ is balanced.
    \item ... infinite if and only if $(σ_i)_{i∈\overline{n}}$ is diverging.
    \item ... ending with |Ret Stuck| if and only if $(σ_i)_{i∈\overline{n}}$ is stuck.
  \end{itemize}
\end{lemma}
\begin{proof}
  The second point follows by a similar inductive argument as in \Cref{thm:abs-length}.

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

We are now ready to prove the main soundness predicate, proving that |evalNeed2|
is an exact abstract interpretation of the LK machine:

\begin{theorem}[|evalNeed2| abstracts LK machine]
  \label{thm:need-abstracts-lk}
  $\correct$ from \Cref{fig:eval-correctness} holds.
  That is, whenever $(σ_i)_{i∈\overline{n}}$ is a maximal LK trace with source
  state $(\pe,ρ,μ,κ)$, we have
  $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |evalNeed e (αEnv μ ρ) (αHeap μ)|$.
\end{theorem}
\begin{proof}
By Löb induction, with $IH ∈ \later C$ as the hypothesis.

We will say that an LK state $σ$ is stuck if there is no applicable rule in the
transition system (\ie the singleton LK trace $σ$ is maximal and stuck).

Now let $(σ_i)_{i∈\overline{n}}$ be a maximal LK trace with source state
$σ_0=(\pe,ρ,μ,κ)$ and let |τ = evalNeed e (αEnv μ ρ) (αHeap μ)|.
Then the goal is to show $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |τ|$.
We do so by cases over $\pe$, abbreviating |tm := αHeap μ| and |tr := αEnv μ ρ|:
\begin{itemize}
  \item \textbf{Case $\px$}:
    Let us assume first that $σ_0$ is stuck. Then $\px \not∈ \dom(ρ)$ (because
    $\LookupT$ is the only transition that could apply), so
    |τ = Ret Stuck| and the goal follows from
    \Cref{thm:abs-max-trace}.

    Otherwise, $σ_1 \triangleq (\pe', ρ_1, μ, \UpdateF(\pa) \pushF κ), σ_0 \smallstep σ_1$
    via $\LookupT(\py)$, and $ρ(\px) = \pa, μ(\pa) = (\py, ρ_1, \pe')$.
    This matches the head of the action of |tr x|, which is of the form
    |step (Look y) (fetch a)|.

    To show that the tails equate, it suffices to show that they equate \emph{later}.

    We can infer that |tm a = memo a (evalNeed2 e' tr')| from the definition of
    $α_\Heaps$, so
    \begin{spec}
      fetch a tm = tm a tm = evalNeed e' tr' tm >>= \case
        (Stuck,  tm') -> Ret (Stuck, tm')
        (val,    tm') -> Step Upd (Ret (val, ext tm' a (memo a (return val))))
    \end{spec}

    Let us define |tl := (idiom (evalNeed e' tr' tm))| and apply the induction
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
    $\UpdateT$ transition fires, reaching $(\pv,ρ_m,μ_m[\pa ↦ (\py, ρ_m, \pv)],κ)$
    and this must be the target state $σ_n$ (so $m = n-2$), because it remains
    a return state and has continuation $κ$, so $(σ_i)_{i∈\overline{n}}$ is
    balanced.
    Likewise, the continuation argument of |>>=| does a |Step Upd| on
    |Ret (val,tmm)|, updating the heap.
    By cases on $\pv$ and the |Domain (D (ByNeed T))| instance we can see that
    \begin{spec}
         Ret (val,ext tmm a (memo a (return val)))
      =  Ret (val,ext tmm a (memo a (evalNeed2 v trm)))
      =  αState σ_n
    \end{spec}
    and this equality concludes the proof.

  \item \textbf{Case $\pe~\px$}:
    The cases where $τ$ gets stuck or diverges before finishing evaluation of
    $\pe$ are similar to the variable case.
    So let us focus on the situation when |tl := (idiom (evalNeed e tr tm))|
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
    |αState σ_m = Ret (Fun (\d -> step App2 (evalNeed2 e' (ext trm y d))), tmm)|
    (where $\tm_m$ corresponds to the heap in $σ_m$ in the usual way).
    The |fun| implementation of |Domain (D (ByNeed T))| applies the |Fun| value
    to the argument denotation |tr x|, hence it remains to show that
    |tl2 := evalNeed e' (ext trm y (tr x)) tmm| is equal to
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
    Then $σ_1 = (\pe_2, ρ_1, μ',κ)$ by $\LetIT$, where $ρ_1 = ρ[\px↦\pa_{\px,i}],
    μ' = μ[\pa_{\px,i}↦(\px,ρ_1,\pe_1)]$.
    Since the stack does not grow, maximality from the tail $(σ_{i+1})_{i∈\overline{n-1}}$
    transfers to $(σ_{i})_{i∈\overline{n}}$.
    Straightforward application of the induction hypothesis to
    $(σ_{i+1})_{i∈\overline{n-1}}$ yields the equality for the tail (after a bit
    of calculation for the updated environment and heap), which concludes the
    proof.
\end{itemize}
\end{proof}

\Cref{thm:need-abstracts-lk} and \Cref{thm:abs-max-trace} are the key to
proving the following theorem of adequacy, which formalises the intuitive
notion of adequacy from before.

(A state $σ$ is \emph{final} when $\ctrl(σ)$ is a value and $\cont(σ) = \StopF$.)

\begin{theorem}[Adequacy of |evalNeed2|]
  \label{thm:need-adequate}
  Let |τ := evalNeed e emp emp|.
  \begin{itemize}
    \item
      |τ| ends with |Ret (Fun _, _)| or |Ret (Con _ _, _)| (is balanced) iff there
      exists a final state $σ$ such that $\init(\pe) \smallstep^* σ$.
    \item
      |τ| ends with |Ret (Stuck, _)| (is stuck) iff there exists a non-final
      state $σ$ such that $\init(\pe) \smallstep^* σ$ and there exists no $σ'$
      such that $σ \smallstep σ'$.
    \item
      |τ| is infinite |Step _ (Step _ ^^ ...)| (is diverging) iff for all $σ$ with
      $\init(\pe) \smallstep^* σ$ there exists $σ'$ with $σ \smallstep σ'$.
    \item
      The |e :: Event| in every |Step e ^^ ...| occurrence in |τ| corresponds in
      the intuitive way to the matching small-step transition rule that was
      taken.
  \end{itemize}
\end{theorem}
\begin{proof}
  There exists a maximal trace $(σ_i)_{i∈\overline{n}}$ starting
  from $σ_0 = \init(\pe)$, and by \Cref{thm:need-abstracts-lk} we have
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
          $\init(\pe) \smallstep^* σ$ there exists an $i$ such that $σ = σ_i$ by
          determinism.
      \end{itemize}

    \item[$\Leftarrow$]
      \begin{itemize}
        \item
          If $σ_n$ is a final state, it has $\cont(σ) = \cont(\init(\pe)) = []$,
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
