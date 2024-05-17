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
    \setlength{\itemsep}{0pt}
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
  \setlength{\itemsep}{0pt}
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
fast and loose equational reasoning about |eval| is not only \emph{morally
correct}~\citep{Danielsson:06}, but simply \emph{correct}.
Furthermore, since evaluation order doesn't matter in Agda or for |eval|,
I could have defined it in a strict language (lowering |Later a| as |() -> a|)
just as well.

\subsection{Proof of Adequacy For |evalNeed2|}
\label{sec:adequacy-formal}

Building on the totality result for |evalNeed2|, I will prove in this subsection
that |evalNeed2| produces an abstraction of the small-step trace of the lazy
Krivine (LK) machine from \Cref{sec:op-sem}.
The main result is \Cref{thm:need-abstracts-lk}, from which the earlier
\Cref{thm:need-adequate-strong} in \Cref{sec:adequacy} follows.

To formalise the main result, I must characterise the maximal traces in the LK
transition system and relate them to the trace produced by |evalNeed2| via
the abstraction function in \Cref{fig:eval-correctness} and its associated
correctness relation.

\subsubsection{Maximal Lazy Krivine Traces}

Formally, an LK trace is a trace in $(\smallstep)$ from
\Cref{fig:lk-semantics}, \ie a non-empty and potentially infinite sequence of
LK states $(σ_i)_{i∈\overline{n}}$, such that $σ_i \smallstep σ_{i+1}$ for
$i,(i+1)∈\overline{n}$.
The \emph{length} of $(σ_i)_{i∈\overline{n}}$ is the potentially infinite
number of $\smallstep$ transitions $n$, where infinity is expressed by the first
limit ordinal $ω$.
The notation $\overline{n}$ means $\{ m ∈ ℕ \mid m \leq n \}$ when $n∈ℕ$
is finite (note that $0 ∈ ℕ$), and $ℕ$ when $n = ω$ is infinite.

The \emph{source} state $σ_0$ exists for finite and infinite traces, while the
\emph{target} state $σ_n$ is only defined when $n \not= ω$ is finite.
When the control expression of a state $σ$ (selected via $\ctrl(σ)$) is a value
$\pv$, we call $σ$ a \emph{return} state and say that the continuation (selected
via $\cont(σ)$) drives evaluation.
Otherwise, $σ$ is an \emph{evaluation} state and $\ctrl(σ)$ drives evaluation.

An important kind of trace is an \emph{interior trace}, one that never leaves
the evaluation context of its source state:

\begin{definition}[Deep]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is
  \emph{$κ$-deep} if every intermediate continuation $κ_i \triangleq
  \cont(σ_i)$ extends $κ$ (so $κ_i = κ$ or $κ_i = \wild \pushF κ$,
  abbreviated $κ_i = ...κ$).
\end{definition}

\begin{definition}[Interior]
  A trace $(σ_i)_{i∈\overline{n}}$ is called \emph{interior} (notated as
  $\interior{(σ_i)_{i∈\overline{n}}}$) if it is $\cont(σ_0)$-deep.
\end{definition}

A \emph{balanced trace}~\citep{Sestoft:97} is an interior trace that is about to
return from the initial evaluation context; it corresponds to a big-step
evaluation of the initial focus expression:

\begin{definition}[Balanced]
  An interior trace $(σ_i)_{i∈\overline{n}}$ is
  \emph{balanced} if the target state exists and is a return
  state with continuation $\cont(σ_0)$.
\end{definition}

In the following I give an example for interior and balanced traces.
I will omit the first component of heap entries in the examples because they
bear no semantic significance apart from instrumenting $\LookupT$ transitions,
and it is confusing when the heap-bound expression is a variable $x$,
\eg $(y,ρ,x)$.
Of course, the abstraction function in \Cref{fig:eval-correctness} will need to
look at the first component.
\begin{example}
  Let $ρ=[x↦\pa_1],μ=[\pa_1↦(\wild,[], \Lam{y}{y})]$ and $κ$ an arbitrary
  continuation. The trace
  \[
     (x, ρ, μ, κ) \smallstep (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is interior and balanced. Its proper prefixes are interior but not balanced.
  The suffix
  \[
     (\Lam{y}{y}, ρ, μ, \UpdateF(\pa_1) \pushF κ) \smallstep (\Lam{y}{y}, ρ, μ, κ)
  \]
  is neither interior nor balanced.
\end{example}

As shown by \citet{Sestoft:97}, a balanced trace starting at a control
expression $\pe$ and ending with $\pv$ corresponds to a derivation of $\pe
\Downarrow \pv$ in a big-step semantics or a non-$⊥$ result in a Scott-style
denotational semantics.
It is when a derivation in a big-step semantics does \emph{not} exist that a
small-step semantics shows finesse.
In this case, a small-step semantics differentiates two different kinds
of \emph{maximally interior} (or, just \emph{maximal}) traces, namely
\emph{diverging} and \emph{stuck} traces:

\begin{definition}[Maximal]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is \emph{maximal} if and only if it is
  interior and there is no $σ_{n+1}$ such that $(σ_i)_{i∈\overline{n+1}}$ is
  interior.
  More formally,
  \[
    \maxtrace{(σ_i)_{i∈\overline{n}}} \triangleq \interior{(σ_i)_{i∈\overline{n}}} \wedge (\not\exists σ_{n+1}.\ σ_n \smallstep σ_{n+1} \wedge \cont(σ_{n+1}) = ...\cont(σ_0)).
  \]
\end{definition}

\begin{definition}[Diverging]
  An infinite and interior trace is called \emph{diverging}.
\end{definition}

\begin{definition}[Stuck]
  A finite, maximal and unbalanced trace is called \emph{stuck}.
\end{definition}

Usually, stuckness is associated with a state of a transition
system rather than a trace.
That is not possible in our framework; the following example clarifies.

\begin{example}[Stuck and diverging traces]
\label{ex:stuck-div}
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

Note that balanced traces are maximal traces as well.
In fact, balanced, diverging and stuck traces are the \emph{only} three kinds of
maximal traces, as the following lemma formalises:

\begin{lemmarep}[Characterisation of maximal traces]
  An LK trace $(σ_i)_{i∈\overline{n}}$ is maximal if and only if it is balanced,
  diverging or stuck.
\end{lemmarep}
\begin{proof}
$ $
\begin{itemize}
\item[$\Rightarrow$:]
  Let $(σ_i)_{i∈\overline{n}}$ be maximal.
  Then it is interior by definition.
  Thus, if $n=ω$ is infinite, then it is diverging.
  Otherwise, $(σ_i)_{i∈\overline{n}}$ is finite.
  If it is \emph{not} balanced, then it is still maximal and finite, hence stuck.
  Otherwise, it is balanced.

\item[$\Leftarrow$:]
  Let $(σ_i)_{i∈\overline{n}}$ be balanced, diverging or stuck. \\
  If $(σ_i)_{i∈\overline{n}}$ is balanced, then it is interior, and $σ_n$ is
  a return state with continuation $\cont(σ_0)$.
  Now suppose there would exist $σ_{n+1}$ such that
  $(σ_i)_{i∈\overline{n+1}}$ was interior.
  Then the transition $σ_n \smallstep σ_{n+1}$ must be one of the
  \emph{returning transition rules} $\UpdateT$, $\AppET$ and $\CaseET$, which
  are the only ones in which $σ_n$ is a return state (\ie $\ctrl(σ_n)$ is a
  value $\pv$).
  But all return transitions leave $\cont(σ_0)$, which is in contradiction to
  interiority of $(σ_i)_{i∈\overline{n+1}}$.
  Thus, $(σ_i)_{i∈\overline{n}}$ is maximal. \\
  If $(σ_i)_{i∈\overline{n}}$ is diverging, it is interior and infinite,
  hence $n=ω$.
  Indeed $(σ_i)_{i∈\overline{ω}}$ is maximal, because the expression $σ_{ω+1}$
  is undefined and hence does not exist. \\
  If $(σ_i)_{i∈\overline{n}}$ is stuck, then it is maximal by definition.
\end{itemize}
\end{proof}

Interiority guarantees that the particular initial stack $\cont(σ_0)$ of a
maximal trace is irrelevant to execution, so maximal traces that differ only in
the initial stack are bisimilar.
This is a consequence of the fact that the semantics of a called function may
not depend on the contents of the call stack; this fact is encoded implicitly in
big-step derivations.

\subsubsection{Abstraction preserves Termination Observable}

One class of maximal traces is of particular interest:
the maximal trace starting in $\init(\pe)$!
Whether it is infinite, stuck or balanced is the semantically defining
\emph{termination observable} of $\pe$.
If we can show that |evalNeed e emp emp| distinguishes these behaviors of
$\init(\pe) \smallstep ...$, we have proven |evalNeed2| \emph{adequate}, and may
use it as a replacement for the LK transition system.

In order to show that |evalNeed2| preserves the termination observable of |e|,
\begin{itemize}
\setlength{\itemsep}{0pt}
\item
  I define a family of abstraction functions $α$ from LK traces to by-need
  traces, formally in |T (Value (ByNeed T), Heap (ByNeed T))| (\Cref{fig:eval-correctness}),
\item
  I show that this function $α$ preserves the termination observable of a given
  LK trace $\init(\pe) \smallstep ...$ (\Cref{thm:abs-max-trace}), and
\item
  I show that running |evalNeed e emp emp| is the same as mapping $α$ over
  the LK trace $\init(\pe) \smallstep ...$, hence the termination behavior is
  observable (\Cref{thm:need-abstracts-lk}).
\end{itemize}

In the following, I will omit repeated wrapping and unwrapping of the |ByNeed|
newtype wrapper when constructing and taking apart elements in |D (ByNeed T)|.
Furthermore, I will sometimes need to disambiguate the clashing definitions from
\Cref{sec:interp} and \Cref{sec:problem} by adorning ``Haskell objects'' with a
tilde, in which case |tm := αHeap μ :: Heap (ByNeed T)| denotes a semantic
by-need heap, defined as an abstraction of a syntactic LK heap $μ ∈ \Heaps$.

\begin{figure}
\hfuzz=1em
\[\ruleform{\begin{array}{c}
  α_\Events : \States \to |Event|
  \qquad
  α_\Values : \States \to |(Value (ByNeed T), Heap (ByNeed T))|
  \\
  α_\Environments : \Heaps \times \Environments \to |Heap (ByNeed T)|
  \qquad
  α_\Heaps : \Heaps \to |Heap (ByNeed T)|
  \\
  α_{\STraces} : \STraces \times \Continuations \to |T (Value (ByNeed T), Heap (ByNeed T))|
\end{array}}\]
\arraycolsep=2pt
\[\begin{array}{rcl}
  α_\Events(σ) & = & \begin{cases}
    |Let1| & \text{if }σ = (\Let{\px}{\wild}{\wild},\wild,\wild,\wild) \\
    |App1| & \text{if }σ = (\pe~\px,\wild,\wild,\wild) \\
    |Case1| & \text{if }σ = (\Case{\wild}{\wild},\wild,\wild, \wild)\\
    |Look y| & \text{if }σ = (\px,ρ,μ,\wild), μ(ρ(\px)) = (\py,\wild,\wild) \\
    |App2| & \text{if }σ = (\Lam{\wild}{\wild},\wild,\wild,\ApplyF(\wild) \pushF \wild) \\
    |Case2| & \text{if }σ = (K~\wild, \wild, \wild, \SelF(\wild,\wild) \pushF \wild) \\
    |Upd| & \text{if }σ = (\pv,\wild,\wild,\UpdateF(\wild) \pushF \wild) \\
  \end{cases} \\
  α_\Values(\Lam{\px}{\pe},ρ,μ,κ) & = & |(Fun (\d -> Step App2 (eval e (ext (αEnv μ ρ) x d))), αHeap μ)| \\
  α_\Values(K~\overline{\px},ρ,μ,κ) & = & |(Con k (map (αEnv μ ρ !) xs), αHeap μ)| \\
  α_\Environments(μ, [\many{\px ↦ \pa}]) & = & [\many{|x| ↦ |Step (Look y) (fetch a)| \mid μ(\pa) = (\py,\wild,\wild)}] \\
  \hspace{-1em}
  α_\Heaps([\many{\pa ↦ (\wild,ρ,\pe)}]) & = & [\many{|a| ↦ |memo a (eval e (αEnv μ ρ))|}] \\
  α_{\STraces}((σ_i)_{i∈\overline{n}},κ) & = & \begin{cases}
    |Step ({-" α_\Events(σ_0) "-}) τl| & \text{if }n > 0, |τl = idiom (αSTraces (lktrace, κ))| \\
    |Ret ({-" α_\Values(σ_0) "-})| & \text{if }\ctrl(σ_0) \text{ value } \wedge \cont(σ_0) = κ \\
    |Ret Stuck| & \text{otherwise}
  \end{cases}
\end{array}\]
\caption{Abstraction functions for |evalNeed2|}
  \label{fig:eval-correctness}
\end{figure}

Now consider the trace abstraction function $α_{\STraces}$ from
\Cref{fig:eval-correctness}.
It maps syntactic entities in the transition system to the definable entities
in the denotational by-need trace domain |T (Value (ByNeed T), Heap (ByNeed
T))|, henceforth abbreviated as |T| because it is the only use of the type
constructor |T| in this subsection.

$α_{\STraces}$ is defined by guarded recursion over the LK trace, in the
following sense:
We regard $(σ_i)_{i∈\overline{n}}$ as a dependent pair type $\STraces
\triangleq ∃n∈ℕ_ω.\ \overline{n} \to \States$, where $ℕ_ω$ is defined
by guarded recursion as |data ℕ_ω = Z || S (Later ℕ_ω)|.
Now $ℕ_ω$ contains all natural numbers (where $n$ is encoded as
|(S . next{-"\!)^n~"-} Z|) and the transfinite limit ordinal
|ω = fix (S . next)|.
We will assume that addition and subtraction are defined as on Peano numbers,
and |ω + _ = _ + ω = ω|.
When $(σ_i)_{i∈\overline{n}} ∈ \STraces$ is an LK trace and $n > 1$, then
$(σ_{i+1})_{i∈\overline{n-1}} ∈ \later \STraces$ is the guarded tail of the
trace.

As such, the expression $\idiom{α_{\STraces}((σ_{i+1})_{i∈\overline{n-1}},κ)}$
has type |Later T|, where the $\later$ in the type of
$(σ_{i+1})_{i∈\overline{n-1}}$ maps through $α_{\STraces}$ via the idiom
brackets.
Definitional equality $=$ on |T| is defined in the obvious structural way by
guarded recursion (as it would be if it was a finite, inductive type).

Function $α_{\STraces}$ expects an LK trace as well as a continuation parameter
$κ$ that remains constant; it is initialised to the continuation of the initial
state $\cont(σ_0)$ in order to detect return states.

The event abstraction function $α_\Events(σ)$ encodes how intensional
information from small-step transitions is retained as |Event|s.
Its implementation does not influence the adequacy result, and we imagine
that this function is tweaked on an as-needed basis to retain more or less
intensional detail, depending on the particular trace property one is interested
in observing.
In our example, we focus on |Look y| events that carry with them the |y ::
Name| of the let binding that allocated the heap entry.
This event corresponds precisely to a $\LookupT(\py)$ transition, so $α_\Events(σ)$
maps $σ$ to |Look y| when $σ$ is about to make a $\LookupT(\py)$ transition.
In that case, the focus expression must be $\px$, and $\py$ is the first
component of the heap entry $μ(ρ(\px))$.
The other cases are similar.

I will now establish a few auxiliary lemmas showing what kind of
properties of LK traces are preserved by $α_{\STraces}$, and in which way.
Let us warm up by defining a length function on traces:
\begin{spec}
  len :: T a -> ℕ_ω
  len (Ret _)     = Z
  len (Step _ τl) = S (idiom (len τl))
\end{spec}
The length is an important property of LK traces that is preserved by $α$.
\begin{lemma}[Abstraction preserves length]
  \label{thm:abs-length}
  Let $(σ_i)_{i∈\overline{n}}$ be a trace. Then
  \[ |len ({-" α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0)) "-})| = n. \]
\end{lemma}
\begin{proof}
  This is quite simple to see and hence a good opportunity to familiarise
  ourselves with Löb induction, the induction principle of guarded recursion.
  Löb induction arises simply from applying the guarded recursive fixpoint
  combinator to a proposition:
  \[
    \textsf{löb} = \fix : \forall P.\ (\later P \Longrightarrow P) \Longrightarrow P
  \]
  That is, we assume that our proposition holds \emph{later}, \ie
  \[
    IH ∈ (\later P_{|len|} \triangleq \later (
        \forall (σ_i)_{i∈\overline{n}}.\
        |len ({-" α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0)) "-})| = n
      )),
  \]
  and use $IH$ to prove $P_{|len|}$.

  To that end, let $(σ_i)_{i∈\overline{n}}$ be an LK trace and define
  $|τ| \triangleq α_{\STraces}((σ_i)_{i∈\overline{n}},\cont(σ_0))$.
  Now proceed by case analysis on $n$:
  \begin{itemize}
    \setlength{\itemsep}{0pt}
    \item \textbf{Case |Z|}: Then we have either
      |τ = Ret ({-" α_\Values(σ_0) "-})| or |τ = Ret Stuck|, both of which map
      to |Z| under |len|.
    \item \textbf{Case |S (idiom m)|}: Then
      |τ = Step _ ^^{-"\idiom{α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\cont(σ_0))}"-}|,
      where $(σ_{i+1})_{i∈\overline{m}} ∈ \later \STraces$ is the guarded
      tail of the LK trace $(σ_i)_{i∈\overline{n}}$.
      Now we apply the inductive hypothesis, as follows:
      \[
        (IH \aplater (σ_{i+1})_{i∈\overline{m}}) \in \later (|len ({-" α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\cont(σ_0)) "-})| = m).
      \]
      We use this fact and congruence to prove
      \[\begin{array}{lclcl}
        n & = & |S (idiom m)| & = & |S (idiom (len ({-" α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\cont(σ_0)) "-})))| \\
          &   &               & = & |len ({-" α_{\STraces}((σ_{i})_{i∈\overline{n}},\cont(σ_0)) "-})|.
      \end{array}\]
  \end{itemize}
  \raisegroup
\end{proof}

It is rewarding to study the use of Löb induction in the proof above in detail,
because many proofs in this subsection as well as \Cref{sec:soundness} will make
good use of it.

The next step is to prove that $α_{\STraces}$ preserves the termination
observable; then all that is left to do is to show that |evalNeed2| abstracts
LK traces via $α_{\STraces}$.
The preservation property is formally expressed as follows:

\begin{lemmarep}[Abstraction preserves termination observable]
  \label{thm:abs-max-trace}
  Let $(σ_i)_{i∈\overline{n}}$ be a maximal trace.
  Then $α_{\STraces}((σ_i)_{i∈\overline{n}}, cont(σ_0))$ ...
  \begin{itemize}
  \setlength{\itemsep}{0pt}
    \item ... ends in |Ret (Fun _)| or |Ret (Con _ _)| if and only
      if $(σ_i)_{i∈\overline{n}}$ is balanced.
    \item ... is infinite if and only if $(σ_i)_{i∈\overline{n}}$ is diverging.
    \item ... ends in |Ret Stuck| if and only if $(σ_i)_{i∈\overline{n}}$ is stuck.
  \end{itemize}
\end{lemmarep}
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

The previous lemma allows us to apply the classifying terminology of maximal LK
traces to a |τ :: T| in the range of $α_{\STraces}$.
For such a maximal |τ| we will say that it is balanced when it ends with
|Ret v| for a |v /= Stuck|, stuck if ending in |Ret Stuck| and diverging if
infinite.

The final remaining step is to prove that |evalNeed2| produces an abstraction of
traces in the LK machine:

\begin{theorem}[|evalNeed2| abstracts LK machine]
  \label{thm:need-abstracts-lk}
  Let $(σ_i)_{i∈\overline{n}}$ be a maximal LK trace with source
  state $(\pe,ρ,μ,κ)$.
  Then $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |evalNeed e (αEnv μ ρ) (αHeap μ)|$,
  where $α_{\STraces}$ is the abstraction function defined in
  \Cref{fig:eval-correctness}.
\end{theorem}
\begin{proof}
Let us abbreviate the proposed correctness relation as
\[\begin{array}{c}
  P_{|α|}((σ_i)_{i∈\overline{n}})
  \triangleq
  \maxtrace{(σ_i)_{i∈\overline{n}}}
  \Longrightarrow
  α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |evalNeed e (αEnv μ ρ) (αHeap μ)| \\
  \hspace{12em}\text{where }(\pe,ρ,μ,κ) = σ_0
\end{array}\]
I prove it by Löb induction, with $IH ∈ \later P_{|α|}$ as the inductive hypothesis.

%I will say that an LK state $σ$ is \emph{inert} if there is no applicable rule
%in the transition system $\smallstep$.
%This is the usual definition of stuckness, but as noted in \Cref{ex:stuck-div}
%my notion of stuckness applies to LK \emph{traces} and is slightly different
%to inertia: for example, for inert $σ$ the singleton LK trace $σ$ is still
%balanced.

Now let $(σ_i)_{i∈\overline{n}}$ be a maximal LK trace with source state
$σ_0=(\pe,ρ,μ,κ)$ and let |τ := evalNeed e (αEnv μ ρ) (αHeap μ)|.
Then the goal is to show $α_{\STraces}((σ_i)_{i∈\overline{n}},κ) = |τ|$.
We do so by cases over $\pe$, abbreviating |tm := αHeap μ| and |tr := αEnv μ ρ|:
\begin{itemize}
  \item \textbf{Case $\px$}:
    Note first that $\LookupT$ is the only applicable transition rule according
    to rule inversion on $\ctrl(σ_0) = \px$.

    In case that $n = 0$, $(σ_i)_{i∈\overline{n}}$ is stuck because
    $\ctrl(σ_0)$ is not a value, hence $α_{\STraces}$ returns |Ret Stuck|.
    Since $\LookupT$ does not apply (otherwise $n > 0$), we must have $\px
    \not∈ \dom(ρ)$, and hence |τ = Ret Stuck| by calculation as well.

    Otherwise, $σ_1 \triangleq (\pe', ρ_1, μ, \UpdateF(\pa) \pushF κ), σ_0 \smallstep σ_1$
    via $\LookupT(\py)$, and $ρ(\px) = \pa, μ(\pa) = (\py, ρ_1, \pe')$.
    This matches |tr ! x = step (Look y) (fetch a)| in the interpreter.

    To show that the tails equate, it suffices to show that they equate \emph{later}.

    We can infer that |tm ! a = memo a (evalNeed2 e' tr')| by definition of
    $α_\Heaps$, so
    \begin{spec}
      fetch a tm = (tm ! a) tm = evalNeed e' tr' tm >>= \case
        (Stuck,  tm') -> Ret (Stuck, tm')
        (val,    tm') -> Step Upd (Ret (val, ext tm' a (memo a (return val))))
    \end{spec}

    Let us define |τl := (idiom (evalNeed e' tr' tm))| and apply the induction
    hypothesis $IH$ to the maximal trace starting at $σ_1$.
    This yields an equality
    \[
      IH \aplater (σ_{i+1})_{i∈\overline{m}} ∈ \idiom{α_{\STraces}((σ_{i+1})_{i∈\overline{m}},\UpdateF(\pa) \pushF κ) = τ^{\later}}
    \]
    When |τl| is infinite, we are done. Similarly, if |τl| ends
    in |Ret Stuck| then the continuation of |>>=| will return |Ret Stuck|,
    indicating by \Cref{thm:abs-length} and \Cref{thm:abs-max-trace} that
    $(σ_{i+1})_{i∈\overline{n-1}}$ is stuck and hence $(σ_i)_{i∈\overline{n}}$
    is, too.

    Otherwise |τl| ends after $m-1$ |Step|s with |Ret (val,tmm)| and
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
    So let us focus on the situation when |τl := (idiom (evalNeed e tr tm))|
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
