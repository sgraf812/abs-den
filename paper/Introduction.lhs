%if style == newcode
> module Introduction where
%endif

\section{Introduction}
\label{sec:introduction}

A \emph{static program analysis} infers facts about a program, such
as ``this program is well-typed'', ``this higher-order function is always called
with argument $\Lam{x}{x+1}$'' or ``this program never evaluates $x$''.
In a functional-language setting, such static analyses are
often defined \emph{compositionally} on the input term.
For example, consider the claim ``|(even 42)| has type |Bool|''.
Type analysis asserts that |even :: Int -> Bool|, |42 :: Int|, and then applies
the function type to the argument type to produce the result type |even 42 ::
Bool|.
The function type |Int -> Bool| is a \emph{summary} of the definition of |even|:
Whenever the argument has type |Int|, the result has type |Bool|.
Function summaries enable efficient modular higher-order analyses, because it is
much faster to apply the summary of a function instead of reanalysing its
definition at use sites in other modules.

If the analysis is used in a compiler to inform optimisations, it is
important to prove it sound, because lacking soundness
can lead to miscompilation of safety-critical applications~\citep{Sun:16}.
In order to prove the analysis sound, it is helpful to pick a language
semantics that is also compositional, such as a \emph{denotational
semantics}~\citep{ScottStrachey:71}; then the semantics and the analysis ``line
up'' and the soundness proof is relatively straightforward.
Indeed, one can often break up the proof into manageable sub goals by regarding
the analysis as an \emph{abstract interpretation} of the compositional
semantics~\citep{Cousot:21}.
%particularly when the abstract operations of the
%analysis correspond to concrete operations in the semantics.

Alas, traditional denotational semantics does not model operational details --
and yet those details might be the whole point of the analysis.
For example, we might want to ask ``How often does $\pe$ evaluate its free
variable $x$?'', but a standard denotational semantics simply does not express
the concept of ``evaluating a variable''.
So we are typically driven to use an \emph{operational
semantics}~\citep{Plotkin:81}, which directly models operational details like
the stack and heap, and sees program execution as a sequence of machine states.
Now we have two unappealing alternatives:
\begin{itemize}
\item Develop a difficult, ad-hoc soundness proof, one that links a
  non-\nolinebreak\hspace{0pt}compositional operational semantics with a compositional analysis.
\item Reimagine and reimplement the analysis as an abstraction of the
  reachable states of an operational semantics.
  This is the essence of the \emph{Abstracting Abstract Machines} (AAM)
  \cite{aam} recipe,
  a very fruitful framework, but one that follows the \emph{call strings}
  approach~\citep{SharirPnueli:78}, reanalysing function bodies at call sites.
  Hence the new analysis becomes non-modular, leading to scalability problems
  for a compiler.
  %\slpj{It's hard
  %to understand this critique.  Better: ``Reimagine and reimplement the analysis as an abstraction of the
  %reachable states of an operational semantics.  Now the analysis and semantics
  %``line up'' again, so the soundness proof is relatively simple.  Alas, this
  %approach has significant shortcomings that we outline in \Cref{blah}''.}
  %\sg{Better? I think that connecting reanalysing function bodies with modularity
  %is pretty succinct and convincing.}
\end{itemize}

In this paper, we resolve the tension by exploring \emph{denotational
interpreters}: total, mathematical objects that live at the intersection of
structurally-defined \emph{definitional interpreters}~\citep{Reynolds:72} and
denotational semantics.
Our denotational interpreters generate small-step traces embellished with
arbitrary operational detail and enjoy a straightforward encoding in typical
higher-order programming languages.
Static analyses arise as instantiations of the same generic interpreter,
enabling succinct, shared soundness proofs just like for AAM or big-step
definitional interpreters~\citep{adi,Keidel:18}.
However, the shared, compositional structure enables a wide range of summary
mechanisms in static analyses that we think are beyond the reach of
non-compositional reachable-states abstractions like AAM.

We make the following contributions:
\begin{itemize}
\item
  We use a concrete example (absence analysis) to argue for
  the usefulness of compositional, summary-based analysis in \Cref{sec:problem}
  and we demonstrate the difficulty of conducting an ad-hoc soundness proof
  \wrt a non-compositional small-step operational semantics.
\item \Cref{sec:interp} walks through the definition of our generic
  denotational interpreter and its type class algebra in Haskell.
  We demonstrate the ease with which different instances of our interpreter
  endow our object language with call-by-name, call-by-need and call-by-value
  evaluation strategies, each producing (abstractions of) small-step
  abstract machine traces.
\item A concrete instantiation of a denotational interpreter is \emph{total}
  if it coinductively yields a (possibly-infinite) trace for every input
  program, including ones that diverge.
  \Cref{sec:totality} proves that the by-name and by-need instantiations are
  total by embedding the generic interpreter and its instances in Guarded Cubical
  Agda.
\item \Cref{sec:adequacy} proves that the by-need instantiation of our
  denotational interpreter adequately generates an abstraction of a trace
  in the lazy Krivine machine~\citep{Sestoft:97}, preserving its length as well
  as arbitrary operational information about each transition taken.
\item By instantiating the generic interpreter with a finite, abstract semantic
  domain in \Cref{sec:abstraction}, we recover summary-based usage analysis, a generalisation
  of absence analysis in \Cref{sec:problem}.
  %Such static analyses can be defined in two steps:
  %in the first, an operational property is encoded by a fold over the trace,
  %inducing an instrumented interpreter.
  %In the second step, the semantic domain is finitised and equipped with a
  %summary mechanism, inducing a static analysis approximating the instrumentation.
  Further examples in the Appendix comprise Type Analysis and 0CFA control-flow
  analysis, demonstrating the wide range of applicability of our framework.
  %We have refactored the Demand Analysis of the Glasgow Haskell Compiler into
  %a abstract denotational interpreter to demonstrate a real-world use case.
\item In \Cref{sec:soundness}, we apply abstract interpretation to characterise
  a set of abstraction laws that the type class instances of an abstract
  domain must satisfy in order to soundly approximate by-name and by-need
  interpretation.
  None of the proof obligations mention the generic interpreter, and, more
  remarkably, none of the laws mention the concrete semantics or the Galois
  connection either!
  This enables us to prove usage analysis sound \wrt the by-name
  and by-need semantics in half a page, building on reusable
  semantics-specific theorems.
\item
  We compare to the enormous body of related approaches in \Cref{sec:related-work}.
\end{itemize}
