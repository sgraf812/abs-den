%if style == newcode
> module Introduction where
%endif

\section{Introduction}
\label{sec:introduction}

A \emph{static program analysis} infers semantic properties about a program,
such as ``this program is well-typed'', ``this higher-order function is always
called with argument $\Lam{x}{x+1}$'' or ``this program never evaluates $x$''.
In a functional-language setting, such static analyses are
often defined \emph{compositionally} on the input term: the result of analysing
a term is obtained by analysing its subterms separately and combining the results.
For example, consider the claim ``|(even 42)| has type |Bool|''.
Type analysis separately computes |even :: Int -> Bool| and |42 :: Int|, and then
combines these results to produce the result type |even 42 :: Bool|,
without looking at the definition of |even| again.

% Omitting this sentence.. it gets in the way of the page-1 flow
% If the analysis is used in a compiler to inform optimisations, it is
% important to prove it sound, because lacking soundness
% can lead to miscompilation of safety-critical applications~\citep{Sun:16}.

Often, a good explanation of a static analysis is by analogy to the semantic
property it is supposed to approximate.
If properly formalised, the analogy doubles as a statement of \emph{soundness}.
To prove a compositional analysis sound, it is helpful to pick a language
semantics that is also compositional, such as a \emph{denotational
semantics}~\citep{ScottStrachey:71}; then the semantics and the analysis ``line
up'' and the soundness proof/explanation is relatively straightforward.
One can regard the analysis as an \emph{abstract interpretation} of the
compositional semantics~\citep{Cousot:21} and further break up the proof into
manageable subgoals decoupled from the definition of analysis or semantics.

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
  non-compositional operational semantics with a compositional analysis.
\item Reimagine and reimplement the analysis as an abstraction of the
  reachable states of an operational semantics.
  This is the essence of the \emph{Abstracting Abstract Machines} (AAM)
  \cite{aam} recipe.
%  A very fruitful framework, but one that follows the \emph{call strings}
%  approach~\citep{SharirPnueli:78}, reanalysing function bodies at call sites.
%  Hence the new analysis becomes non-modular, leading to scalability problems
%  for a compiler.
\end{itemize}

In this paper, we explore a third alternative, \textbf{\emph{denotational
interpreters}}: total, mathematical objects that live at the intersection of
compositionally-defined \emph{definitional interpreters}~\citep{Reynolds:72} and
denotational semantics.
Our denotational interpreters generate abstract machine traces and enjoy a
straightforward encoding in typical higher-order programming languages.
Static analyses arise as instantiations of the same generic interpreter,
enabling succinct, shared and modular soundness proofs just like for AAM or
big-step definitional interpreters~\citep{adi,Keidel:18}.
However, the compositional structure enables a wide range of summary mechanisms
in static analyses that we found difficult to achieve using an AAM approach.

We make the following contributions:
\begin{itemize}
\item
  We use a concrete example (absence analysis) to argue for
  the usefulness of compositional, summary-based analysis in \Cref{sec:problem}
  and we demonstrate the difficulty of conducting an ad-hoc soundness proof
  \wrt a non-compositional abstract machine semantics.
\item \Cref{sec:interp} walks through the definition of our generic
  denotational interpreter and its type class algebra in Haskell.
  We demonstrate the ease with which different instances of our interpreter
  endow our object language with call-by-name, call-by-need and call-by-value
  evaluation strategies, each producing (abstractions of) abstract
  machine traces.
\item A concrete instantiation of a denotational interpreter is \emph{total}
  if it coinductively yields a (possibly infinite) trace for every input
  program, including ones that diverge.
  \Cref{sec:totality} proves that the by-name and by-need instantiations are
  total by embedding the generic interpreter and its instances in Guarded Cubical
  Agda.
\item \Cref{sec:adequacy} proves that the traces generated by the by-need
  instantiation of our denotational interpreter are bisimilar to traces in the
  lazy Krivine machine~\citep{Sestoft:97}.
  Thus, denotational interpreters can be semantic ground truth.
\item In \Cref{sec:abstraction} we instantiate the generic interpreter with
  finite, abstract semantic domains.
  In doing so, we recover summary-based usage analysis, a generalisation
  of absence analysis in \Cref{sec:problem}, as well as \citeauthor{Milner:78}'s
  type analysis.
  The Appendix contains further examples, such as 0CFA control-flow analysis and
  Demand Analysis of the Glasgow Haskell Compiler.
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
