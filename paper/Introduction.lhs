%if style == newcode
> module Introduction where
%endif

\section{Introduction}
\label{sec:introduction}

A \emph{static program analysis} infers facts about a program, such
as ``this program is well-typed'', ``this higher-order function is always called
with argument $\Lam{x}{x+1}$'' or ``this program never evaluates $x$''.
In a functional-language setting, such static analyses are
often defined by \emph{structural recursion} on the input term.
For example, consider the claim ``|(even 42)| is well-typed''.
Type analysis asserts that |even :: Int -> Bool|, |42 :: Int|, and then applies
the function type to the argument type to produce the result type |even 42 ::
Bool|.
The function type |Int -> Bool| is a \emph{summary} of |even|:
Whenever the argument has type |Int|, the result has type |Bool|.
Function summaries play a crucial role in achieving modular higher-order
analyses, because it is much more efficient to apply the summary of a function
instead of reanalysing its definition at use sites in other modules.

To prove the analysis correct, it is favorable to pick a language semantics that
is also defined by structural recursion, such as a \emph{denotational
semantics}~\citep{ScottStrachey:71}; then the semantics and the analysis ``line
up'' and the correctness proof is relatively straightforward.
Indeed, one can often break up the proof into manageable subgoals by regarding
the analysis as an \emph{abstract interpretation} of the denotational
semantics~\citep{Cousot:21}, particularly when the abstract operations of the
analysis correspond to concrete operations in the semantics.

Alas, traditional denotational semantics does not model operational details --
but those details might be the whole point of the analysis.
For example, we might want to ask ``How often does $\pe$ evaluate its free
variable $x$?'', but a standard denotational semantics simply does not express
the concept of ``evaluating a variable''.
So we are typically driven to use an \emph{operational
semantics}~\citep{Plotkin:81}, which directly models operational details like
the stack and heap, and sees program execution as a sequence of machine states.
Now we have two unappealing alternatives:
\begin{itemize}
\item Put up with \emph{structural mismatch} and peform a difficult correctness
  proof, one that links an operational semantics for the language with an
  analysis defined by structural recursion.
\item Reimagine and reimplement the analysis as an abstraction of the
  reachable states of an operational semantics.
  This is the essence of \emph{Abstracting Abstract Machines} (AAM) \cite{aam}
  recipe.
  A very fruitful framework, but one that follows the \emph{call strings}
  approach~\citep{SharirPnueli:78}, reanalysing function bodies at call sites.
  Hence the new analysis becomes non-modular, and possibly less efficient and
  less precise than its summary-based variant.
\end{itemize}

In this paper, we resolve the tension by exploring \emph{Denotational
Interpreters}~\citep{Might:10}: total, mathematical objects that
live at the intersection of structurally-defined \emph{Definitional
Interpreters}~\citep{Reynolds:72} and denotational semantics.
Our denotational interpreters generate small-step traces embellished with
arbitrary operational detail and enjoy a straightforward encoding in typical
higher-order programming languages.
Static analyses arise as instantiations of the shared interpreter skeleton,
enabling succinct correctness proofs just like for AAM or big-step definitional
interpreters~\citep{adi,Keidel:18,Bodin:19}.
However, the shared, compositional structure enables a wide range of summary
mechanisms in static analyses that we think are beyond reach for reachable
states abstractions.

We make the following contributions:
\begin{itemize}
\item
  We use a concrete example (deadness analysis) to explain the problems we
  sketched above: the lack of operational detail and other shortcomings of
  denotational semantics, and the structural mismatch between the semantics and
  the analysis (\Cref{sec:problem}).
\item \Cref{sec:interp} walks through the structural definition of our shared
  denotational interpreter and its type class algebra in Haskell.
  We demonstrate the ease with which different instances of our interpreter
  endow our object language with call-by-name, variants of call-by-need and
  variants of call-by-value evaluation strategies, producing (abstractions of)
  small-step traces.
\item In \Cref{sec:abstractions} we give three examples of abstract
  interpretations, covering a wide span of applications: Type analysis, usage
  analysis and 0CFA control-flow analysis.
  The former two have interesting summary mechanisms that our framework
  expresses in a natural way.
\item A concrete instantiation of a denotational interpreter is \emph{total}
  if it coinductively yields a (possibly-infinite) trace for every input
  program, including ones that loop.
  \Cref{sec:totality} proves that the by-name and by-need instantiations are
  total by embedding the shared interpreter and its instances in Guarded Cubical
  Agda.
\item \Cref{sec:adequacy} delivers proof that the by-need instantiation of our
  denotational interpreter adequately generates an abstraction of a lazy Krivine
  trace, preserving its length as well as arbitrary operational information
  about each transition taken.
\item In \Cref{sec:soundness}, we apply abstract interpretation to characterise
  a set of soundness conditions that the type class instances of an abstract
  domain must satisfy in order to soundly approximate by-name and by-need
  interpretation.
  None of the conditions mention shared code, and, more remarkably, none of the
  conditions mention the concrete semantics or the Galois connection either!
  This enables us to finally prove usage analysis correct \wrt the by-name
  semantics in a third of a page, because all reasoning happens in the abstract.
\item
  We compare to a variety of other related approaches in \Cref{sec:related-work}.
  %TODO say more?
\end{itemize}
