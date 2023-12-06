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
In the application case (\ie, ``is |(even 42)| well-typed?''), this
recursion must produce a \emph{summary} for the function to be applied
(|even :: Int -> Bool|), and then apply that summary to produce an abstraction
that is sound for the particular argument (|42 :: Int|).
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
\item Peform a difficult correctness proof, that links an operational semantics for the language
  with an analysis defined by structural recursion.
\item Re-imagine and re-implement the analysis as an abstraction of the
  reachable states of an operational semantics.
  This is the essence of \emph{Abstracting Abstract Machines} (AAM) \cite{aam}
  recipe.
  A very fruitful approach, but one that is not summary-based, hence
  non-modular, possibly less efficient and less precise; in contrast to type
  analysis.
\end{itemize}

Recent years have seen successful applications of the AAM recipe to big-step
style \emph{Definitional Interpreters} as well \cite{Reynolds:72,adi,Keidel:18},
however, the structural mismatch and resulting lack of modularity persists.
Furthermore, big-step interpreters are no substitute for a formal semantics
because they diverge when their input program diverges, thus providing no
safety guarantees for infinite program behaviors.

In this paper, we explore \emph{Denotational Interpreters}:
total, mathematical objects that live at the intersection of
structurally-defined definitional interpreters and denotational semantics,
enjoying a straightforward encoding in typical higher-order programming
languages.

We make the following contributions:
\begin{itemize}
\item
  We use a concrete example (usage analysis) to explain the problems we
  sketched above: the lack of operational detail and other shortcomings of
  denotational semantics, and the structural mismatch between the semantics and
  the analysis (\Cref{sec:problem}).
\item \Cref{sec:interp} walks through the structural definition of our shared
  denotational interpreter and its type class algebra in Haskell.
  We demonstrate the ease with which different instances of our interpreter
  endow our object language with call-by-name, variants of call-by-need, and
  variants of call-by-value evaluation strategies, producing (abstractions of)
  small-step traces.
\item In the AAM spirit, our denotational interpreter can also be instantiated
  at more \emph{abstract} semantic domains.
  \Cref{sec:abstractions} gives three examples, covering a wide span of
  applications: Type analysis, usage analysis and 0CFA control-flow analysis.
  The former two have interesting summary mechanisms that our framework
  expresses in a natural way.
\item \Cref{sec:adequacy} delivers proof that denotational
  interpreters are actual semantics.
  Totality is demonstrated by embedding the shared interpreter and its by-name
  and by-need instantiations in Guarded Cubical Agda~\citep{tctt}.
  Furthermore, the by-need instantiation is shown to adequately generate an
  abstraction of a lazy Krivine trace, preserving length as well as arbitrary
  information about each transition taken.
\item In \Cref{sec:soundness}, we apply abstract interpretation to characterise
  a set of soundness conditions that the type class instances of an abstract
  domain must satisfy in order to soundly approximate by-name interpretation.
  None of the conditions mention shared code, and, more remarkably, none of the
  conditions mention the concrete semantics or the Galois connection either!
  This enables us to finally prove usage analysis correct \wrt the by-name
  semantics in a third of a page, because all reasoning happens in the abstract.
%\item
%  \sg{Write more here once I revisited Related Work}
%  \Cref{sec:related-work}, Related Work.
\end{itemize}
