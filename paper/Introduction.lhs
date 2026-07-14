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

Traditional denotational semantics, however, abstracts away operational detail,
and that detail is often the whole point of the analysis.
To ask ``how often does $\pe$ evaluate its free variable $x$?'' is to ask about
\emph{evaluation}, a notion that a standard denotational semantics does not even
express.
Such questions drive us to an \emph{operational semantics}~\citep{Plotkin:81},
which makes the stack and heap explicit and views execution as a sequence of
machine states.

Yet an operational semantics is not compositional, and that mismatch resurfaces
in the soundness proof.
Relating a compositional analysis to a non-compositional sequence of machine
states calls for a hand-crafted \emph{step-indexed logical
relation}~\citep{AppelMcAllester:01} over machine configurations.
This relation is the creative core of the proof, and under call-by-need it is
especially delicate: the heap stores computations that may refer back to the
heap, so the relation must be stratified over recursive heap invariants.
Both the relation and its congruence proof grow with the
complexity of the semantics and of the analysis.

We tried to find ways to avoid this complexity.
Our approach still rests on a logical relation, but relates the compositional
\emph{denotations} of a \textbf{\emph{denotational interpreter}}\footnote{This term was
coined by \citet{Might:10}.} rather than machine configurations.
Such an interpreter is compositional like a denotational semantics, yet records the
operational detail of an abstract machine, sitting at the intersection of the executable
\emph{definitional interpreter}~\citep{Reynolds:72} and the compositional denotational
semantics.
The denotation of a term is a (possibly infinite) trace, bisimilar to the abstract
machine's run on that term; to our knowledge, this is the first denotational semantics
for call-by-need with that property.

Moreover, the interpreter is \emph{parameterised} over the semantic domain and
the operations that interpret each syntactic construct.
Plugging in one domain yields the trace semantics just described; plugging in
another, deliberately finite domain yields a static analysis of the same program.
Semantics and analysis are thus the same definition at different instantiations.

Because analysis and semantics are the same interpreter, they once again ``line
up'' and soundness becomes markedly easier to prove.
Since the relation follows the structure of the interpreter, its congruence proof is a
simple structural induction over the syntax, and each denotation abstracts directly into
an element of the analysis domain, whereas a machine configuration is inseparable from
its continuation.
Packaged once and for all as a reusable \emph{fundamental theorem} in the spirit of
parametricity~\citep{Reynolds:83,Wadler:89}, this induction reduces the soundness of an
analysis to properties of its plugged-in operations, which we identify and characterise
as \emph{abstraction laws}.
As a concrete example, we prove a summary-based \emph{usage
analysis}~\citep{WrightBakerFinch:93,Gustavsson:98} sound for call-by-need.

We do not claim that this interpreter and proof setup applies as-is to \emph{just
any} analysis; rather, we share a new pattern for defining static analyses and
proving them correct without drowning in operational detail, in the spirit of
abstract interpretation.
% To exemplify this difficulty and show the usefulness of our approach, we prove
% that a derived summary-based \emph{usage analysis} is sound for call-by-need
% and give an example where this simple usage analysis can be more precise than
% any analysis based on control-flow analysis (referring to \citet{Mangal:14} for
% the general result).

We make the following contributions:
\begin{itemize}
\item \Cref{sec:interp} walks through the definition of our generic
  denotational interpreter and its type class algebra in Haskell.
  The exposition assumes a by-name evaluation strategy, but we will see how easily
  the interpreter adjusts to by-need, each instance producing (abstractions of)
  abstract machine traces.
\item A concrete instantiation of a denotational interpreter is \emph{total}
  if it coinductively yields a (possibly infinite) trace for every input
  program, including ones that diverge.
  \Cref{sec:totality} proves that the by-name and by-need instantiations are
  total by embedding the generic interpreter and its instances in Lean, using
  guarded recursion.
\item \Cref{sec:adequacy} proves that the traces generated by the by-need
  instantiation of our denotational interpreter are bisimilar to traces in the
  lazy Krivine machine~\citep{Sestoft:97}.
  Thus, concrete denotational interpreters can be semantic ground truth.
\item
  Even if the reader is unconvinced at this point that \emph{concrete}
  denotational interpreters are useful, \Cref{sec:abstraction} shows that its
  \emph{abstract} instances are.
  We instantiate the generic interpreter with a finite, abstract semantic domain,
  recovering summary-based usage analysis, which infers upper bounds on how many
  times each variable is used.
  Such a domain is an ordinary finite lattice: defining an analysis needs none of the
  guarded-recursive domain construction that the concrete by-need semantics requires.
  The extended version contains further examples, such as \citeauthor{Milner:78}'s type
  analysis, as well as a 0CFA control-flow analysis and Demand Analysis of the
  Glasgow Haskell Compiler.
\item In \Cref{sec:soundness}, we apply abstract interpretation to characterise
  a set of abstraction laws that the type class instances of an abstract
  domain must satisfy in order to soundly approximate by-need
  interpretation.
  None of the proof obligations mention the generic interpreter, and, more
  remarkably, none of the laws mention the concrete semantics or the Galois
  connection either!
  This enables us to prove usage analysis sound \wrt the by-need
  semantics by an argument that never mentions the interpreter,
  building on reusable semantics-specific theorems.
  Due to the adequacy result in \Cref{sec:adequacy}, this result
  holds regardless of whether a concrete denotational interpreter or an
  operational semantics is considered semantic ground truth.
\item
  \Cref{sec:mechanisation} mechanises the by-need development in Lean on top of the
  Iris separation logic~\citep{Jung:18}: the generic interpreter, its adequacy \wrt
  the lazy Krivine machine, and the soundness of usage analysis, culminating in a
  machine-checked proof that a variable the analysis reports unused is never looked up
  during evaluation.
  The guarded-recursive interpreter stays executable, so the example traces of
  \Cref{sec:interp} are checked by the build.
\item
  We compare to the enormous body of related approaches in \Cref{sec:related-work}.
\end{itemize}
