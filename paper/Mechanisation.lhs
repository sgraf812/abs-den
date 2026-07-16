%if style == newcode
> module Mechanisation where
%endif

\section{Mechanisation in Lean}
\label{sec:mechanisation}

The development of the previous sections is mechanised in Lean~4 on top of
\texttt{iris-lean}, the Lean port of the Iris separation logic
framework~\citep{Jung:18}.\footnote{The development builds with Lean~4.31.0 and
\texttt{iris-lean} pinned at commit \texttt{18e9020}, which \texttt{lake} fetches
from the recorded manifest.}
All proofs have been contributed by a large language model in a close feedback loop,
with a human-written pen-and-paper proof serving as the blueprint.
The mechanisation follows the blueprint's reusable logical-relation structure
and makes precise what the paper leaves informal: the Later modality, the ``$f$
polymorphic'' and ``$x$ fresh'' premises of the abstraction laws
(\Cref{fig:abstraction-laws}), and the finite height of the abstract domain.

Iris' model is the category of \emph{ordered families of equivalences} (OFEs) and
\emph{non-expansive maps}. Working inside it changes |eval| only in its arrows: the
function arrow of \Cref{fig:eval} becomes the non-expansive \texttt{-n>}, so the OFE
structure carries the step-indexing that guarded recursion needs. At a discrete OFE
every map is non-expansive, so this refinement is provably equivalent to the direct
translation of \Cref{fig:eval} (\texttt{evalConst\_eq\_eval}).
The soundness argument reduces to a single parameterised binary logical relation, and
its fundamental lemma is proved once, by induction on the expression.
The by-need interpreter still runs, so the traces we computed by hand in
\Cref{sec:interp} are machine-checked.

The end product of the mechanisation is \texttt{absence}: a
variable that usage analysis reports unused is never looked up during by-need
evaluation. Its Lean statement is

\lstinputlisting[language=Lean]{mechanisation-absence.lean}

\noindent
where \texttt{hb} asks that |e| obey Barendregt's convention (bound variables pairwise
distinct and distinct from the free ones, so nothing shadows), \texttt{habs} is the
analysis verdict that $x$ is unused, and the conclusion says that in the by-need trace of
|e| from the empty heap, no prefix looks $x$ up.
Absence is the $|U0|$ case of \texttt{usage\_approximates\_need}, the |Prop|-level
counterpart of \Cref{thm:usage-abstracts-need}:

\lstinputlisting[language=Lean]{mechanisation-approx.lean}

\noindent
Here \texttt{Trace.lookCount x n} counts the lookups of $x$ in the first $n$ steps of the
by-need trace, \texttt{U.ofCount} abstracts that count into a |U|-cardinality, and
\texttt{.uses !? x} is the usage the analysis reports for $x$.
The bound holds at every $x$ and $n$.
In $\Let{i}{\Lam{x}{x}}{i~i}$, for example, the analysis reports $x$ as $|U0|$, so the
binder $x$ is looked up zero times at every prefix length.
These are ordinary |Prop|s over the by-need semantics; the logical relation of
\Cref{sec:mech-lr} discharges them.

\subsection{The Interpreter, in the World of Non-Expansive Maps}
\label{sec:mech-eval}

\begin{figure}
\lstinputlisting[language=Lean, deletekeywords={let}]{mechanisation-eval.lean}
\caption{The Lean definition of |eval|, the counterpart of the Haskell interpreter in
\Cref{fig:eval}. A binder that must be non-expansive is written \texttt{ofe\_fun}.}
\label{fig:lean-eval}
\end{figure}

\Cref{fig:lean-eval} shows the mechanised |eval|.
It is a non-expansive map from environments to the semantic domain, polymorphic over
any |d| that is an OFE with the operations of the |Domain| class, and it follows the
Haskell interpreter of \Cref{fig:eval} clause for clause.
The one difference is the binder: \texttt{ofe\_fun} where Haskell writes a plain
lambda.
An \texttt{ofe\_fun} carries a non-expansiveness obligation, which for |eval| a
purpose-built tactic (\texttt{ne\_solve}) discharges.
Because |eval| is non-expansive, the closures it passes to |fun| and |bind| are
non-expansive by construction, and no step index is manipulated by hand.
The definition of |eval| needs only an OFE, not a complete one; completeness enters
when we construct a concrete domain such as |DNeed| to run it in.

\subsection{The Guarded Domain}
\label{sec:mech-domain}

The by-need domain, its traces, and its values solve the recursive equations
\begin{align*}
  |DNeed| &~\cong~ |Heap|\,(\later|DNeed|) \to |T|\,(|Value| \times |Heap|\,(\later|DNeed|)), \\
  |T|~a   &~\cong~ |Ret|~a ~\mid~ |Step|~|Event|~(\later(|T|~a)) ~\mid~ |Invis|~(\later(|T|~a)), \\
  |Value| &~\cong~ |Stuck| ~\mid~ |Fun|\,(\later(|DNeed| \to |DNeed|)) ~\mid~ |Con|~K~[\,\later|DNeed|\,],
\end{align*}
which Iris resolves as the fixpoints of \emph{contractive} functors~\citep{Jung:18}.
A trace guards its tails, the heap maps addresses to guarded thunks $\later|DNeed|$, and
a |Value| guards its recursive components: the domain occurs in |Fun| and |Con| only
under a $\later$.
Every self-reference thus sits beneath a $\later$, which makes the signatures
contractive.
Löb induction, the induction principle of $\later$, closes the guarded fixpoints.

A trace carries visible events, |Step|, and silent steps, |Invis|; the productivity
result below concerns runs of the latter.
Two step-indexed logics appear.
Productivity and adequacy use \texttt{SiProp}, the pure step-indexed propositions.
By-need soundness uses \texttt{UPred} over a ghost-heap \emph{camera}~\citep{Jung:18}: a heap invariant
relates each thunk to its abstract value, and the frame rule of separation logic
threads it through the proof.

\subsection{A Logical Relation, Proved Once}
\label{sec:mech-lr}

The mechanisation reads the soundness statement of \Cref{sec:soundness} as a
step-indexed logical relation and builds it directly: a binary relation \texttt{LR2},
parameterised over the ambient step-indexed logic, relating one expression evaluated in
two |Domain| instances.
Its fields are the relation itself and one closure condition per combinator,
stating that the relation is preserved by that combinator.
Its fundamental lemma, that the relation holds of |eval|~$e$ in related environments
for every $e$, is proved once by induction on $e$, each case discharged by the matching
field.

By-need productivity and by-need soundness are two instances of \texttt{LR2}.
Soundness does not reuse the Galois connection of \Cref{fig:abstract-name-need}: a
guarded, higher-order heap has no abstraction function to fold over an infinite trace,
so soundness is a step-indexed relation in the ghost-heap logic,
\[
  \texttt{SoundR}~d~dh \;:=\; \forall \mu.\ \texttt{HeapInv}~\mu \wand \texttt{Rel}~dh~(\mathit{run}~\mu~d).
\]
\texttt{Rel} folds the trace that $d$ produces in a heap $\mu$ against the abstract
bound $dh$: a returned value $v$ must satisfy \texttt{SoundVal}~$dh~v$ and re-establish
\texttt{HeapInv}; a visible event requires an abstract |step| below $dh$; a silent step
only descends under a $\later$.
The single inequality of \Cref{thm:abstract-by-need} becomes this guarded
relation.
The mechanised results compose:
\[\begin{array}{rl}
  & \texttt{AbstractionLaws}~V \\
  \xrightarrow{\ \texttt{soundLR2}\ } & \texttt{LR2}~(\texttt{NeedProp}~V) \\
  \xrightarrow{\ \texttt{LR2.fundamental}\ } & \text{soundness of } |eval| \text{, for every } e \\
  \xrightarrow{\ \texttt{need\_abstracts\_lk}\ } & \text{the same bound on the LK trace}
\end{array}\]
\texttt{soundLR2} builds the \texttt{LR2} instance from the abstraction laws of
\Cref{fig:abstraction-laws}, discharging each closure field against them by Löb
induction under the heap invariant; the composite of the first two arrows is
\texttt{byNeed\_sound}.
At the usage lattice \texttt{UDk}~$k$ (\Cref{sec:mech-finite}),
\texttt{usageAbstractionLaws} proves the laws, giving \texttt{usage\_abstracts\_need}
(\Cref{thm:usage-abstracts-need}); a new analysis supplies only this input.
Read at the empty heap, this step-indexed statement collapses to the |Prop|-level
\texttt{usage\_approximates\_need} and \texttt{absence} of the section opener.

Productivity, over \texttt{SiProp}, states that no two silent steps occur in a row.
It is what makes the interpreter total (\Cref{thm:totality}), so the fuel-bounded
observation of \Cref{sec:mech-exec} always reaches the next event.
Adequacy against the LK machine (\Cref{thm:need-adequacy-bisimulation}, mechanised as
\texttt{need\_abstracts\_lk}) supplies the final arrow; it is proved separately, by Löb
induction relating the by-need trace to the machine.

\subsection{The Side Conditions, Made Precise}
\label{sec:mech-side}

The abstraction laws carry two informal premises, ``$f$ polymorphic'' and ``$x$
fresh''.
Polymorphism, the premise of \textsc{App-Fun} and \textsc{Sel-Con}, becomes a
parametricity condition: $f$ respects every logical relation whose closure clauses
cover the summarised binders and the looked-up variables.
A separate lemma shows that every closure |eval| produces is parametric in this sense.
This is the parametricity that \Cref{sec:soundness} invokes for \textsc{App-Fun}.
Freshness becomes the least combinator-closed predicate that does not observe a lookup
of $x$.
A variable's occurrence is not observable in a generic |Domain| element, so this is the
faithful reading of ``$x$ does not occur in $d$'', and it too transports through |eval|.
Lexical scoping becomes a Barendregt well-scopedness predicate on the syntax, which supplies
facts such as $x \neq y$ for a let-bound $y$.

\subsection{Finite Height, and Where Completeness Enters}
\label{sec:mech-finite}

Usage analysis takes a least fixpoint, so its domain must have no infinite ascending
chains (\Cref{sec:usage-fixpoint}).
The mechanisation bounds a summary to its $k$ leading components and the variable
supply to names of a fixed length, which gives a finite lattice on which Kleene
iteration terminates.
This truncation is crude: a principled finite abstract domain with a proper widening is
an orthogonal problem we do not address, and the mechanisation needs only some
finite-height instance to run the fixpoint.

Completeness enters in one place, the construction of the concrete |DNeed|
(\Cref{sec:mech-domain}).
An abstract domain such as |UD| is used at its discrete OFE, where non-expansive maps
are ordinary functions, so it needs no guardedness.
The abstraction laws are therefore stated over a preorder with chain-complete suprema
rather than a full lattice.

\subsection{The Interpreter Still Runs}
\label{sec:mech-exec}

|eval| at |DNeed| is executable: it reduces to a by-need trace, and a fuel-bounded
function reads off a finite prefix.
The example traces of \Cref{sec:interp} and the analysis results of
\Cref{sec:usage-analysis} are checked against it by \texttt{\#guard} during the build,
including that each trace agrees with the LK machine up to silent steps.
Execution goes through unsafe \texttt{implemented\_by} shims for the domain isomorphism
and the guarded fixpoint.
The shims replace compiled code only, so the proofs are unaffected:
\texttt{absence} depends on the standard axioms alone.
