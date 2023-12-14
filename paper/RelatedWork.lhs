%if style == newcode
> module RelatedWork where
%endif

\section{Related Work}
\label{sec:related-work}

%\subsubsection*{Operational Semantics and Abstract Machines}
%Plotkin's Aarhus lectures~\citep{Plotkin:81} in the late 70's systematically
%introduced small-step operational semantics based on transition systems,
%covering both state and higher-order functions.
%The use of transition systems was novel, in contrast to the then
%prevalent notion of \emph{abstract machine} definitions, such as for the
%\emph{G-machine}~\citet{Johnsson:84} for executing Lazy ML programs.
%\citet{SPJ:92} bridged the gap between graph reduction and transition systems,
%giving an operational semantics for the still widely used \emph{STG machine} for
%lazy evaluation.
%Soon after, \citet{Launchbury:93} gave a big-step operational semantics for
%call-by-need lambda calculus that was drastically simpler than the STG machine
%(and thus simpler to formalise), featuring an explicit heap.
%Our heap forcing relation $(\forcesto)$ from \Cref{sec:essence} is reminiscent
%of Launchbury's $(\leq)$ ordering, although the latter was shown
%inadequate in a mechanised correctness proof~\citep[Section 2.3.3]{Breitner:18}.
%\citet{Sestoft:97}, evidently inspired by Krivine's by-name
%machine~\citep{AgerDanvyMidtgaard:04}, derived a small-step semantics from
%Launchbury's semantics, the metatheory of which was very influential for this
%work.

%        eval/apply or push/enter?
%        Given an expr like $f x$, we first push $ρ(x)$ onto the stack and then
%        evaluate $f$, which will look it up (pushing an udpate frame) and evaluate its
%        RHS. Since we will never return to the "eval site" of $f$, IMO this qualifies
%        as push/enter rather than eval/apply. Which is in contrast to what the Krivine
%        paper says, which dubs return states as "apply" transitions

\subsubsection*{Definitional Big-Step Interpreters, Coinduction, Fuel, Step-indexing and Mechanisation}
% TODO:
% - HOAS
% - Galois Transformers
\citet{LeroyGrall:09} show that a coinductive encoding of big-step semantics
is able to encode diverging traces by proving it equivalent to a small-step
semantics.
Their Lemma 10 covers much the same ground as \Cref{thm:sem-adequate}.
\citet{Owens:16} recognise the usefulness of a definitional interpreters for
correctness proofs, albeit in big-step style and using a fuel-based encoding of
infinite behaviors.
\citet{AgerDanvyMidtgaard:04} show a principled way of how to derive a variant
of the LK machine from a partial denotational interpreter, which could be
applied to our formulation as well.
In fact, the |syn| constraints of \Cref{sec:soundness} express the same
information that closure conversion exploits when turning the denotational
interpreter into a definitional big-step interpreter.
\citet{Keidel:18} show that in abstracting big-step interpreters, correctness of
shared code follows by parametricity~\citep{Wadler:89}.
We found it quite elegant to utilise parametricity in this way, but
unfortunately the free theorem for our interpreter is too weak because it
would exclude the syntactic premises in \Cref{fig:by-name-soundness-lemmas}.
Once the right correctness statement was established, the main proof became so
simple that it could easily be automated.

While our |T|race type is appropriate for tracking ``pure'' transition events,
it is not up to the task of modelling user input, for example.
It would be interesting to see whether use of guarded interaction
trees~\citep{interaction-trees,gitrees} would be as simple to integrate into our
framework as we expect them to.

While working out how to embed |eval| in Guarded Cubical Agda and then
attempting mechanised proofs about |D (ByNeed T)|, we very soon decided that
this was not a task we were up to, due to lack of automation and the general
perceived tediousness of Cubical types.
It would be interesting to see if the Iris proof framework is a better fit
for mechanisation, where guarded types in |eval| would need to be encoded via
fuel/step-indexing.
Certainly, we could use both guarded recursion as well as separation logic for
by-need heaps in our proofs.

\subsubsection*{Contextual Improvement}
Abstract interpretation is useful to prove that an analysis approximates
the right trace property, but it does not make any claim on whether a
transformation conditional on some trace property is actually sound, yet alone
an \emph{improvement}~\citep{MoranSands:99}.
If we were to prove update avoidance correct, would we use our denotational
interpreter to do so?
We have spent some time on this issue and are torn:
Defining a contextual improvement relation $\lessequiv$ on the
semantic domain |D (ByNeed T)| invites all kinds of troubling concerns
relating to the lack of full abstraction~\citep{Plotkin:77}, and if we
were to define $\lessequiv$ on syntax, then what is the difference to
\citet{MoranSands:99}, other than complicating matters?
We think there is none, and hence we would stick to the established improvement
relation $\lessequiv$.
\Cref{thm:sem-adequate} can be used to translate trace properties from
denotational interpreter to small-step semantics.

\subsubsection*{Control-Flow Analysis}
\emph{Control-flow analysis}~\citep{Shivers:91} (CFA) computes a useful
control-flow graph abstraction for higher-order programs.
Such an approximation is useful to apply classic data-flow analyses such as
constant propagation or dead code elimination to the interprocedural setting.
The contour depth parameter $k$ allows to trade precision for performance,
although practical applications never seem to go beyond $1$.

\citet{MontaguJensen:21} derive CFA from small-step traces.
Their chain of abstractions is inspiring and we think that a variant of our
denotational interpreter would be a good fit for their collecting semantics.
Specifically, the semantic inclusions of Lemma 2.10 that govern the
transition to a big-step style interpreter follow simply by adequacy of our
interpreter, \Cref{thm:sem-adequate}.

Abstracting Abstract Machines~\citep{aam} is an ingenious recipe to derive
a computable \emph{reachable states semantics}~\citep{Cousot:21} from any
small-step semantics.
By bounding the size of the store, the freely choosably
$\widehat{\mathit{alloc}}$ function embodies a precision-performance trade-off.
Many analyses such as control-flow analysis (and usage analysis) arise as
abstractions of reachable states.
In fact, we think that for any trace property (\ie, |Trace| instance), there
is an analysis that can be built on CFA, without the need to define a custom
summary mechanism encoded as a |Domain| instance.

\subsubsection*{Summaries of Functionals \vs Call Strings}

\citet{SharirPnueli:78} first brought up the distinction between the
``functional approach'' to interprocedural program analysis and the ``call
strings approach''.
The former approach models the semantics of a function application as
(higher-order) function in the meta language, inviting typical domain-theoretic
concerns, the latter is a predecessor to $k$-CFA.
\citet{Mangal:14} have shown that the functional approach can be equivalent to
$\infty$-CFA for arbitrary complete lattices.
Moreover, they report that 2-CFA is less precise and slower than a comparable
approach to pointer analysis based on function summaries (symbolic abstractions
of the functional).

To illustrate this, usage analysis based on $k$-CFA would need less explanation
of its |Nop| summary, but in some cases we'd lose out on precision due to the
use of call strings.
For example, it is trivial for modular usage analysis to determine that |i|
in $\Let{i}{\Lam{y}{y}}{i~x~x}$ uses |i| only once, \emph{in any context this
expression is ever embedded}.
By contrast, $k$-CFA will have trouble with recursions where multiple
activations of |i| are live simultaneously, \ie, in the Haskell expression

< let f n = let i y = y in if n == 0 then 0 else i (f (n-1) + 1) in f 42{-"."-}

The definition of |f| is a complicated way to define the identity function.
Nevertheless, it is evident that |i| is evaluated at most once, and
usage analysis would infer this fact if we were to desugar and ANFise this
expression into an |Exp|.
On the other hand, $k$-CFA (for $k < 42$) would confuse different recursive
activations of |i|, thus conservatively attributing evaluations multiple times,
to the effect that |i| is not inferred as used at most once.

Furthermore, as sufficiently discussed, summaries lead to modular analyses, in
contrast to a call string approach.
That is why we would favour a summary-based approach where possible.
Furthermore, given a semantic description of abstract values, it is likely
that the implementation of |Domain| can be synthesised using the approach of
\citet{Kalita:2022}.

More interesting cardinality analyses involve the inference of summaries called
\emph{demand transformers}~\citep{cardinality-ext}.
We have indeed been able to define a protoype of \citeauthor{cardinality-ext}'s
work as an instance of our denotational interpreter, however we omit discussion
for space reasons.
Its inner workings are most similar to Clairvoyant
call-by-value~\citep{HackettHutton:19}, so it is a shame that the Clairvoyant
instantiation leads to partiality.

%\subsubsection*{Denotational Semantics}
%Recent work on \emph{Clairvoyant call-by-value}
%semantics~\citep{HackettHutton:19} sheds light on a useful, heapless denotational
%interpretation of call-by-need.
%Their semantics could be factored in two:
%A semantics that non-deterministically drops or eagerly evaluates let
%bindings, and a downstream $\min$ function that picks the (non-stuck) trace with
%the least amount of steps.
%The continuity restrictions of the algebraic domain on the semantics necessitate
%fusing both functions.
%The trace generated by $\pe$ may not even share a common prefix with the trace
%generated for $\pe~\px$.
%We had trouble abstracting such a semantics.
%It would be interesting to revisit the problem with a guarded domain
%formulation such as \citet{Mogelberg:21}.


% These assumptions could perhaps be encoded in a dependently-typed language
% by formulating |eval| as an open recursive function, refining the type of
% |fun| to |fun :: Σ (D -> D) φ -> D| (we did something similar in
% \Cref{sec:totality} for the Agda encoding) and deriving the free theorem for
% that function.
% The recursion could then be closed with guarded/Löb |fix| after the fact.
% In general, we could do this refinement for all type class operations,
% reflecting ever more information from the definition of |eval| into its type;
% the |φ| would thus enumerate all syntactic use sites of |fun|.
% At this point, the use of parametricity to conclude the soundness proof is not
% too different from writing a custom tactic for a theorem prover.
% Alas, parametricity is hard to use without a tool verifying correct extraction
% of theorems, so we prove the below lemma by hand.
% However, parametricity is a strong argument that our approach can easily be
% generalised to other denotational interpreters.

% TODO: Compare the Speculate and Postpone properties to the frame rule of
% separation logic

% Other topics:
% - Operational semantics: CESK Felleisen, Launchbury, Sestoft, Krivine
% - Nielson: correctness predicate
% - Imprecise exceptions
%        There have been attempts to discern panices from other kinds of loops, such as
%        \citep{imprecise-exceptions}. Unfortunately, in Section 5.3 they find it
%        impossible give non-terminating programs a denotation other than $\bot$, which
%        still encompasses all possible exception behaviors.
% - Definitional Interpreter work; we are using TCTT as the defining language
% - Pitts chapter in TAPL2, "largest congruence relation"
% - SGDT:
%     * Nakano:00 introduced modality
%     * DreyerAhmedBirkedal:11 refined and applied to step-indexing
%     * Birkedal:12 discovered how to hide step indices. Applied to System F like language with store. Later also depedent type theory. Connection to Kripke worlds
%     * BirkedalMogelbergEjlers:13 first described how to encode guarded recusive types ``syntactically'', e.g., as we use them in meta ::=-notation
%     * gdtt was all about lifting to dependent product types containing the later modality. For example `f <*> t` has to substitute `t` in `f`'s type, solved via delayed substitutions.
%       Important for properties! Hence guaded DEPENDENT type theory
%     * Guarded Cubical Type Theory: Reasoning about equality in GDTT can be undecidable, fix that. But no clock qunatification!
%     * Clocks are ticking: Clock quantification via tick binders which act similar to intervals in Cubical. (Still uses those delayed substitutions!)
%     * TCTT (Bisimulation as Path Type for Guarded Recursive Types) not only introduces ticked cubical, it also covers bisimilarity of guarded labelled transition systems. Our traces are just that, plus a bit more.
%       Also shows how to define a mixed guarded/inductive data type.
%     * "Formalizing π-Calculus in Guarded Cubical Agda" is a great introduction to the TCTT implementation in Guarded Cubical Agda
%     * Later credits: May solve the unguarded positive occurrence
