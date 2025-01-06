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

\subsubsection*{Call-by-need, Semantics}
Arguably, \citet{Josephs:89} described the first denotational by-need semantics,
predating the work of \citet{Launchbury:93} and \citet{Sestoft:97}, but not
the more machine-centric work on the
G-machine~\citep{Johnsson:84}.
We improve on \citeauthor{Josephs:89}'s work in that our encoding is
simpler, rigorously defined (\Cref{sec:totality}) and proven adequate \wrt
\citeauthor{Sestoft:97}'s by-need semantics (\Cref{sec:adequacy}).
\citet{HackettHutton:19} define a denotational cost semantics for call-by-need,
but unfortunately we were unable to factor their approach into a productive
definition, \cf \Cref{sec:clair}.

\citet{Sestoft:97} related the derivations of
\citeauthor{Launchbury:93}'s big-step natural semantics for our language to
the subset of \emph{balanced} small-step LK traces.
Balanced traces are a proper subset of our maximal LK traces that --- by nature
of big-step semantics --- excludes stuck and diverging traces.

Our denotational interpreter bears strong resemblance to
a denotational semantics~\citep{ScottStrachey:71},
or to a definitional interpreter~\citep{Reynolds:72}
featuring a finally encoded domain~\citep{Carette:07}
using higher-order abstract syntax~\citep{Pfenning:88}.
The key distinction to these approaches is that we generate small-step traces,
totally and adequately, observable by abstract interpreters.
%
%\subsubsection*{Definitional Interpreters}
%\citet{Reynolds:72} introduced ``definitional interpreter'' as an
%umbrella term to classify prevalent styles of interpreters for higher-order
%languages at the time.
%Chiefly, it differentiates compositional interpreters that necessarily use
%higher-order functions of the meta language from those that do not, and are
%therefore non-compositional.
%Among its key contributions is \emph{defunctionalisation}, a key transformation
%for turning a definition of the former into one of the latter.
%The former correspond to (partial) denotational interpreters, whereas the latter
%correspond to big-step interpreters.
%By giving by-name and by-value evaluation strategies for our denotational
%interpreter, our work is somewhat contradicting Reynolds' pitch that
%definitional interpreters inherit the evaluation strategy from their host
%language.
\citet{AgerDanvyMidtgaard:04} successively transform a partial denotational
interpreter into a variant of the LK machine, going the reverse route of
\Cref{sec:adequacy}.

\subsubsection*{Coinduction and Fuel}
\citet{LeroyGrall:09} show that a coinductive encoding of big-step semantics
is able to encode diverging traces by proving it equivalent to a small-step
semantics, much like we did for a denotational semantics.
%\citet{Owens:16} recognise the usefulness of definitional interpreters for
%correctness proofs, albeit in big-step style and using a fuel-based encoding of
%infinite behaviors.
The work of \citet{Atkey:13,tctt} had big influence on our use of the later
modality and Löb induction.

Our |Trace| type class is appropriate for tracking ``pure'' transition events,
but it is not up to the task of modelling user input, for example.
A redesign of |Trace| inspired (and instantiated) by guarded interaction
trees~\citep{interaction-trees,gitrees} would help with that.

%While working out how to embed |evalNeed| in Guarded Cubical Agda~\citep{tctt} and
%then attempting mechanised proofs about it, we very soon decided
%that we were not up to the task, not least due to lack of automation and the
%general perceived tediousness of Cubical types.
%Perhaps we shall try again with an encoding of guarded recursion rather than
%using a language where it is primitive.

%\subsubsection*{Contextual Improvement}
%Abstract interpretation is useful to prove that an analysis approximates
%the right trace property, but it does not help to prove an \emph{optimisation}
%conditional on some trace property sound, yet alone an
%\emph{improvement}~\citep{MoranSands:99}.
%%If we were to prove update avoidance~\citep{Gustavsson:98} correct, would we use
%If we were to prove dead code elimination correct based on our notion of
%absence, would we use our denotational interpreter to do so?
%Probably not; we would try to conduct as much of the proof as possible in the
%equational theory, \ie on syntax.
%If need be, we could always switch to denotational interpreters via
%\Cref{thm:need-adequacy-bisimulation}, just as in \Cref{thm:absence-denotational}.
%\citet{HackettHutton:19} have done so as well.

\subsubsection*{Abstract Interpretation and Relational Analysis}
\citet{Cousot:21} recently condensed his seminal work rooted in \citet{Cousot:77}.
The book advocates a compositional, trace-generating semantics and then derives
compositional analyses by calculational design, and inspired us to attempt the same.
However, while \citet{Cousot:94,Cousot:02} work with denotational semantics
for a higher-order language, it was unclear to us how to derive a compositional,
\emph{trace-generating} semantics for a higher-order language.
The required changes to the domain definitions seemed daunting, to say the
least.
Our solution delegates this complexity to the underlying theory of guarded
recursive type theory~\citep{tctt}.

% TODO: Comment back in for final version
%We deliberately tried to provide a simple framework and thus stuck to cartesian
%(\ie pointwise) abstraction of environments as in \citet[Chapter
%27]{Cousot:21}, but we expect relational abstractions to work just as well.
%Our generic denotational interpreter is a higher-order generalisation of the
%generic abstract interpreter in \citet[Chapter 21]{Cousot:21}.
%Our abstraction laws in \Cref{fig:abstraction-laws} correspond to Definition 27.1
%and \Cref{thm:abstract-by-need} to Theorem 27.4.

\subsubsection*{Abstractions of Reachable States}
CFA~\citep{Shivers:91} computes a useful control-flow graph abstraction for
higher-order programs, thus lifting classic intraprocedural analyses such as
constant propagation to the interprocedural setting.

\citet{MontaguJensen:21} derive CFA from small-step traces.
We think that a variant of our denotational interpreter would be a good fit for
their collecting semantics.
Specifically, the semantic inclusions of Lemma 2.10 that govern the transition
to a big-step style interpreter follow simply by adequacy of our interpreter,
\Cref{thm:need-adequacy-bisimulation}.

Abstracting Abstract Machines~\citep{aam} derives
a computable \emph{reachable states semantics}~\citep{Cousot:21} from any
small-step semantics, by bounding the size of the heap.
Many analyses such as control-flow analysis arise as abstractions of reachable
states.
\citet{adi} and others apply the AAM recipe to big-step interpreters in the style
of \citeauthor{Reynolds:72}.

An advantage of operational semantics and AAM compared to our denotational
approach is the focus on syntax, enabling proofs entirely within an equational
theory.
In our framework, proofs may appeal to parametricity or otherwise must take
caution to consider definable elements only.

Whenever AAM is involved, abstraction follows some monadic structure inherent to
dynamic semantics~\citep{Sergey:13,adi}.
In our work, this is apparent in the |Domain (D τ)| instance depending on
|Monad τ|.
Decomposing such structure into a layer of reusable monad transformers has been
the subject of \citet{Darais:15} and \citet{Keidel:19}.
%The trace transformers of \Cref{sec:interp} enable reuse along a different dimension.
%Likewise, \citet{Keidel:23} discusses a sound, declarative approach to reuse
%fixpoint combinators which we hope to apply in implementations of our framework
%as well.

A big advantage of the big-step framework of \citet{Keidel:18} is that
soundness proofs are modular in the sense of \Cref{sec:mod-subst}.
In the future, we hope to modularise the proof for
\Cref{thm:abstract-by-need}.

\subsubsection*{Summaries of Functionals \vs Call Strings}
\citet{Lomet:77} used procedure summaries to capture aliasing effects,
crediting the approach to untraceable reports by \citet{Allen:74} and
\citet{Rosen:75}.
\citet{SharirPnueli:78} were aware of the work of both \citet{Cousot:77} and \citet{Allen:74},
and generalised aliasing summaries into the ``functional approach'' to
interprocedural data flow analysis, distinguishing it from the ``call strings
approach'' (\ie $k$-CFA).
%The former models a procedure call by the abstract transformer function
%induced by the intraprocedural analysis, and hence requires computing fixpoints
%over function-valued lattices barring subsequent abstraction.
%The latter is a predecessor to $k$-CFA and has a simpler operational reading.

That is not to say that the approaches cannot be combined;
inter-modular analysis led \citet[Section 3.8.2]{Shivers:91} to implement
the $\mathit{xproc}$ summary mechanism.
He also acknowledged the need for accurate intra-modular summary mechanisms for
scalability reasons in Section 11.3.2.

We wonder how the powerset-centric AAM approach could be
parameterised over an arbitrary summary mechanism such as in our framework.
While some AAM-inspired approaches \citep{Nguyen:14} support a fixed set of
summaries, these require custom reductions in the semantics.

\citet{Mangal:14} have shown that a summary-based analysis can be equivalent
to $\infty$-CFA for arbitrary complete lattices and outperform 2-CFA in both
precision and speed.
%\Cref{sec:summaries} demonstrates why summary-based analyses scale better.
%In the Appendix we argue why they can also be more precise
%To illustrate why they can also be more preicse, consider the Haskell expression
%
%< let f n = let i y = y in if n == 0 then 0 else i (f (n-1) + 1) in f 42{-"."-}
%
%The definition of |f| is a complicated way to define the identity function.
%Nevertheless, it is evident that |i| is evaluated at most once, and
%|evalUsg| would infer this fact for the respective subexpression.
%On the other hand, $k$-CFA (for $k < 42$) would confuse different recursive
%activations of |i|, thus conservatively attributing evaluations multiple times,
%to the effect that |i| is not inferred as used at most once.

%Given a semantic description of abstract values, it is likely
%that the implementation of |Domain| can be synthesised using the approach of
%\citet{Kalita:2022}.

\subsubsection*{Cardinality Analysis} More interesting cardinality
analyses involve the inference of summaries called \emph{demand
transformers}~\citep{Sergey:14}, such as implemented in the Demand Analysis of
the Glasgow Haskell Compiler.
%It is very similar to Clairvoyant call-by-value (CCbV)~\citep{HackettHutton:19},
%suggesting that the former is an abstract interpretation of the latter.
%Since CCbV is cost equivalent to call-by-need, such an abstraction relationship
%could be used to prove that Demand Analysis infers operational properties such
%as absence in call-by-need.
%Alas, since the Clairvoyant instantiation of our denotational interpreter is
%partial, such a proof would carry no meaning for partial inputs.
We intend to build on our framework to describe improvements to Demand Analysis in
the future.
However, a soundness proof would require a different Galois connection than
\Cref{fig:abstract-name-need}, because Demand Analysis is not sound \wrt by-name
evaluation.

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
