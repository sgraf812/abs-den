%if style == newcode
> module RelatedWork where
%endif

\section{Related Work}
\label{sec:related-work}

\subsubsection*{Call-by-need, Semantics}
Arguably, \citet{Josephs:89} described the first denotational by-need semantics,
predating the work of \citet{Launchbury:93} and \citet{Sestoft:97}, but not
the more machine-centric work on the
G-machine~\citep{Johnsson:84}.
We improve on \citeauthor{Josephs:89}'s work in that our encoding is
simpler, rigorously defined (\Cref{sec:mech-domain}) and proven adequate \wrt
\citeauthor{Sestoft:97}'s by-need semantics (\Cref{sec:adequacy}).
\citet{HackettHutton:19} define a denotational cost semantics for call-by-need,
but unfortunately we were unable to factor their approach into a productive
definition.

\citet{Sestoft:97} related the derivations of
\citeauthor{Launchbury:93}'s big-step natural semantics for our language to
the subset of \emph{balanced} small-step LK traces.
Balanced traces are a proper subset of our maximal LK traces: by nature of
big-step semantics, they exclude stuck and diverging traces.

Our denotational interpreter bears strong resemblance to
a denotational semantics~\citep{ScottStrachey:71},
or to a definitional interpreter~\citep{Reynolds:72}
featuring a finally encoded domain~\citep{Carette:07}
using higher-order abstract syntax~\citep{Pfenning:88}.
The key distinction to these approaches is that we generate small-step traces,
totally and adequately, observable by abstract interpreters.
\citet{AgerDanvyMidtgaard:04} successively transform a partial denotational
interpreter into a variant of the LK machine, going the reverse route of
\Cref{sec:adequacy}.

\subsubsection*{Coinduction and Fuel}
\citet{LeroyGrall:09} show that a coinductive encoding of big-step semantics
is able to encode diverging traces by proving it equivalent to a small-step
semantics, much like we did for a denotational semantics.
Our use of the later modality and Löb induction follows Iris~\citep{Jung:18} and
the topos-of-trees model of guarded recursion~\citep{Birkedal:12}.

Our |Trace| type class is appropriate for tracking ``pure'' transition events,
but it is not up to the task of modelling user input, for example.
A redesign of |Trace| inspired (and instantiated) by guarded interaction
trees~\citep{interaction-trees,gitrees} would help with that.

\subsubsection*{Mechanised Semantics and Verified Analyses}
\citet{Breitner:18} mechanised \citeauthor{Launchbury:93}'s natural semantics for
call-by-need in Isabelle and proved the cardinality analysis \emph{Call Arity}
safe~\citep{Breitner:15,Breitner:16}.
His proof relates analysis and machine directly, the coupling that
\Cref{sec:decomposed-proof} decomposes.
\citet{CacheraPichardie:10} certify a denotational abstract interpreter in Coq,
and Verasco~\citep{Jourdan:15} scales verified abstract interpretation to a
static analyser for C; both target first-order imperative languages.
\citet{DaraisVanHorn:16} mechanise calculational abstract interpretation with
constructive Galois connections, whereas our mechanisation replaces the Galois
connection of \Cref{fig:abstract-name-need} by the guarded relation of
\Cref{sec:mech-lr}.
Denotational semantics in guarded type theory covers PCF~\citep{Paviotti:15} and
recursive types~\citep{MogelbergPaviotti:16}; the by-need domain of
\Cref{sec:mech-domain} continues this line.
Like interaction trees~\citep{interaction-trees}, the interpreter remains
executable inside the proof assistant (\Cref{sec:mech-exec}).

\subsubsection*{Abstract Interpretation}
\citet{Cousot:21} recently condensed his seminal work rooted in \citet{Cousot:77}.
The book advocates a compositional, trace-generating semantics and then derives
compositional analyses by calculational design, and inspired us to attempt the same
for a higher-order language, delegating the domain construction to guarded recursive
type theory and defining the interpreter against Iris' interface of OFEs and
non-expansive maps~\citep{DiGianantonioMiculan:02,Jung:18}, whose model is the topos
of trees~\citep{Birkedal:12}.
Our generic denotational interpreter is a higher-order generalisation of the
generic abstract interpreter in \citet[Chapter 21]{Cousot:21}.
Our abstraction laws in \Cref{fig:abstraction-laws} correspond to Definition 27.1
and \Cref{thm:abstract-by-need} to Theorem 27.4.

\citet{Giacobazzi:25} study compositionality of best correct
approximations in abstract interpretation, whereas we aim for sound, computable
abstractions at the cost of some precision.

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
In our work, this is apparent in the |Domain| instances of |DName| and |DNeed|,
which rely on the monadic structure of the trace type |T|,
\citeauthor{Capretta:05}'s delay monad enriched with events.
Decomposing such structure into a layer of reusable monad transformers has been
the subject of \citet{Darais:15} and \citet{Keidel:19}.

A big advantage of the big-step framework of \citet{Keidel:18} is that
soundness proofs are modular in the sense of \Cref{sec:mod-subst}.
Our mechanisation achieves a comparable factoring: the fundamental lemma of
\Cref{sec:mech-lr} is proved once, and each combinator contributes one closure
field.

\subsubsection*{Summaries of Functionals \vs Call Strings}
\citet{Lomet:77} used procedure summaries to capture aliasing effects,
crediting the approach to untraceable reports by \citet{Allen:74} and
\citet{Rosen:75}.
\citet{SharirPnueli:78} were aware of the work of both \citet{Cousot:77} and \citet{Allen:74},
and generalised aliasing summaries into the ``functional approach'' to
interprocedural data flow analysis, distinguishing it from the ``call strings
approach'' (\ie $k$-CFA).

That is not to say that the approaches cannot be combined;
inter-modular analysis led \citet[Section 3.8.2]{Shivers:91} to implement
the $\mathit{xproc}$ summary mechanism.
Some AAM-inspired approaches \citep{Nguyen:14} support a fixed set of
summaries, but require custom reductions in the semantics.

\citet{Mangal:14} have shown that a summary-based analysis can be equivalent
to $\infty$-CFA for arbitrary complete lattices and outperform 2-CFA in both
precision and speed.
Summary-based analyses scale better because a function is analysed once and its
summary reused at every call site.
To illustrate why they can also be more precise, consider the Haskell expression

< let f n = let i y = y in if n == 0 then 0 else i (f (n-1) + 1) in f 42{-"."-}

It is evident that |i| is evaluated at most once, and |evalUsg| infers this fact
for the respective subexpression.
$k$-CFA (for $k < 42$), by contrast, conflates the recursive activations of |i|
and reports |i| as used many times.

\subsubsection*{Cardinality Analysis} More interesting cardinality
analyses involve the inference of summaries called \emph{demand
transformers}~\citep{Sergey:14}, such as implemented in the Demand Analysis of
the Glasgow Haskell Compiler.

