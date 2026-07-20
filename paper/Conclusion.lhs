%if style == newcode
> module Conclusion where
%endif

\section{Conclusion and Future Work}
\label{sec:conclusion}

A single denotational interpreter, parameterised by its semantic domain, is both a
dynamic semantics and a static analysis, depending on how we instantiate it. We used
it to define a summary-based usage analysis and to prove that analysis sound for
call-by-need, and we mechanised the whole by-need development in Lean using the algebra
of Iris.
The proof stays manageable because it comes apart into three reusable layers:
one removes the abstract machine, one removes the interpreter, and the last
removes the by-need domain, leaving only the analysis.

The analysis we most want to reach is GHC's Demand Analysis, the cardinality
analysis that GHC ships~\citep{Sergey:14}. Its demand transformers are summaries of
the same kind as ours, so it fits the framework, which would give it a first modular,
mechanised soundness proof, and a setting precise enough for the refinements that
reach beyond \citet{Sergey:14}. The remaining work is a domain rich enough for its
sub-demands and a soundness argument tuned to call-by-need.

More broadly, our domain construction opens Cousot's calculational design to
higher-order languages. That method~\citep{Cousot:21} derives an analysis, and its
soundness proof, by algebraic manipulation of a compositional, trace-generating
semantics, so far only for first-order languages. Our interpreter supplies such a
semantics for a higher-order language, unblocking summary-based analyses that infer
operational properties against a trace-generating semantics. The difficulty the
framework meets, soundly abstracting higher-order mutable state, is shared by strict
languages with mutable references and stateful objects, so the approach should reach
them too. We expect a great deal of new research to grow there.
