\section{Introduction}
\label{sec:introduction}

As an implementor of a programming language, it is customary to automatically
glean facts about a program such as ``this program is well-typed'', ``this
higher-order function is always called with argument $\Lam{x}{x+1}$'' or ``this
program never evaluates $x$'' by way of static analysis.

If the implementation language is a functional one, then often such static
analyses are formulated as a function defined by \emph{structural recursion} on
the input term.
For example, given an application expression $(\pe_1~\pe_2)$,
the property ``$(\pe_1~\pe_2)$ never evaluates $x$'' can be \emph{conservatively
approximated} (here: It's OK to say ``No'' more often) by the property ``$\pe_1$
and $\pe_2$ never evaluate $x$''.

Such a structural formulation is quite convenient:
(1) Structural recursion gives an immediate proof of termination and can
    further be exploited in other inductive proofs.
(2) A structural definition is often \emph{compositional}, meaning that
    if you replace a sub-expression by another sub-expression with the same
    result under the function, the overall result of the containing expression
    does not change. This makes it easy for humans to understand and reason
    about.

For static analyses, especially more complicated ones, it is good practice to
provide a proof of correctness of some sort. If the correctness statement can
be expressed in terms of a \emph{denotational semantics}
\cite{ScottStrachey:71}, then the recursion structure of analysis function and
semantics function line up nicely. As a result, the proof of correctness can be
conducted by simple induction over the expression.

Alas, it turns out that the traditional denotational semantics for lambda
calculus (like the traditional notion of natural semantics) conflates diverging
and stuck programs. Consider the following program using recursive let that is
infinitely-looping
\[
  \pe_{loop} \triangleq \Let{id}{\Lam{x}{x}}{\Let{loop}{id~loop}{loop}}
\]
The traditional denotational semantics after Scott and Strachey would equate all
of the following programs:
$\semscott{\pe_{loop}}_ρ = \semscott{\Let{loop}{id~loop}{loop}}_ρ =
\semscott{\mathsf{segfault}}_ρ = \bot$.
Note that the first program has an infinite loop, the second one a scoping bug
and the last one is a straight out crash in the style of an imprecise exception
\cite{imprecise-exceptions}.
To a compiler developer, this conflation is both a reason for joy (more
optimisation opportunities) and a reason for reflection (users didn't expect
their infinite loop to be optimised into a crash). Such issues come up in
practice \sg{cite GHC issues}.

More seriously, it is impossible to prove that a static analysis does not
misoptimise infinite behaviors by way of denotational semantics.
(a) The \emph{potential liveness} analysis that says ``$\pe_{loop}$ never
evaluates $id$'' could be proven ``correct''.
(b) A type analysis that says ``$\Let{loop}{id~loop}{loop}$ is well-typed'' can
still be proven progressing (assuming that the system is not strongly
normalising), because $\pe_{loop}$ should be well-typed and is
denotationally equivalent to the former.
(c) Imagine that $id$ was passed as an argument to $loop$ instead, \eg
$...\ \Let{loop}{\Lam{f}{f~(loop~f)}}{loop~id}$. Then a control-flow analysis
\cite{Shivers:91} that says ``$f$ is never bound to $id$'' can be proven correct
in terms of the denotational semantics.

Furthermore, although it is sensible (in the terminating case) to ask whether or
not $x$ is \emph{never} evaluated in terms of the denotational semantics, asking
whether $x$ is evaluated \emph{more than once} is not, for the same reason that
traditional denotational semantics is not able to discern call-by-name from
call-by-need. Yet, to the Glasgow Haskell Compiler, this distinction is very
much of concern!

When denotational semantics fails the compiler developer, they turn to a
correctness criterion in terms of a \emph{structural operational semantics}.
This was the approach taken by \cite{cardinality} to prove evaluation
cardinality properties such as potential liveness. The drawback of this approach
is the immense proof complexity arising from the disconnect between a structural
definition and a transition system; matters such as substitution, multiple heap
activations of the let binding, non-determinism and fixpoint induction abound.
It is hard to raise confidence in such a proof without full mechanisation.

One could adopt the approach of \emph{Abstracting Abstract Machines} \cite{aam}
and let the structure of the semantics dictate the structure of the
analysis for a re-usable proof of correctness via abstract interpretation
\cite{Cousot:21}.
However, that is not how the static analyses work that the author is familiar with.
For example, it would be quite an effort to rewrite the neat, compositional
analyses of the Glasgow Haskell Compiler into a fixpoint iteration on the
approximated states of an abstract transition system.

The contributions of this work are as follows:
\begin{itemize}
  \item In \Cref{sec:problem}, we give a more formal illustration of the
    problems we just introduced and are inclined to solve.
  \item In \Cref{sec:semantics}, we give a \emph{structurally-defined} semantics
    for lambda calculus that is \emph{able to discern stuck, diverging and
    converging programs}. Furthermore, it is a semantics for \emph{call-by-need}
    lambda calculus that is distinct from similar ones for call-by-name or
    call-by-value. We believe that our semantics is the first with the
    aforementioned two qualities and prove it correct \wrt a standard
    operational semantics. The idea borrows heavily from the idea of a maximal
    prefix trace semantics advocated by \citep{Cousot:21}.
  \item The semantics in \Cref{sec:semantics} is one generating \emph{stateful}
    traces in a standard operational semantics, and serves mostly as a
    convenient bridge for proving bisimulation. In \Cref{sec:stateless} we will
    define an equivalent, but more convenient \emph{stateless} semantics and we
    will see how to recover necessary state as needed.
  \item We employ the stateless semantics as a collecting semantics and derive
    $\semlive{\wild}$ by calculational design \cite{Cousot:21}.
    Similar derivations will be made for a simple type system as well as for
    control flow analysis.
  \item Talk about prototype in Haskell?
  \item Related Work
\end{itemize}
