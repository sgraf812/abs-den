\section{Problem Statement}
\label{sec:problem}

\subsection{Notation}

Collection of stuff to explain, for now:
\begin{itemize}
  \item $\triangleq$ for defining an object (defn eq), rather than $=$
  \item $\text{letrec}$
    The (meta-level, math) notation
    \[
    \text{letrec}~l.~\many{x = rhs_x} ~ l = rhs_{l} ~ \many{y = rhs_y}~\text{in}~body
    \]
    where $l$ might occur freely in any $rhs_{\wild}$ and $body$, is syntactic sugar for
    \[
    snd(\lfp(\fn{(l,\wild)}{\text{let}~\many{x = rhs_x} ~ \many{y = rhs_y}~\text{in}~(rhs_{l},body)}))
    \]
    Where $\lfp$ is the least fixpoint operator and $snd(a,b) = b$. Clearly, this
    desugaring's use of $\lfp$ is well-defined for its use on elements of the
    powerset lattice $\LiveD$.

    But \cite{Shivers:91} uses the similar $\text{whererec}$ and gets by without
    ever explaining it, so we might as well.
\end{itemize}

\subsection{Lax Adequacy and Potential Liveness Analysis}

The fact ``never evaluates $x$'' can be established by a liveness analysis such
as $\semlive{\wild}$, depicted in \Cref{fig:liveness}, analysing a call-by-name
(or call-by-need? Can you tell?) lambda calculus with recursive let bindings
defined in \Cref{fig:scott-syntax}.
%It is in \emph{administrative normal form} (ANF),
%that is, the arguments of applications are restricted to be variables, so
%the difference between call-by-name and call-by-value manifests purely in
%the semantics of let.
Assuming that all program variables are distinct, the result of
$\semlive{\wild}$ is an element $d ∈ \LiveD$, itself a subset of all program
variables that are \emph{potentially live}.
Intuitively, if $x \not∈ d$, then $x$ is considered to be \emph{dead}, \eg,
never evaluated. The \emph{requirement} (in the sense of informal specification)
on an assertion such as ``$x$ is dead'' is that if $x$ was let-bound (rather
than lambda-bound), we can replace its right-hand side with whatever expression
we want, perhaps to minimise code size.

%More formally, given an expression $\pe$ and a mapping $ρ : \Var \to \LiveD$
%that describes which variables are potentially live after any one of $\pe$'s
%free variables have been evaluated deeply, $\semlive{\pe}_ρ$ is the set of
%potentially live variables after a deep evaluation of $\pe$.

Without going into further detail of how exactly $\semlive{\wild}$ produces a
result, note that its definition is \emph{compositional}, that is, by
\emph{structural recursion} over the input term, as is a common scheme in
functional programming. Apart from a trivial proof of termination, structural
definitions allow humans (and proofs) to reason about what a function returns
(``What is live in $(λx. x+y)~z$?'')
for a complex expression by considering what the function returns on its parts
(``I know that $y$ is live in $(λx.x+y)$ and $z$ is live in $z$, so both $y$ and
$z$ are live in $(λx. x+y)~z$ by the application rule'').

Squinting a bit, we find that $\semlive{\wild}$ looks a lot like the function
to its left in \Cref{fig:denotational}. $\semscott{\wild}$ is the canonical
denotational semantics for lambda calculus after Scott and Strachey
\cite{ScottStrachey:71}.
The structure of $\semlive{\wild}$ lines up quite nicely with $\semscott{\wild}$:
It recurses in all the right places, the variable case is an exact match and
the other three cases differ only very slightly.

We can now give a formal definition of deadness in terms of this semantics:

\begin{definition}[Deadness]
  Let $\pe$ be an expression and $\px$ a variable.
  $\px$ is \emph{dead} in $\pe$ if and only if, for all $ρ ∈ Var \to \ScottD$
  and $d_1, d_2 ∈ \ScottD$ we have
  $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
  Otherwise, $\px$ is \emph{potentially live}.
\end{definition}

Now, consider a program $\Let{x}{\pe_1}{\pe_2}$. If $x$ is dead in $\pe_2$,
then a compiler can drop the entire let binding, because
$\semscott{\Let{x}{\pe_1}{\pe_2}}_ρ = \semscott{\pe_2}_{ρ[x↦d]} =
\semscott{\pe_2}_ρ$ (for a suitable $d$). So our definition of deadness is not
only simple to grasp, but also simple to exploit.

\begin{figure}
\begin{minipage}{\textwidth}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}       & \px,\py & ∈ & \Var    &     & \\
  \text{Expressions}     &     \pe & ∈ & \Exp    & ::= & \px \mid \Lam{\px}{\pe} \mid \pe~\px \mid \Let{\px}{\pe_1}{\pe_2} \\
  \\
  \text{Scott Domain}    &       d & ∈ & \ScottD & =   & [\ScottD \to_c \ScottD]_\bot \\
  \text{Liveness Domain} &  d^{∃l} & ∈ & \LiveD  & =   & \poset{\Var} \\
 \end{array} \\
\end{array}\]
\subcaption{Syntax of expressions and domain equations}
  \label{fig:scott-syntax}
\end{minipage}
\begin{minipage}{0.52\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semscott{\wild} \colon \Exp → (\Var \to \ScottD) → \ScottD } } \\
  \\[-0.5em]
  \semscott{\px}_ρ & {}={} & ρ(\px) \\
  \semscott{\Lam{\px}{\pe}}_ρ & {}={} & d ↦_c \semscott{\pe}_{ρ[\px ↦ d]} \\
  \semscott{\pe~\px}_ρ & {}={} & \begin{cases}
     f(ρ(x)) & \text{if $\semscott{\pe} = \FunV(f)$}  \\
     \bot   & \text{otherwise}  \\
   \end{cases} \\
  \semscott{\Let{\px}{\pe_1}{\pe_2}}_ρ & {}={} &
    \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semscott{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\subcaption{Denotational semantics after Scott}
  \label{fig:denotational}
\end{minipage}%
\begin{minipage}{0.5\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semlive{\wild} \colon \Exp → (\Var → \LiveD) → \LiveD } } \\
  \\[-0.5em]
  \semlive{\px}_ρ & {}={} & ρ(\px) \\
  \semlive{\Lam{\px}{\pe}}_ρ & {}={} & \semlive{\pe}_{ρ[\px ↦ \varnothing]} \\
  \\[-0.5em]
  \semlive{\pe~\px}_ρ & {}={} & \semlive{\pe} ∪ ρ(\px) \\
  \\[-0.5em]
  \semlive{\Let{\px}{\pe_1}{\pe_2}}_ρ& {}={} & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = \{\px\} \mathord{∪} \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semlive{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\subcaption{Naïve potential liveness analysis}
  \label{fig:liveness}
\end{minipage}%
  \label{fig:intro}
\caption{Connecting liveness analysis to denotational semantics}
\end{figure}
We can now try to prove our liveness analysis correct in terms of this notion of
deadness:

\newcommand{\tr}{\ensuremath{\tilde{ρ}}}

\begin{theorem}[Correctness of $\semlive{\wild}$]
  \label{thm:semlive-correct-1}
  Let $\pe$ be an expression and $\px$ a variable.
  Then $\px$ is dead in $\pe$ whenever
  there exists $\tr ∈ \Var \to \LiveD$ such that
  $\tr(\px) \not⊆ \semlive{\pe}_{\tr}$.
\end{theorem}
\begin{proof}
  By induction over $\pe$. Full proof in the Appendix.
\end{proof}

The proof capitalises on the similarities in structure by using induction on the
program expression, hence it is simple and direct. Often, such a proof needs to
assume conformance to some logical relation to strengthen the induction hypothesis
for the application case, but for our very simple analysis we do not need to be
so crafty.

Unfortunately, our notion of deadness is also insufficient. Consider the
infinitely-looping program
\[
  \pe_{loop} \triangleq \Let{id}{\Lam{x}{x}}{\Let{loop}{id~loop}{loop}}
\]
Its denotation is $\semscott{\pe_{loop}}_ρ = \bot$ in every environment $ρ$ since
$loop$ never terminates, hence $\pe_{loop}$ and its subexpression $loop$ are dead in
all variables, including $id$.

Imagine a compiler exploiting the deadness of $id$ to optimise to
$\Let{loop}{id~loop}{loop}$ or even just $segfault$! The former program is not
even well-scoped (thus stuck at some point), and the latter program crashes
immediately instead of running into an infinite loop, yet both programs have the
same denotation $\bot$.

We have just seen how the traditional notion of adequacy in denotational
semantics (similar to the natural semantics) does not give distinct denotations to
programs that are very much observationally distinct (stuck, looping, crashing)
to a compiler developer and users of said compiler.

%\sg{Move to related work.}
%There have been attempts to discern crashes from other kinds of loops, such as
%\cite{imprecise-exceptions}. Unfortunately, in Section 5.3 they find it
%impossible give non-terminating programs a denotation other than $\bot$, which
%still encompasses all possible exception behaviors.

There is no use in fretting and the compiler developer will instead
try to find a suitable definition of correctness in terms of a \emph{structural
operational semantics}. Unfortunately, such a semantics does not share structure
with our neat and, ultimately, sound definition $\semlive{\wild}$. That severely
complicates both the correctness criterion and the associated proof with
details such as substitution, thinking about multiple activations of the same
let binding leading to heap allocation, \etc.

Furthermore, the weakness of the accepted notion of adequacy is not unique to
liveness analysis; it concerns progress proofs for type systems (is the
term stuck or diverging?) and correctness proofs for control-flow analysis
\cite{Shivers:91} as well (does the analysis approximate the control-flow of
diverging programs?).

%The free variable case $\semlive{\wild}$ simply looks up
%what variables are potentially live when evaluating $x$ in $ρ$.
%
%Most interesting is its handling of lambda abstractions:
%Even if evaluating a lambda does not evaluate any variables whatsoever, $\semlive{\wild}$
%conservatibely accounts for potential beta reductions in the future (``deep
%evaluation'') by returning the potentially live varables of the lambda body
%$\pe$ minus the lambda-bound variable
%\sg{Removing the lambda-bound variable isn't strictly necessary as they
%are never added in the first place. Yet, omission may lead to a few head
%scratches...}.
%The recursive call into the lambda body adds an entry to $ρ$ for the variable
%$x$ bound by the lambda, which may occur free in $\pe$. Its mapping to the empty
%set reveals another interesting invariant about $\semlive{\wild}$: That any
%evaluation of lambda-bound variables has been accounted for by the application
%site.
%
%Indeed, the application case $\semlive{\pe~\px}$ simply unites the potentially
%live variables of the argument $ρ(x)$ with the ones from the application head,
%whether the head evaluates its argument or not.
%
%Finally, $\semlive{\Let{\px}{\pe_1}{\pe_2}}$ extends $ρ$ in a useful way,
%analysing $\pe_2$ in the extended environment $ρ'$ that contains an entry
%describing the potentially live variables of $\pe_1$, including $\px$ to
%symbollically stand for liveness of $\pe_1$.
%
%
%Intuition suggests that the facts produced by $\semlive{\wild}$ is correct in
%some sense,

