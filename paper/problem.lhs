\section{Problem Statement}
\label{sec:problem}

By way of the poster child example of potential liveness analysis, we showcase
how the notion of adequacy in traditional denotational semantics is too weak
to substantiate a correctness criterion. Further consideration of more elaborate
cardinality analyses~\cite{cardinality} and quantitative type
systems~\cite{Atkey:18} characterise this weakness not only in terms of
unobservable divergence but also in terms of evaluation cardinality.

%\subsection{Notation}
%
%Collection of stuff to explain, for now:
%\begin{itemize}
%  \item $\triangleq$ for defining an object (defn eq), rather than $=$
%  \item $\text{letrec}$
%    The (meta-level, math) notation
%    \[
%    \text{letrec}~l.~\many{x = rhs_x} ~ l = rhs_{l} ~ \many{y = rhs_y}~\text{in}~body
%    \]
%    where $l$ might occur freely in any $rhs_{\wild}$ and $body$, is syntactic sugar for
%    \[
%    snd(\lfp(\fn{(l,\wild)}{\text{let}~\many{x = rhs_x} ~ \many{y = rhs_y}~\text{in}~(rhs_{l},body)}))
%    \]
%    Where $\lfp$ is the least fixpoint operator and $snd(a,b) = b$. Clearly, this
%    desugaring's use of $\lfp$ is well-defined for its use on elements of the
%    powerset lattice $\LiveD$.
%
%    But \cite{Shivers:91} uses the similar $\text{whererec}$ and gets by without
%    ever explaining it, so we might as well.
%\end{itemize}

\subsection{Potential Liveness Analysis}

\begin{figure}
\begin{minipage}{\textwidth}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}       & \px,\py & ∈ & \Var    &     & \\
  \text{Expressions}     &     \pe & ∈ & \Exp_0  & ::= & \px \mid \Lam{\px}{\pe} \mid \pe~\px \mid \Let{\px}{\pe_1}{\pe_2} \\
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

\Cref{fig:scott-syntax} defines the syntax of a lambda calculus with recursive
let bindings. The calculus is factored into \emph{administrative normal form},
that is, the arguments of applications are restricted to be variables, so the
difference between call-by-name and call-by-value manifests purely in the
semantics of $\mathbf{let}$.

This semantics is given in \Cref{fig:denotational}, the standard denotational
call-by-name semantics $\semscott{\wild}$ after \citep{ScottStrachey:71}, giving
meaning to our syntax by means of the infamous Scott domain $\ScottD$.
Squinting a bit, we find that it looks quite similar to the function
on its right in \Cref{fig:liveness}, depicting a naïve potential liveness
analysis $\semlive{\wild}$. (It is naïve in that its treatment of function
application assumes that every function deeply evaluates its argument.)

Assuming that all program variables are distinct (a silent assumption from
here on throughout), the result of $\semlive{\wild}$ is an element $d ∈ \LiveD$,
itself a subset of all program variables that are \emph{potentially live}.
Intuitively, if $x \not∈ d$, then $x$ is considered to be \emph{dead}, \eg,
\emph{never evaluated}; thus $\semlive{\wild}$ can be used to infer facts of
the form ``$\pe$ never evaluates $x$'' from the introduction.
The \emph{requirement} (in the sense of informal specification) on an assertion
such as ``$x$ is dead'' in a program like $\Let{x}{\pe_1}{\pe_2}$ is that we
may rewrite to $\pe_2$ (perhaps to reduce allocations or code size) without
observing any change in semantics.

This can be made formal in the following definition of deadness in terms of
$\semscott{\wild}$:

\begin{definition}[Deadness]
  Let $\pe$ be an expression and $\px$ a variable.
  $\px$ is \emph{dead} in $\pe$ if and only if, for all $ρ ∈ \Var \to \ScottD$
  and $d_1, d_2 ∈ \ScottD$, we have
  $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
  Otherwise, $\px$ is \emph{potentially live}.
\end{definition}

Indeed, if we know that $x$ is dead, then the following equation justifies our
rewrite above: $\semscott{\Let{x}{\pe_1}{\pe_2}}_ρ = \semscott{\pe_2}_{ρ[x↦d]} =
\semscott{\pe_2}_ρ$ (for all $ρ$ and the suitable $d$).
So our definition of deadness is not only simple to grasp, but also simple to
exploit.

We can now try to prove our liveness analysis correct in terms of this notion of
deadness. After a bit of trial and error, we could arrive at the following
theorem:

\newcommand{\tr}{\ensuremath{\tilde{ρ}}}

\begin{theorem}[Correctness of $\semlive{\wild}$]
  \label{thm:semlive-correct-1}
  Let $\pe$ be an expression and $\px$ a variable.
  Then $\px$ is dead in $\pe$ whenever
  there exists $\tr ∈ \Var \to \LiveD$ such that
  $\tr(\px) \not⊆ \semlive{\pe}_{\tr}$.
\end{theorem}
\begin{proof}
  By induction over $\pe$. The full proof can be found in
  \Cref{prf:semlive-correct-1}.
\end{proof}

Let us stop and reflect about this theorem for a bit.
Whenever thinking about the witnessing $\tr$ giving values to free variables of
$\pe$, it helps to think that $\tr(\py) \triangleq \{ \py \}$, then the
intuitive notion of deadness translates directly.
\footnote{In fact, it can be proven that \emph{if} any $\tr$ exists, then the
``diagonal'' $\tr$ is also a witness.}

It is surprising that the theorem does not relate $\tr$ with $ρ$; after all,
$ρ(\py)$ might be bound to the \emph{meaning} of an expression that is
potentially live in $\px$, and we have no way to observe that.
On the other hand, our notion of deadness does not vary $ρ(\py)$, only
$ρ(\px)$, so for all intents and purposes, the proof may assume that $ρ(\py)$
is dead in $\px$. The analysis, on the other hand, encodes transitive deadness
relationships via $\tr(\px) ⊆ \tr(\py)$ for the let-bound $\py$ in the
$\mathsf{let}$ case, thus the proof succeeds.

The proof capitalises on the similarities in structure by using induction on the
program expression, hence it is simple and direct, at just under a page of
accessible prose. Often, such a proof needs to assume conformance to some
logical relation to strengthen the induction hypothesis for the application
case, but for our very simple analysis we do not need to be so crafty.

Nevermind our confidence in the ultimate correctness of $\semlive{\wild}$,
we have seen in the introduction that our notion of deadness is insufficient.
Recall again the infinitely-looping program $\pe_{loop}$ in \eqref{eqn:loop};
our notion of deadness finds that $x$ is dead in $\pe_{loop}$ and the compiler
would be justified to optimise to $\Let{loop}{id~loop}{loop}$ based on that
fact.

Fortunately, $id ∈ \semlive{\pe_{loop}}$, so our analysis seems to behave more
benign than ``necessary''. We are hopeful that it adheres to a stricter notion
of deadness, perhaps in terms of a structural operational semantics such as
Sestoft's Mark II machine \cite{Sestoft:97} (an obvious pick for call-by-value
would be a CESK machine \cite{Felleisen:87} or a simpler derivative thereof).
For example, (recall that the a state in Sestoft's transition system consists of
heap, control, environment, stack, in this order)

\begin{definition}[Deadness, Mark II]
  Let $\pe$ be an expression and $\px$ a variable.
  $\px$ is \emph{dead} in $\pe$ if and only if
  there exists no sequence of transitions
  $(\{\},\pe,\{\},[]) \smallstep^* (Γ,\px,E,S)$ such that the next transition
  would apply the variable lookup rule $var_1$.
  Otherwise, $\px$ is \emph{potentially live}.
\end{definition}

While more accurate a definition, the corresponding correctness proof
requires an elaborate setup, extending the liveness analysis (or the correctness
criterion) to every component of the machine states, \eg, the heap $Γ$,
the environment $E$ and the stack $S$. Doing so usually culminates in
an extensive logical relation such as $\sim_V$ in \cite[Theorem
2.21]{Nielson:99} or the ``well-typed'' relation for elaborated configurations
in \cite[Lemma 4.3]{cardinality-ext} (only the extended version has the proof
and full typing relations for heaps and stacks in the Appendix).

The situation is a bit less dire for call-by-name and call-by-value calculi
because their heap is immutable. Furthermore, if evaluation cardinality is
unimportant, lambda-bound variables can be substituted immediately for their
arguments during $β$-reduction, hence no need for a heap whatsoever. The
stack can be reflected back into the premises of the judgment rules, so that
the system distinguishes \emph{instruction transitions} from \emph{search
transitions}, a distinction which is made explicit in a \emph{contextual
semantics}. Happily, such a contextual semantics also exists for call-by-need
\cite{Ariola:95}, although its complexity is comparatively mind-boggling.
All this reflection is with the ultimate goal of simplifying proofs: Instead
of defining an inductive well-formedness predicate on the heap, we prove a
substitution lemma. Instead of a well-formedness predicate for the stack, we
appeal to the well-formedness of the search transition rule.
\sg{Urgh, more rambling. This was an important realisation to me, although I
fear it doesn't really belong here. Perhaps it belongs in the call-by-need
subsection?}

To re-iterate: The mismatch in structure between analysis and semantics leads to
a drastic increase in proof complexity to bridge said gap. It would be desirable
to find a proof framework that allows us to re-use this bridge by means of
abstract interpretation, in the spirit of \citep{Cousot:21}.

Another way to work around the structure gap is to adopt the structure of the
semantics in the analysis; this is done in the Abstracting Abstract
Machines work \cite{aam}. To our knowledge, its exclusive application seems
to be control-flow analysis \cite{Shivers:91}, so that the analyses and
optimisations that follow do not need to reason about arbitrary function call
structure and can apply traditional intraprocedural analysis techniques that are
well-explored in the imperative world. \sg{Move this babbling to Related Work?}

\subsection{Type Analysis}

Perhaps it's best if we simply give the analysis at the end with the adequate
correctness criterion.

\subsection{Control-Flow Analysis}

Dito

\subsection{Call-by-need and Evaluation Cardinality}

While the traditional denotational semantics distinguishes call-by-name from
call-by-value by termination, it has no means to distinguish call-by-need from
call-by-name as there is no explicit notion of state or ``observable evaluation''.

Furthermore, apart from the denotational property of deadness and strictness,
which corresponds to the operational interpretation of ``never evaluated'' and
``evaluated at least once or diverging'', there is no general way to observe
properties of \emph{evaluation cardinality} such as ``evaluated at most once''
(affine) or even ``called at most once'', such as inferred by the Glasgow
Haskell Compiler \cite{cardinality}.

You might still think that the symptoms described in this subsection should
hardly affect the semantics of call-by-value languages, but the applications
of evaluation cardinality go beyond lazy languages such as Haskell.
For example, it affects linear, uniqueness and quantitative type
theory.
%, although~\citep{Atkey:18} is able to give a categorical semantics that
%postulates observability of cardinality in a suitable \emph{$R$-Quantitative Category with Families}.
%\sg{I don't really understand what Atkey does there?! If anything, our
%semantics is simpler... But this is quickly drifting towards Related Work}
Another example is recent work on re-use analysis in reference-counted language
implementations~\cite{Ullrich:19,perceus}.
\emph{Even if} we were uncaring towards infinite behaviors%
\footnote{Such as strongly-normalising type theories},
or had a denotational semantics that allowed us to observe them (but not
cardinality) as suggested in the introduction, the soundness proof for these
type systems would still need to resort to an operational semantics for the lack
of observable evaluation cardinality or postulate observability as is the case
for the categorical semantics of \citep{Atkey:18}.

\begin{figure}
\begin{minipage}{0.52\textwidth}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Usage cardinality} &       u & ∈ & \Card & =   & \{ 0 ⊏ 1 ⊏ ω \} ⊂ \mathbb{N}_ω \\
  \text{Liveness Domain}   &  d^{∃ω} & ∈ & \UsgD & =   & \Var \to \Card \\
 \end{array} \\
 \begin{array}{rcl}
   (ρ_1 + ρ_2)(\px) & = & ρ_1(\px) + ρ_2(\px) \\
   (u * ρ_1)(\px)   & = & u * ρ_1(\px) \\
 \end{array} \\
\end{array}\]
\end{minipage}%
\begin{minipage}{0.5\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semusg{\wild} \colon \Exp → (\Var → \UsgD) → \UsgD } } \\
  \\[-0.5em]
  \semusg{\px}_ρ & {}={} & ρ(\px) \\
  \semusg{\Lam{\px}{\pe}}_ρ & {}={} & ω*\semusg{\pe}_{ρ[\px ↦ \varnothing]} \\
  \\[-0.5em]
  \semusg{\pe~\px}_ρ & {}={} & \semusg{\pe} + ω*ρ(\px) \\
  \\[-0.5em]
  \semusg{\Let{\px}{\pe_1}{\pe_2}}_ρ& {}={} & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = [\px\mathord{↦}1] \mathord{+} \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semusg{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\end{minipage}%
\caption{Naïve usage analysis}
  \label{fig:liveness}
\end{figure}

\begin{theorem}[Correctness of $\semlive{\wild}$]
  \label{thm:semlive-correct-1}
  Let $\pe$ be an expression and $\px$ a variable.
  Then $\px$ is evaluated at most $u$ times whenever
  there exists $\tr ∈ \Var \to \UsgD$ such that
  $(u+1)*\tr(\px) \not⊑ \semlive{\pe}_{\tr}$.
\end{theorem}
% Curiosly, this is sound for call-by-name. Call-by-need would be a bit more complicated.
