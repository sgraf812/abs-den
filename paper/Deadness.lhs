%if style == newcode
> module Problem where
%endif

\section{Demo: Deadness Analysis, Denotationally}
\label{sec:problem}

%By way of the poster child example of a compositional definition of \emph{usage
%analysis}, we showcase how the operational detail available in traditional
%denotational semantics is too coarse to substantiate a correctness criterion,
%although the \emph{proof} of (a weaker notion of) correctness is simple and direct.
%While operational semantics observe sufficient detail to formulate a correctness
%criterion, it is quite complicated to come up with a suitable inductive
%hypothesis for the correctness proof.

Let us begin by defining the object language of this work, a lambda
calculus with \emph{recursive} let bindings and algebraic data types:
\[
\arraycolsep=3pt
\begin{array}{rrclcrrclcl}
  \text{Variables}    & \px, \py & ∈ & \Var        &     & \quad \text{Constructors} &        K & ∈ & \Con        &     & \text{with arity $α_K ∈ ℕ$} \\
  \text{Values}       &      \pv & ∈ & \Val        & ::= & \highlight{\Lam{\px}{\pe}} \mid K~\many{\px}^{α_K} \\
  \text{Expressions}  &      \pe & ∈ & \Exp        & ::= & \multicolumn{6}{l}{\highlight{\px \mid \pv \mid \pe~\px \mid \Let{\px}{\pe_1}{\pe_2}} \mid \Case{\pe}{\SelArity}}
\end{array}
\]
The form is reminiscent of \citet{Launchbury:93} and \citet{Sestoft:97} because
it is factored into \emph{A-normal form}, that is, the arguments of applications
are restricted to be variables, so the difference between call-by-name and
call-by-value manifests purely in the semantics of $\mathbf{let}$.
Note that $\Lam{x}{x}$ (with an overbar) denotes syntax, whereas $\fn{x}{x+1}$
denotes a function in math.
In this section, only the highlighted parts are relevant, but the interpreter
definition in \Cref{sec:interp} supports data types as well.
From hereon throughout, we assume that all bound program variables
are distinct.

\begin{figure}
\begin{minipage}[t]{0.48\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semscott{\wild}_{\wild} \colon \Exp → (\Var \to \ScottD) → \ScottD } } \\
  \\[-0.5em]
  \semscott{\px}_ρ & {}={} & ρ(\px) \\
  \semscott{\Lam{\px}{\pe}}_ρ & {}={} & \fn{d}{\semscott{\pe}_{ρ[\px ↦ d]}} \\
  \semscott{\pe~\px}_ρ & {}={} & \begin{cases}
     f(ρ(\px)) & \text{if $\semscott{\pe}_ρ = f$}  \\
     \bot      & \text{otherwise}  \\
   \end{cases} \\
  \semscott{\Letsmall{\px}{\pe_1}{\pe_2}}_ρ & {}={} & \semscott{\pe_2}_{ρ[\px ↦ \lfp (\fn{d}{\semscott{\pe_1}_{ρ[\px ↦ d]}})]}
  \\
  \\[-0.5em]
\end{array}\]
\caption{Denotational semantics after Scott}
  \label{fig:denotational}
\end{minipage}%
\quad
\begin{minipage}[t]{0.48\textwidth}
\arraycolsep=0pt
\[\begin{array}{c}
  \ruleform{ \dead{Γ}{\pe} }
  \\ \\[-0.5em]
  \inferrule[\textsc{Var}]{\px ∈ Γ}{\dead{Γ}{\px}}
  \quad
  \inferrule[\textsc{App}]{\dead{Γ}{\pe \quad \px ∈ Γ}}{\dead{Γ}{\pe~\px}}
  \quad
  \inferrule[\textsc{Lam}]{\dead{Γ, \px}{\pe}}{\dead{Γ}{\Lam{\px}{\pe}}}
  \\ \\[-0.5em]
  \inferrule[$\textsc{Let}_1$]{\dead{Γ, \py}{\pe_1} \quad \dead{Γ, \py}{\pe_2}}{\dead{Γ}{\Let{\py}{\pe_1}{\pe_2}}}
  \quad
  \inferrule[$\textsc{Let}_2$]{\dead{Γ}{\pe_2}}{\dead{Γ}{\Let{\py}{\pe_1}{\pe_2}}}
  \\[-0.5em]
\end{array}\]
\caption{Modular deadness analysis}
  \label{fig:deadness}
\end{minipage}
\end{figure}

We give a standard call-by-name denotational semantics $\semscott{\wild}$ in
\Cref{fig:denotational} \citep{ScottStrachey:71}, assigning meaning to our
syntax by means of the Scott domain $\ScottD$ defined as
\[
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Scott Domain}      &  d & ∈ & \ScottD & =   & [\ScottD \to_c \ScottD]_\bot, \\
 \end{array}
\]
where $[X \to_c X]_\bot$ is
the topology of Scott-continuous endofunctions on $X$ together with a distinct
least element $\bot$, and the equation is to be interpreted as the least
fixpoint of the implied functional.

\Cref{fig:deadness} defines a static \emph{deadness analysis}.
We say that $\px$ is \emph{dead} in $\pe$ when the value bound to $\px$ is
irrelevant to the value of $\pe$, that is, varying the value of $\px$ has
no effect on the value of $\pe$.
Intuitively, when $\dead{Γ}{\pe}$ is derivable and $Γ$ only contains variables
that $\px$ is known to be dead in, then $\px$ is dead in $\pe$.
For example, $\dead{\{f\}}{\Lam{y}{f~y~y}}$ is derivable and encodes
that $x$ is dead in $\Lam{y}{f~y~y}$ as long as $x$ is dead in
whatever value gets bound to $f$. \slpj{What does it mean to say that ``$x$ is dead in the value bound to $f$?  I'm struggling to understand the text.  And yet all the
analysis does is find free variables, so we are making something simple seem complicated.
And I still do not see a ``summary mechanism''.}

\slpj{It's also puzzling that although we make a big deal that analysis and
semantics are both compositional, yet we use entirely different notations to express the two; and moreover Fig 2 isn't even syntax-directed. It would be so much easier to
define an analysis function by structural recursion, just like in Fig 1, which yields the set of variables that are relevant to the value of $e$.}
$$
D[e] :: Set \; Var \\
$$

Thus, the context $Γ$ can be thought of as the set of assumptions (variables
that $\px$ is assumed dead in), and the larger $Γ$ is, the more statements are
derivable.
A decision algorithm would always pick the largest permissible $Γ$, which is
used in the \textsc{Var} and \textsc{App} cases to prove deadness of open terms.
Rules $\textsc{Let}_1$ and $\textsc{Let}_2$ handle the case where $\px$ can
be proven dead in $\pe_1$ or not, respectively; in the former case,
the let-bound variable $\py$ may be added to the context when analysing $\pe_2$.
Otherwise, evaluating $\py$ might transitively evaluate $\px$ and hence $\py$ is
not added to the context in $\textsc{Let}_2$.

Note that although the formulation of deadness analysis is so simple, it is
\emph{not} entirely naïve \slpj{in what way is it not-naive? being conservative on applications (no summary for functions) looks naive to me}:
Because it is defined by structural recursion, the \textsc{App} rule employs
a \emph{summary mechanism}, maintaining the conservative precondition that every
application deeply evaluates the argument.
For example, when $f \triangleq (\Lam{y}{\Lam{z}{z}})$, $x$ is never evaluated
when evaluating $(f~x)$, but our deadness analysis errs on the safe side and
says ``not dead'' (\eg, \emph{live}), in that $\dead{Γ}{f~x}$ is not derivable
by the \textsc{App} rule when $x$ is presumed live, $x \not∈ Γ$.
On the other hand, rule \textsc{Lam} is free to assume that any argument it
receives is dead, hence it adds the lambda-bound variable to the context.

This summary contract enables modularity:
Let us assume that the function $f$ is defined as above in a different module
than its use site $(f~x)$.
Its original definition is never looked at by the analysis when we apply it at
the use site; what matters is its easily persisted summary in the form of
the fact $f ∈ Γ$, presumably populated by a top-level equivalent of the
$\textsc{Let}_1$ rule for exported/imported bindings.
\slpj{I'm sorry I just don't get this.  If you had a summary for $f$ like ``f does not use its first argument'' I'd be with you.  But you don't.  To me the discussion of summaries is a big red herring. The point is: both semantics an analysis are compositional so we get an easy proof.}

We can formalise correctness of the summary mechanism with the following
\emph{substitution lemma}:%
\footnote{All proofs can be found in the Appendix; in case of the extended
version via clickable links.}

\begin{lemmarep}[Substitution]
\label{thm:subst-deadness}
If $\dead{Γ,\py}{(\Lam{\px}{\pe})~\py}$, then $\dead{Γ,\px}{\pe}$.
\end{lemmarep}
\begin{proof}
The assumption has a sub-derivation for $\dead{Γ,\px}{\pe}$ in the premise of
\textsc{Lam}, showing the goal.
\end{proof}

A similar lemma can be derived for $\mathbf{let}$.
The substitution lemma is often instrumental in correctness proofs, although in
this case it is so simple (the proof is right in the premise of
\textsc{Lam}) that it can be inlined when proving deadness analysis correct in
terms of semantic irrelevance below:

\begin{theoremrep}[Correct deadness analysis]
  \label{thm:deadness-correct}
  If $\dead{Γ}{\pe}$ and $\px \not∈ Γ$,
  then $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
\end{theoremrep}
\begin{proof}
  By induction on $\pe$.
  \begin{itemize}
    \item \textbf{Case $\pe = \py$}: If $\px=\py$, then by rule \textsc{Var} we
      have $\px ∈ Γ$, a contradiction.
      If $\px \not= \py$, then $ρ[\px↦d_1](\py) = ρ(\py) = ρ[\px↦d_2](\py)$.

    \item \textbf{Case $\pe = \Lam{\py}{\pe'}$}: The equality follows from
      pointwise equality on functions, so we pick an arbitrary $d$ to show
      $\semscott{\pe'}_{ρ[\px↦d_1][\py↦d]} = \semscott{\pe'}_{ρ[\px↦d_2][\py↦d]}$.

      By rule \textsc{Lam}, we have $\dead{Γ,\py}{\pe'}$, and since
      $\px \not∈ Γ$ we may apply the induction hypothesis to get
      $\semscott{\pe'}_{ρ[\py↦d][\px↦d_1]} = \semscott{\pe'}_{ρ[\py↦d][\px↦d_2]}$,
      and commuting the extension of $ρ$ shows the goal.

    \item \textbf{Case $\pe = \pe'~\py$}:
      By rule \textsc{App}, we have $\dead{Γ}{\pe'}$ and $\py ∈ Γ$.
      We apply the induction hypothesis to get
      $\semscott{\pe'}_{ρ[\px↦d_1]} = \semscott{\pe'}_{ρ[\px↦d_2]}$, which
      either is $\bot$ or some function $f$.

      In the former case, both applications evaluate to $\bot$.
      In the latter case, we have to prove that $f(ρ[\px↦d_1](\py)) =
      f(ρ[\px↦d_2](\py))$, but that is easy to see as well,
      because $\px \not∈ Γ$ while $\py ∈ Γ$ implies that $\px \not= \py$.

    \item \textbf{Case $\pe = \Let{\py}{\pe_1}{\pe_2}$}:
      We have to show that
      \[
        \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
      \]
      where $d'_i$ satisfy $d'_i = \semscott{\pe_1}_{ρ[\px↦d_i][\py↦d'_i]}$.
      The case $\px = \py$ is simple to see, because $ρ[\px↦d_i](\px)$ is never
      looked at.

      We proceed by rule inversion on $\dead{Γ}{\Let{\py}{\pe_1}{\pe_2}}$:
      \begin{itemize}
        \item \textbf{Case $\textsc{Let}_1$}: Then $\dead{Γ,\py}{\pe_1}$ and by
          the induction hypothesis and commuting extensions of $ρ$ we have
          $d'_1 = d'_2$.
          We apply the induction hypothesis once more to $\dead{Γ,\py}{\pe_2}$
          and commute the extensions once more to show the goal.
        \item \textbf{Case $\textsc{Let}_2$}: Then $\dead{Γ}{\pe_2}$ and both
          $\px$ and $\py$ are dead in $\pe_2$; hence we may apply the induction
          hypothesis to rewrite the extensions $[\px↦d_i]$, $[\py↦d'_i]$
          independently and however we want to show the goal:
          \[
            \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_2]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
          \]
      \end{itemize}
  \end{itemize}
\end{proof}


The semantics $\semscott{\wild}$ and analysis $\dead{\wild}{\wild}$ are
both defined by \emph{structural recursion} over the expression. In other words, they
are both \emph{compositional} in the sense that the meaning of an expression
is obtained by combining the meanings of its sub-expressions.
Moreover, because the semantics and the analysis are so similar in structure,
it is easy to prove the analysis sound by induction on the program expression.
The proof is simple and direct, at barely over half a page in length.
Indeed, leaning on
the deep notion of equality in $\ScottD$,%
\footnote{Thus we stay blissfully unaware of the lack of full
abstraction~\citep{Plotkin:77}.}
we don't even need to strengthen the induction hypothesis for the application
case.

Alas, there are several reasons why this framework is not so useful in practice:
\slpj{I took "this framework" to mean the compositional semantics + analysis.  But then the third bullet is about oprerational semantics -- very confusing.}
\begin{itemize}
% Simon convinced me of his unconvincedness:
%  \item
%    Denotational semantics are fundamentally restricted in the way they
%    \textbf{\emph{represent diverging computations}}, in that any such computation must
%    be denoted by $\bot$.
%    Thus, a denotational semantics cannot be used to prove that an analysis
%    yields safe results on diverging programs.
  \item
    \Cref{thm:deadness-correct} yields credible proof that the implied
    transformation is safe, but none whatsoever on whether it is
    \textbf{\emph{contextually improving}}~\citep{MoranSands:99}.
    Proof for the latter would need to expose more operational detail in the
    semantics, such as in \citet{HackettHutton:19}.
    For more complex analyses, it would be good to separate the semantic
    property from the transformation it enables, such that improvement can be
    shown separately.
  \item
    Suppose we were to extend our deadness analysis to infer more detailed
    upper bounds on \emph{evaluation cardinality}, \eg, how \emph{often} some variable
    is evaluated.
    Unfortunately, a denotational semantics does not allow us to
    \textbf{\emph{express the operational property}} ``$\pe$ evaluates $\px$ at
    most $u$ times''%
    \footnote{A more useful application of the ``at most once'' cardinality is the
    identification of \emph{one-shot} lambdas~\citep{cardinality-ext} --- functions which are
    called at most once for every activation --- because it allows floating of heap
    allocations from a hot code path into cold function bodies.},
    so we cannot prove that this so-called \emph{usage analysis} can be used for
    update avoidance~\citep{Gustavsson:98}.
  \item
    While (small-step) operational semantics can be used to prove aforementioned
    cardinality properties, the \textbf{\emph{mismatch in recursion structure}}
    necessitates (1) extension of the analysis to whole machine configurations,
    (2) complex refinements of the correctness statement to strengthen the
    induction hypothesis, and possibly (3) fixpoint induction when the original
    analysis definition is used without prior generalisation into a declarative system.

    While recent years have made progress in grasping these proofs in terms of
    (step-indexed) logical relations and Galois connections, we found it quite
    hard to come up with an ad-hoc correctness predicate for the implied usage
    analysis.
  \item
    Abstracting a small-step or big-step interpreter~\citep{aam,adi} bridges the
    structural mismatch alright, but does so at the cost of
    \textbf{\emph{modularity}} and discards a perfectly good summary mechanism.
    It is the modern-time equivalent of the classic functional \vs call string
    approach to interprocedural analysis~\citep{SharirPnueli:78}; summaries are
    symbolic approximations of the ``functional'' that is a function's abstract
    transformer.
\end{itemize}

Our work improves on all the issues highlighted above.

\begin{comment}
\subsection{Approximation Order and Safety Properties}
\label{sec:continuity}

Our correctness proof has a blind spot \wrt diverging computations:
$\semscott{\wild}$ denotes any looping program such as
$\pe_{\mathit{loop}} \triangleq
\Let{\mathit{loop}}{\Lam{x}{\mathit{loop}~x}}{{\mathit{loop}~\mathit{loop}}}$
by $\bot$, the same element that is meant to indicate partiality in the
approximation order of the domain (\eg, insufficiently specified input).
Hence our analysis is free to respond ``all dead'' for any looping program, even
though the free variables' values have an effect on which endless loop is taken.

Fortunately, type analysis, deadness analysis and control-flow
analysis~\citep{Shivers:91} infer so called \emph{safety
properties}~\citep{Lamport:77}.
When a diverging execution violates a safety property (\eg, ``goes wrong'',
evaluates a variable or reaches a control-flow node), one of its finite prefixes
will also violate it.
It is however impossible to formulate a non-trivial property of infinite
executions \wrt a denotational semantics, because all infinite executions are
denoted by $\bot$, which is a fundamental artifact of the approximation order
in Scott domains.
\citet[p. 23]{Shivers:91} remedies this limitation by introducing a
\emph{non-standard semantic interpretation} that assigns diverse meaning to
diverging programs.
While this is a reasonable step, credibility of it rests solely on the
structural similarity to the standard denotational semantics.

According to \citet[Section 2.3]{WrightFelleisen:94}, the approximation order
used in denotational semantics and the resulting recurring need to solve domain
equations and prove continuity -- tedious manual processes -- contributed great
arguments in favor of operational semantics.

\subsection{Operational Detail}

Blind spots and annoyances notwithstanding, the denotational notion of deadness
above is quite reasonable and \Cref{thm:deadness-correct} is convincing.
However, it does not tell us much about whether exploiting deadness leads to
faster programs!
One would need an argument based on contextual improvement~\citep{MoranSands:99}
to do so; necessitating a proof based on an operational semantics.

Moreover, suppose we were to extend our deadness analysis to infer more detailed
bounds on \emph{evaluation cardinality}, \eg, how often some variable is
evaluated.
A context $Γ$ then is a finite map, assigning each variable an upper bound
$u ∈ \{0,1,ω\}$ of its evaluation cardinality, which we call \emph{usage
cardinality}.
The assertion $Γ(\px) = 0$ is equivalent to $\px ∈ Γ$ in \Cref{fig:deadness}.
The resulting system $\usg{Γ}{\pe}$, dubbed \emph{usage analysis}, is
not unlike a substructural type system and can be used to infer whether a
binding $\px$ is used at most once, in which case $Γ(\px) \leq 1$.%
\footnote{Thus our usage analysis is a combination of deadness analysis
and \emph{sharing analysis}~\citep{Gustavsson:98}.}
This information can be useful to inline a binding that is not a value or
to avoid update frames under call-by-need~\citep{Gustavsson:98,cardinality-ext}.%
\footnote{A more useful application of the ``at most once'' cardinality is the
identification of \emph{one-shot} lambdas~\citep{cardinality-ext} --- functions which are
called at most once for every activation --- because it allows floating of heap
allocations from a hot code path into cold function bodies.}

We will see in \Cref{sec:usage-analysis} how to formally define usage analysis.
Unfortunately, a denotational semantics does not allow us to express the
operational property ``$\pe$ evaluates $\px$ at most $u$ times'', so
we cannot prove that usage analysis can be used for update avoidance.

\subsection{Structural Mismatch}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl@@{\hspace{1.5em}}rrcrclcl}
  \text{Addresses}     & \pa & ∈ & \Addresses     & \simeq & ℕ
  &
  \text{States}        & σ   & ∈ & \States        & =      & \Exp \times \Environments \times \Heaps \times \Continuations
  \\
  \text{Environments}  & ρ   & ∈ & \Environments  & =      & \Var \pfun \Addresses
  &
  \text{Heaps}         & μ   & ∈ & \Heaps         & =      & \Addresses \pfun \Environments \times \Exp
  \\
  \text{Continuations} & κ   & ∈ & \Continuations & ::=    & \multicolumn{7}{l}{\StopF \mid \ApplyF(\pa) \pushF κ \mid \SelF(ρ,\SelArity) \pushF κ \mid \UpdateF(\pa) \pushF κ} \\
 \end{array} \\
 \\[-0.5em]
\end{array}\]

\newcolumntype{L}{>{$}l<{$}} % math-mode version of "l" column type
\newcolumntype{R}{>{$}r<{$}} % math-mode version of "r" column type
\newcolumntype{C}{>{$}c<{$}} % math-mode version of "c" column type
\resizebox{\textwidth}{!}{%
\begin{tabular}{LR@@{\hspace{0.4em}}C@@{\hspace{0.4em}}LL}
\toprule
\text{Rule} & σ_1 & \smallstep & σ_2 & \text{where} \\
\midrule
\LetIT & (\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) & \smallstep & (\pe_2,ρ',μ[\pa↦(ρ',\pe_1)], κ) & \pa \not∈ \dom(μ),\ ρ'\! = ρ[\px↦\pa] \\
\AppIT & (\pe~\px,ρ,μ,κ) & \smallstep & (\pe,ρ,μ,\ApplyF(\pa) \pushF κ) & \pa = ρ(\px) \\
\CaseIT & (\Case{\pe_s}{\Sel[r]},ρ,μ,κ) & \smallstep & (\pe_s,ρ,μ,\SelF(ρ,\Sel[r]) \pushF κ) & \\
\LookupT & (\px, ρ, μ, κ) & \smallstep & (\pe, ρ', μ, \UpdateF(\pa) \pushF κ) & \pa = ρ(\px),\ (ρ',\pe) = μ(\pa) \\
\AppET & (\Lam{\px}{\pe},ρ,μ, \ApplyF(\pa) \pushF κ) & \smallstep & (\pe,ρ[\px ↦ \pa],μ,κ) &  \\
\CaseET & (K'~\many{y},ρ,μ, \SelF(ρ',\Sel) \pushF κ) & \smallstep & (\pe_i,ρ'[\many{\px_i ↦ \pa}],μ,κ) & K_i = K',\ \many{\pa = ρ(\py)} \\
\UpdateT & (\pv, ρ, μ, \UpdateF(\pa) \pushF κ) & \smallstep & (\pv, ρ, μ[\pa ↦ (ρ,\pv)], κ) & \\
\bottomrule
\end{tabular}
} % resizebox
\caption{Lazy Krivine transition semantics $\smallstep$}
  \label{fig:lk-semantics}
\end{figure}

Let us try a different approach then and define a stronger notion of deadness
in terms of a small-step operational semantics such as the Mark II machine of
\citet{Sestoft:97} given in \Cref{fig:lk-semantics}, the semantic ground truth
for this work. (A close sibling for call-by-value would be a CESK machine
\citep{Felleisen:87} or a simpler derivative thereof.)
It is a Lazy Krivine (LK) machine implementing call-by-need, so for a meaningful
comparison to the call-by-name semantics $\semscott{\wild}$, we ignore rules
$\CaseIT, \CaseET, \UpdateT$ and the pushing of update frames in $\LookupT$ for
now to recover a call-by-name Krivine machine with explicit heap.

\sg{I would \emph{love} to say less here on boring explanations of the machine.
Perhaps move closer to the proofs where the detail becomes relevant}
The configurations $σ$ in this transition system resemble abstract machine
states, consisting of a control expression $\pe$, an environment $ρ$ mapping
lexically-scoped variables to their current heap address, a heap $μ$ listing a
closure for each address, and a stack of continuation frames $κ$.

The notation $f ∈ A \pfun B$ used in the definition of $ρ$ and $μ$ denotes a
finite map from $A$ to $B$, a partial function where the domain $\dom(f)$ is
finite and $\rng(f)$ denotes its range.
The literal notation $[a_1↦b_1,...,a_n↦b_n]$ denotes a finite map with domain
$\{a_1,...,a_n\}$ that maps $a_i$ to $b_i$. Function update $f[a ↦ b]$
maps $a$ to $b$ and is otherwise equal to $f$.

The initial machine state for a closed expression $\pe$ is given by the
injection function $\inj(\pe) = (\pe,[],[],\StopF)$ and
the final machine states are of the form $(\pv,\wild,\wild,\StopF)$.
We bake into $σ∈\States$ the simplifying invariant of \emph{well-addressedness}:
Any address $\pa$ occuring in $ρ$, $κ$ or the range of $μ$ must be an element of
$\dom(μ)$.
It is easy to see that the transition system maintains this invariant and that
it is still possible to observe scoping errors which are thus confined to lookup
in $ρ$.

This machine allows us to observe variable lookups as $\LookupT$ transitions,
which enables a semantic characterisation of usage cardinality:

\begin{definition}[Usage cardinality]
  \label{defn:usage}
  An expression $\pe$ \emph{evaluates} $\px$ \emph{at most $u$ times}
  if and only if for any evaluation context $(ρ,μ,κ)$ and expression $\pe'$,
  there are at most $u$ configurations $σ$ in the trace
  $(\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],\wild,\wild) \smallstep^* σ$ such
  that $σ=(\py,ρ',\wild,\wild)$ and $ρ'(\py) = \pa$.
\end{definition}

In other words, the usage cardinality of a variable $\px$ is an upper bound to
the number of $\LookupT$ transitions that alias to the heap entry of $\px$,
assuming we start in a state where $\px$ is alias-free.

We can use this definition for a correctness statement of the (so far
hypothetical) usage analysis:
\begin{theorem}[Correct usage analysis]
  \label{thm:usg-correct}
  If $\usg{Γ}{\pe}$, then $\pe$ evaluates $\px$ at most $Γ(\px)$ times.
\end{theorem}
For the proof, one would expect to be able to conclude that
$\Let{y}{\pe_1}{\pe_2}$ never evaluates $x$ if $\pe_1$ and $\pe_2$ never
evaluate $x$, but unfortunately that is not the case:
\[
  (\Let{x}{\pe'}{\Let{y}{\pe_1}{\pe_2}},ρ,μ,κ) \smallstep^2
  (\pe',ρ[x↦\pa_1,y↦\pa_2],μ[\pa_1↦(\wild,\pe'),\pa_2↦(\wild, \pe_1)],κ)
\]
Note that although $x$ is dead in $\pe_1$, it might still \emph{occur} in
$\pe_1$ (in a dead argument, for example), so it is impossible to derive this
state by starting from $\Let{x}{\pe'}{\pe_2}$.
Consequently, we can make no statement about the usage cardinality of
$\Let{y}{\pe_1}{\pe_2}$ and it is impossible to prove that $\semusg{\pe}$
satisfies \Cref{thm:usg-correct} by direct structural induction on $\pe$
(in a way that would be useful to the proof).

Instead, such proofs are often conducted by induction over the reflexive
transitive closure of the transition relation.
For that it is necessary to give an inductive hypothesis that considers
environments, stacks and heaps.
One way is to extend the analysis $\usg{Γ}{\pe}$ to entire
configurations and then prove preservation lemmas about $⊦ σ$.
This is a daunting task, for multiple reasons:
First off, $\usg{\wild}{\wild}$ might be quite complicated in practice and
extending it to entire configurations multiplies this complexity.
Secondly, realistic analyses make use of fixpoints in the let case, so
preservation needs to resort to fixpoint induction over a huge functional.

In call-by-need, there will be a fixpoint between the heap and stack due to
update frames acting like heap bindings whose right-hand side is under
evaluation (a point that is very apparent in the semantics of
\citet{Ariola:95}), so fixpoint induction needs to be applied \emph{at every
case of the proof}, diminishing confidence in correctness unless the proof is
fully mechanised.

Instead of referencing the algorithmic inference algorithm in our proof,
we could instead come up with (yet another) declarative system that is more
permissive.
Preservation then corresponds to the proof that the declarative predicate is
\emph{logical} \wrt $\smallstep$.
Examples of this approach are the
``well-annotatedness'' relation in \citep[Lemma 4.3]{cardinality-ext} or
$\sim_V$ in \citep[Theorem 2.21]{Nielson:99}), and the Galois connections we
give in \Cref{sec:adequacy,sec:soundness}.
We found it quite hard to come up with a suitable ad-hoc correctness relation
for usage cardinality, though.
\end{comment}

\begin{comment}
\subsection{Abstract Interpretation}

Where does \emph{Abstract Interpretation}~\citep{Cousot:21} fit into this?
Note first that the property ``$\pe$ evaluates $\px$ at most $u$ times'' can be
interpreted as a property of all the (potentially infinite) traces $τ$ generated by
$(\Let{\px}{\pe'}{\pe},ρ,μ,κ)$ for some $\pe',ρ,μ,κ$.
For a fixed $u$, this trace property is a safety property:
If $τ$ evaluates $\px$ more than $u$ times, then some finite prefix of $τ$ will
also evaluate $\px$ more than $u$ times.
Thus we can formulate usage cardinality of a trace as a mathematical function:
\[\begin{array}{lcl}
  \usg    & \colon & \mathbb{T} \to \UsgD \\
  \usg(τ) & =      & \begin{cases}
    [ \px ↦ 1 \mid ρ(\py) = ρ(\px) ] + \usg(τ') & τ = (\py,ρ,\wild,\wild) \smallstep τ' \\
    \usg(τ') & τ = σ \smallstep τ' \\
    \bot & τ = σ, σ \not\smallstep \\
    \Lub_{τ^* ∈ \mathit{pref}(τ)} \usg(τ^*) & \text{otherwise},
  \end{cases}
\end{array}\]
(where $\mathit{pref}(τ)$ enumerates the finite prefixes of $τ$.)
Furthermore, we can lift $\usg$ to sets of traces via
\emph{join homomorphic abstraction}~\citep[Exercise 11.8]{Cousot:21}
$α_{\usg}(T) \triangleq \Lub_{τ∈T} \{ \usg(τ) \mid τ ∈ T \}$,
yielding for free a Galois connection between inclusion on sets of traces and
$(\Usg,⊑)$.%
\footnote{\citeauthor{Nielson:99} calls $\usg$ a \emph{representation function}
and derive a Galois connection in the same way.}
Writing $\semsmall{σ}$ to denote the maximal small step trace starting from
$σ$, we can re-state \Cref{thm:semusg-correct-2} as
\[
  ∀\pe,ρ,μ,κ,\px,\pe'.\ α_{\usg}(\{\semsmall{(\Let{\px}{\pe'}{\pe},ρ,μ,κ)}\})(\px) ⊑ \semusg{\pe}_{\tr_Δ}(\px).
\]
The art of abstract interpretation is to massage this statement into a
form that it applies at the recursive invokations of $\semusg{\wild}$ (by
discarding the first transition, among other things) and relating the
environment parameter $\tr_Δ$ to $(ρ,μ)$ via $α_{\usg}$.
This process constructs a correctness relation in ``type-driven'' way, by
(in-)equational reasoning.

Alas, due to the structural mismatch between semantics and analysis, the
``massaging'' becomes much harder.
This is why related literature such as
\emph{Abstracting Abstract Machines}~\citep{aam} and
\emph{Abstracting Definitional Interpreters}~\citep{adi}
force the analysis structure to follow the semantics.

On the other hand, \citet{Cousot:21} gives a structurally recursive semantics
function, generating potentially infinite traces (understood topologically) for
an imperative, first-order language.
Consequently, all derived analyses are structurally-recursive in turn.%
\footnote{Computation of fixpoints can still happen on a control-flow graph, of
course, employing efficient worklist algorithms.}

This inspired us to find a similar semantics for a higher-order language.
By coincidence, this semantics has the form of definitional interpreter,
and can be abstracted enough to qualify as an abstract definitional interpreter.
In contrast to the work on abstract small-step and big-step
machines, this interpreter is \emph{total}, just like Cousot's semantics, and
hence qualifies as a denotational semantics that we can harness to prove
statements such as \Cref{thm:never-dead}.

% TODO: Forward reference to where we bring our semantics to bear

% An alternative to avoid structural mismatch is to follow Abstracting Abstract
% Machines~\citep{aam}.
% We will compare our approach to theirs in \Cref{sec:related-work}.

%\subsection{Abstracting Abstract Machines}
%
%Another way to work around the structural mismatch is to adopt the structure of
%the semantics in the analysis; this is done in the Abstracting Abstract Machines
%work \citep{aam}.
%The appeal is to piggy-back traditional and well-explored intraprocedural
%analysis techniques on the result of an interprocedural flow
%analysis~\citep{Shivers:91}.

\end{comment}

\begin{comment}
\Cref{fig:usage} defines a static \emph{usage analysis}.
The idea is that $\semusg{\pe}_{ρ}$ is a function $d ∈ \UsgD$ whose domain
is the free variables of $\pe$; this function maps each free variable $\px$ of
$\pe$ to its \emph{usage cardinality} $u ∈ \Usg$, an upper bound on the
number of times that $\px$ will be evaluated when $\pe$ is evaluated (regardless
of context).
Thus, $\Usg$ is equipped with a total order that corresponds to the inclusion
relation of the denoted interval of cardinalities:
$\bot = 0 ⊏ 1 ⊏ ω = \top$, where $ω$ denotes \emph{any} number of evaluations.
This order extends pointwise to a partial ordering on $\UsgD$, so $d_1 ⊑
d_2$ whenever $d_1(\px) ⊑ d_2(\px)$, for all $\px$ and $\bot_{\UsgD} =
\constfn{\bot_\Usg}$.
We will often leave off the subscript of, \eg, $\bot_\UsgD$ when it can be
inferred from context.

So, for example $\semusg{x+1}_{ρ}$ is a function mapping $x$ to 1
and all other variables to 0 (for a suitable $ρ$ that we discuss in due course).
Any number of uses beyond $1$, such as $2$ for $x$ in $\semusg{x+x}_{ρ}$, are
collapsed to $d(x) = ω$.
Similarly $\semusg{\Lam{v}{v+z}}_{\rho}$
maps $z$ to $\omega$, since the lambda might be called many times.

For open expressions, we need a way to describe the denotations of its
free variables with a \emph{usage environment}\footnote{
Note that we will occassionally adorn with \textasciitilde{} to disambiguate
elements of the analysis domain from the semantic domain.}
$\tr ∈ \Var \to \UsgD$.
Given a usage environment $\tr$, $\tr(\px)(\py)$ models an upper bound
on how often the expression bound to $\px$ evaluates $\py$.

\begin{figure}
\begin{minipage}{\textwidth}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Scott Domain}      &  d & ∈ & \ScottD & =   & [\ScottD \to_c \ScottD]_\bot \\
  \text{Usage cardinality} &  u & ∈ & \Usg & =   & \{ 0, 1, ω \} \\
  \text{Usage Domain}      &  d & ∈ & \UsgD & =   & \Var \to \Usg \\
 \end{array} \quad
 \begin{array}{rcl}
   (ρ_1 ⊔ ρ_2)(\px) & = & ρ_1(\px) ⊔ ρ_2(\px) \\
   (ρ_1 + ρ_2)(\px) & = & ρ_1(\px) + ρ_2(\px) \\
   (u * ρ_1)(\px)   & = & u * ρ_1(\px) \\
 \end{array}
 \\[-0.5em]
\end{array}\]
\subcaption{Syntax of semantic domains}
  \label{fig:dom-syntax}
\newcommand{\scalefactordenot}{0.92}
\scalebox{\scalefactordenot}{%
\begin{minipage}{0.49\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semscott{\wild}_{\wild} \colon \Exp → (\Var \to \ScottD) → \ScottD } } \\
  \\[-0.5em]
  \semscott{\px}_ρ & {}={} & ρ(\px) \\
  \semscott{\Lam{\px}{\pe}}_ρ & {}={} & \fn{d}{\semscott{\pe}_{ρ[\px ↦ d]}} \\
  \semscott{\pe~\px}_ρ & {}={} & \begin{cases}
     f(ρ(\px)) & \text{if $\semscott{\pe}_ρ = f$}  \\
     \bot      & \text{otherwise}  \\
   \end{cases} \\
  \semscott{\Letsmall{\px}{\pe_1}{\pe_2}}_ρ & {}={} &
    \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semscott{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\subcaption{\relscale{\fpeval{1/\scalefactordenot}} Denotational semantics after Scott}
  \label{fig:denotational}
\end{minipage}%
\quad
\begin{minipage}{0.56\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semusg{\wild}_{\wild} \colon \Exp → (\Var → \UsgD) → \UsgD } } \\
  \\[-0.5em]
  \semusg{\px}_ρ & {}={} & ρ(\px) \\
  \semusg{\Lam{\px}{\pe}}_ρ & {}={} & ω*\semusg{\pe}_{ρ[\px ↦ \bot]} \\
  \semusg{\pe~\px}_ρ & {}={} & \semusg{\pe}_ρ + ω*ρ(\px)
    \phantom{\begin{cases}
       f(ρ(\px)) & \text{if $\semusg{\pe}_ρ = f$}  \\
       \bot      & \text{otherwise}  \\
     \end{cases}} \\
  \semusg{\Letsmall{\px}{\pe_1}{\pe_2}}_ρ& {}={} & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = [\px\mathord{↦}1] \mathord{+} \semusg{\pe_1}_{ρ'} \\
      \text{in}         & \semusg{\pe_2}_{ρ'}
    \end{letarray}
\end{array}\]
\subcaption{\relscale{\fpeval{1/\scalefactordenot}} Naïve usage analysis}
  \label{fig:usage}
\end{minipage}
}
\end{minipage}
  \label{fig:intro}
\vspace{-0.75em}
\caption{Connecting usage analysis to denotational semantics}
\end{figure}

\subsection{Usage Analysis Infers Denotational Deadness}

The requirement (in the sense of informal specification) on an assertion
such as ``$x$ is dead'' in a program like $\Let{x}{\pe_1}{\pe_2}$ is that we
may rewrite to $\Let{x}{\mathit{panic}}{\pe_2}$ and even to $\pe_2$ without
observing any change in semantics. Doing so reduces code size and heap
allocation.

This can be made formal in the following definition of deadness in terms of
$\semscott{\wild}$:

\begin{definition}[Deadness]
  \label{defn:deadness}
  A variable $\px$ is \emph{dead} in an expression $\pe$ if and only
  if, for all $ρ ∈ \Var \to \ScottD$ and $d_1, d_2 ∈ \ScottD$, we have
  $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
  Otherwise, $\px$ is \emph{live}.
\end{definition}

Indeed, if we know that $x$ is dead in $\pe_2$, then the following equation
justifies our rewrite above: $\semscott{\Let{x}{\pe_1}{\pe_2}}_ρ =
\semscott{\pe_2}_{ρ[x↦d]} = \semscott{\pe_2}_{ρ[x↦ρ(x)]} =\semscott{\pe_2}_ρ$
(for all $ρ$ and the suitable $d$),
where we make use of deadness in the second $=$.
So our definition of deadness is not only simple to grasp, but also simple to
exploit.

We can now prove our usage analysis correct as a deadness analysis in
terms of this notion: \\

\begin{theoremrep}[$\semusg{\wild}$ is a correct deadness analysis]
  \label{thm:semusg-correct-live}
  Let $\pe$ be an expression and $\px$ a variable.
  If $\semusg{\pe}_{\tr_Δ}(\px) = 0$
  then $\px$ is dead in $\pe$.
\end{theoremrep}
\begin{proof}
  By induction on $\pe$, generalising $\tr_Δ$ in the assumption
  $\semusg{\pe}_{\tr_Δ}(\px) = 0$ to ``there exists a $\tr$
  such that $\tr(\px) \not⊑ \semusg{\pe}_{\tr}$''.
 \slpj{That is indeed a tricky statement.  What is the intuition?  Do you mean
    that this has to be true for \emph{every} $\tr$?  Or that $\px$ is dead if I can find \emph{some} $\tr$ for which
    the statement holds? It is surely not true in general because $\px$ might have bindings for variables nothing to do with $e$.}
 \sg{The ``some'' version is the correct notion. The $\tr$ becomes a witness of
     deadness. I don't understand your comment \wrt not being true in general. }

  It is $\tr_Δ(\px) \not⊑ \semusg{\pe}_{\tr_Δ}$:
  Let us assume $\semusg{\pe}_{\tr_Δ}(\px) = 0$.
  We know, by definition of $\tr_Δ$ that ${\tr_Δ(\px)(\px) = 1}$.
  Hence $\tr_Δ(\px)(\px) \not⊑ \semusg{\pe}_{\tr_Δ}(\px)$; and hence $\tr_Δ(\px) \not⊑ \semusg{\pe}_{\tr_Δ}$.
  \sg{I suppose we can be a little more explicit here, as you suggested.
  Ultimately I don't think that hand-written proofs will carry us very far
  and I'll try formalise the more important proofs in Agda.}

  We fix $\pe$, $\px$ and $\tr$ such that $\tr(\px) \not⊑ \semusg{\pe}_{\tr}$.
  The goal is to show that $\px$ is dead in $\pe$,
  so we are given an arbitrary $ρ$, $d_1$ and $d_2$ and have to show that
  $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
  By cases on $\pe$:
  \begin{itemize}
    \item \textbf{Case $\pe = \py$}: If $\px=\py$, then
      $\tr(\px) \not⊑ \semusg{\py}_{\tr} = \tr(\py) = \tr(\px)$, a contradiction.
      If $\px \not= \py$, then varying the entry for $\px$ won't matter; hence
      $\px$ is dead in $\py$.
    \item \textbf{Case $\pe = \Lam{\py}{\pe'}$}: The equality follows from
      pointwise equality on functions, so we pick an arbitrary $d$ to show
      $\semscott{\pe'}_{ρ[\px↦d_1][\py↦d]} = \semscott{\pe'}_{ρ[\px↦d_2][\py↦d]}$.

      This is simple to see if $\px=\py$. Otherwise, $\tr[\py↦\bot]$ witnesses the fact that
      \[
        \tr[\py↦\bot](\px) = \tr(\px) \not⊑
        \semusg{\Lam{\py}{\pe'}}_{\tr} = \semusg{\pe'}_{\tr[\py↦\bot]}
      \]
      so we can apply the induction hypothesis to see that $\px$ must be dead in
      $\pe'$, hence the equality on $\semscott{\pe'}$ holds.
    \item \textbf{Case $\pe = \pe'~\py$}:
      From $\tr(\px) \not⊑ \semusg{\pe'}_{\tr} + ω*\tr(\py)$ we can see that
      $\tr(\px) \not⊑ \semusg{\pe'}_{\tr}$ and $\tr(\px) \not⊑ \tr(\py)$ by
      monotonicity of $+$ and $*$.
      If $\px=\py$ then the latter inequality leads to a contradiction.
      Otherwise, $\px$ must be dead in $\pe'$, hence both cases of
      $\semscott{\pe'~\py}$ evaluate equally, differing only in
      the environment. It remains to be shown that
      $ρ[\px↦d_1](\py) = ρ[\px↦d_2](\py)$, and that is easy to see since
      $\px \not= \py$.
    \item \textbf{Case $\pe = \Let{\py}{\pe_1}{\pe_2}$}:
      We have to show that
      \[
        \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
      \]
      where $d'_i$ satisfy $d'_i = \semscott{\pe_1}_{ρ[\px↦d_i][\py↦d'_i]}$.
      The case $\px = \py$ is simple to see, because $ρ[\px↦d_i](\px)$ is never
      looked at.
      So we assume $\px \not= \py$ and see that $\tr(\px) = \tr'(\px)$, where
      $\tr' = \operatorname{fix}(\fn{\tr'}{\tr ⊔ [\py ↦ [\py↦1]+\semusg{\pe_1}_{\tr'}]})$.

      We know that
      \[
        \tr'(\px) = \tr(\px) \not⊑ \semusg{\pe}_{\tr} = \semusg{\pe_2}_{\tr'}
      \]
      So by the induction hypothesis, $\px$ is dead in $\pe_2$.

      We proceed by cases over $\tr(\px) = \tr'(\px) ⊑ \semusg{\pe_1}_{\tr'}$.
      \begin{itemize}
        \item \textbf{Case $\tr'(\px) ⊑ \semusg{\pe_1}_{\tr'}$}: Then
          $\tr'(\px) ⊑ \tr'(\py)$ and $\py$ is also dead in $\pe_2$ by the above
          inequality.
          Both deadness facts together allow us to rewrite
          \[
            \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_2]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
          \]
          as requested.
        \item \textbf{Case $\tr'(\px) \not⊑ \semusg{\pe_1}_{\tr'}$}:
          Then $\px$ is dead in $\pe_1$ and $d'_1 = d'_2$. The goal follows
          from the fact that $\px$ is dead in $\pe_2$.
      \end{itemize}
  \end{itemize}
\end{proof}

Simplicity of proofs is a good property to strive for, so let us formulate an
explicit goal:

\formgoal{1}{Give a semantics that makes correctness proofs similarly simple.}

This is a rather vague goal and should be seen as the overarching principle of
this work.
In support of this principle, we will formulate a few more concrete goals that
each require more context to make sense.


\end{comment}

