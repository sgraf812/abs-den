%if style == newcode
> module Problem where
%endif

\section{The Problem We Solve}
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

\subsection{Deadness Analysis}
\label{sec:deadness}

\begin{figure}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semdead{\wild}_{\wild} \colon \Exp → (\Var → \pow{\Var} \times S) → \pow{\Var} \times S } } \\
  \\[-0.5em]
  S & {}::={} & \bullet \\
  \\[-0.5em]
  \semdead{\px}_\tr & {}={} & \tr(\px) \\
  \semdead{\Lam{\px}{\pe}}_\tr & {}={} & \mathit{summarise}(\fn{V}{\semdead{\pe}_{\tr[\px ↦ V]}}) \\
  \semdead{\pe~\px}_\tr & {}={} & \mathit{apply}(\semdead{\pe}_{\tr}, \tr(\px)) \\
  \semdead{\Letsmall{\px}{\pe_1}{\pe_2}}_\tr & {}={} & \semdead{\pe_2}_{\tr[\px ↦ \{\px\} ∪_1 \semdead{\pe_1}_{\tr[\px ↦ (\varnothing,\bullet)]}]} \\
  V_1 ∪_1 (V_2,\bullet) & = & (V_1 ∪ V_2, \bullet) \\
  \mathit{summarise}(f) & = & f((\varnothing, \bullet)) \\
  \mathit{apply}((V_f,\bullet), (V_a,\bullet)) & = & (V_f ∪ V_a, \bullet)
  \\[-0.5em]
\end{array}\]
\caption{Compositional deadness analysis}
  \label{fig:deadness}
\end{figure}

\Cref{fig:deadness} defines a static \emph{deadness analysis} for call-by-name
and call-by-need programs.
We informally say that $\px$ is \emph{dead} in $\pe$ when $\px$ is never
evaluated during by-name and by-need evaluation of $\pe$, no matter how deep we
evaluate.
Otherwise, $\px$ is \emph{needed} in $\pe$.
When a let-bound variable $\px$ is dead in $\pe$, we may exploit that by rewriting
the right-hand side $\pe_1$ of $\px$ to an arbitrary expression $\pe_2$ without
changing the meaning of the program, \ie, $\Let{\px}{\pe_1}{\pe} \cong \Let{\px}{\pe_2}{\pe}$.
A compiler can perform \emph{dead code removal} by choosing a very small
$\pe_2$, yielding a beneficial program optimisation.

The idea for $\semdead{\pe}$ is to overapproximate the set of variables that are
needed in $\pe$.
For example, $\semdead{f~x}_{\tr} = \tr(f) ∪ \tr(x)$, encoding that the
expression $(f~x)$ needs whatever $f$ needs and possibly what $x$ needs, which
the caller of the analysis supplies in $\tr(f)$ and $\tr(x)$, respectively.
Often, passing the ``diagonal'' $\tr_Δ(\px) \triangleq \{\px\}$ is a good
choice for the caller, in which case $\semdead{f~x}_{\tr_Δ} = \{f, x\}$ and one
might be tempted to think that $\semdead{\pe}_{\tr_Δ}$ is just a
complicated way to compute the free variables of $\pe$.
To see that this is not the case, consider $\Let{z}{y}{(f~x)}$.
Clearly, $y$ is a free variable of the expression, yet it is dead, because
$y \not∈ \{f,x\} = \semdead{\Let{z}{y}{f~x}}_{\tr_Δ}$.

In general, we can make the following \emph{soundness statement}:
$\px$ is dead in $\pe$ when $\px \not∈ \semdead{\pe}_{\tr_Δ}$.
Thus, $\semdead{\wild}$ can be used in a compiler to enable dead code removal.

\subsection{Function Summaries, Compositionality and Modularity}

%\slpj{in what way is it not-naive? being conservative on applications (no summary for functions) looks naive to me}
%\sg{What we have corresponds to DmdAnal always returning |nopSig|. That is not the most naïve analysis! See sentence about top element.}

Note that although the formulation of deadness analysis is so simple, it is
\emph{not} entirely naïve:
For example, we have
$\semdead{\Lam{y}{\Lam{z}{z}}}_{\tr_Δ} = \varnothing$, where clearly
$\Lam{y}{\Lam{z}{z}}$ should need whatever the argument to $z$ needs at an
anticipated application site.
Rather than to return the top element of the implied powerset lattice, that is,
the set of \emph{all} program variables $\Var$, it offloads accounting of what
will be needed by $z$ to the application site.
The application case in turn errs on the safe side and says that
$\Let{w}{x_3}{((\Lam{y}{\Lam{z}{z}})~x_1~x_2)}$ \emph{might} need \emph{both}
$x_1$ and $x_2$ when actually only $x_2$ is needed, in that
$\{x_1,x_2\} = \semdead{\Let{w}{x_3}{(\Lam{y}{\Lam{z}{z}})~x_1~x_2}}_{\tr_Δ}$.
However, it correctly infers that $x_3$ is dead, in contrast to the naïve
result $\Var$.
This is an example of an arguably simple \emph{summary mechanism}, inferring a
contract between function definitions and their call sites.

Put more concisely in terms of abstract interpretation~\citep{Cousot:21}:
In this work, a \emph{function summary} is an approximation to, or abstraction
of, the function's abstract transformer implied by the considered analysis.

For deadness analysis, the implied abstract transformer of the (syntactic)
function $\Lam{\px}{\pe}$ would be $T(V) \triangleq
\semdead{\pe}_{\tr[\px↦V]}$, itself a (mathematical) function taking the set
$V$ of variables that the argument at an application site needs.
The summary $S(V) \triangleq \semdead{\pe}_{\tr[\px↦\varnothing]} ∪ V$ is a
pointwise abstraction thereof, as witnessed by the following \emph{substitution
lemma}:

\begin{lemmarep}[Substitution]
\label{thm:subst-deadness}
$\semdead{\pe}_{\tr[\px↦V]} ⊆ \semdead{\pe}_{\tr[\px↦\varnothing]} ∪ V$.
\end{lemmarep}
\begin{proof}
Immediate by induction on $\pe$.
\end{proof}

We conjecture that every substitution lemma has a summary mechanism it proves correct.
%The use of (dependent) function types in type systems are good examples of this.
For example, the substitution lemma above proves correct the use of $S$
in $\semdead{\wild}$, where the mechanism is implemented such that the
constant part $\semdead{\pe}_{\tr[\px↦\varnothing]}$ is accounted for in
$\semdead{\Lam{\px}{\pe}}$ and the argument dependent part $\wild ∪ V$ is
accounted for in $\semdead{\pe~\py}$.

Any static analysis might employ a summary mechanism, but they arise naturally
for a compiler analysis such as $\semdead{\pe}$ that is \emph{compositional}:
A (static or dynamic) semantics $\denot{\wild}$ is compositional
when $\denot{\pe}$ is a function of the denotations $\denot{\pe_1}, ...,
\denot{\pe_n}$ of $\pe$'s subexpressions $\pe_1,...,\pe_n$, but \emph{not}
of the subexpressions themselves.

%Compositionality enables proofs by structural induction on $\pe$.
Compositionality implies that $\denot{\Let{\px}{\Lam{\py}{\pe_1}}{\pe_2}}$
is a function of $\denot{\Lam{\py}{\pe_1}}$, itself a function of
$\denot{\pe_1}$.
In order to satisfy the scalability requirements of a compiler and
guarantee termination of the analysis in the first place, it is
important not to repeat the work of analysing $\denot{\pe_1}$, so
$\denot{\Let{\px}{\Lam{\py}{\pe_1}}{\pe_2}}$ computes a \emph{finite} summary
(\ie, data) for $\denot{\Lam{\py}{\pe_1}}$ to apply at use sites of $\px$ in
$\pe_2$. For our deadness analysis, summarisation is baked right into the lambda
case rather than the let case.
% Doing so keeps the analysis domain simple, even though it penalises analysis
% of redexes such as $(\Lam{y}{\Lam{z}{z}})~x$ that fortunately are unlikely
% to be encountered in an optimised program.

In the same way that compositionality and finite summaries enable scalability
\emph{within} a module, they ensure \emph{modularity}~\citep{Cousot:02}, \ie,
scalability \emph{across} module boundaries.
Let us say that $f = (\Lam{y}{\Lam{z}{z}})$ is defined
in module A and there is a use site $(f~x_1~x_2)$ in module B.
To analyse the use site, we only need to load $f$'s summary from module A's
signature file, but do not need to reanalyse its definition.

%\slpj{I'm sorry I just don't get this. If you had a summary for $f$ like ``f
%does not use its first argument'' I'd be with you. But you don't. To me the
%discussion of summaries is a big red herring. The point is: both semantics an
%analysis are compositional so we get an easy proof.}
%\sg{But the summary mechanism is crucial, because it enables modularity.
%If we didn't have the summary mechanism, we would have to reanalyse the body
%of $f$, $\Lam{y}{\Lam{z}{z}}$, at every call site! Now we can simply persist
%that $f$ is summarised by $\tr ↦ \tr(f)$.
%We will get back to summaries and substitution lemmas in Section 5, when we
%discuss usage analysis proper.
%And then we really need that substitution lemma when we prove usage analysis
%correct in Section 7.
%We should discuss. You grok'd an earlier version of this section with usage
%analysis; focusing just on deadness should be strictly simpler.
%Just because the summary mechanism is so simple that you don't think it is
%useful does not mean it isn't there!
%You can only learn by looking at simple examples, and this is as simple as it gets.
%Furthermore, if you think it's so simple, try proving the substitution lemma
%below, which ``obviously'' must be true.}

\subsection{Why care for Soundness?}

A soundness theorem for a static analysis relates the results of the former to a
property of the dynamic semantics.
Such theorems can often serve a useful purpose as a teaching device.

For example, the explanation in \Cref{sec:deadness} began with a few concrete
examples and concluded with an informal soundness statement for
$\semdead{\wild}$, connecting an unfamiliar static analysis with intuition about
``deadness'' and ``evaluation'' in a more familiar reference semantics.
Nevermind the lack of a definition of a reference semantics at this point, this
kind of explanation is very common when communicating what a static analysis
does, in a lecture or on paper.

A soundness statement may help the reader to develop an intuition for an analysis,
which is vital when trying to \emph{adapt} such an analysis for their use
case, furthermore it aids coming up with viable hypotheses while
\emph{debugging} the implementation.

A soundness statement becomes \emph{indispensable} for more complicated analyses
than $\semdead{\wild}$.
We argue that for analyses such as in \citet{cardinality-ext}, there comes a point
where no paper-proper amount of examples can convince the reader that the rigorously
described analysis produces correct results, for a perceived lack of
understanding of all boundary conditions.
This is good, for when such trust is given too lightly, the result could be a
misinformed compiler optimisation, causing monetary loss at a bank or human
tragedy at an airplane company.
In such cases, a \emph{proof} for the soundness statement is in order to
establish trust and confidently treat the analysis as a working ``black box''.

Such a proof can easily grow more complicated than either the complexity of the
analayis or the semantics suggests.
To see that, we will now attempt a proof of soundness for $\semdead{\wild}$.
The first step in doing so is to formally define the correctness theorem,
and for that we need to define deadness formally, in terms of an operational
reference semantics defined next.

\subsection{Reference Semantics: Lazy Krivine Machine}
\label{sec:opsem}

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

Let us introduce the semantic ground truth of this work: The Mark II machine of
\citet{Sestoft:97} given in \Cref{fig:lk-semantics}, a small-step operational
semantics.
It is a Lazy Krivine (LK) machine implementing call-by-need.
(A close sibling for call-by-value would be a CESK machine \citep{Felleisen:87}.)
A reasonable call-by-name semantics can be recovered by removing the $\UpdateT$
rule and the pushing of update frames in $\LookupT$.
Furthermore, we will ignore $\CaseIT$ and $\CaseET$ in this section because we
do not consider data types for now.

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
%We conclude with the following example trace evaluating $\Let{i}{\Lam{x}{x}}{i~i}$:
%TODO: If we decide to bring the example below, adapt it for by-need by inserting Update transitions
%
%\[\begin{array}{c}
%  \arraycolsep2pt
%  \begin{array}{clclcl}
%             & (\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF) & \smallstep[\LetIT] & (i~i, ρ_1, μ, \StopF)
%             & \smallstep[\AppIT] & (i, ρ_1, μ, \ApplyF(\pa_1) \pushF \StopF)
%             \\
%  \smallstep[\LookupT] & (\Lam{x}{x}, ρ_1, μ, \ApplyF(\pa_1) \pushF \StopF) & \smallstep[\AppET] & (x, ρ_2, μ, \StopF) & \smallstep[\LookupT] & (\Lam{x}{x}, ρ_1, μ, \StopF)
%  \end{array} \\
%  \\[-0.5em]
%  \quad \text{where} \quad \begin{array}{lll}
%    ρ_1 = [i ↦ \pa_1] & ρ_2 = [i ↦ \pa_1, x ↦ \pa_1] & μ = [\pa_1 ↦ (ρ_1,\Lam{x}{x})]. \\
%  \end{array}
%\end{array}\]

\subsection{Formal Proof of Soundness}

We will now establish a formal grasp on our previously informal notion of deadness:

\begin{definition}[Operational Deadness]
  \label{defn:deadness}
  A variable $\px$ is \emph{needed} in an expression $\pe$
  if and only if there exists a trace
  $(\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],\wild,\wild) \smallstep^* (\py,ρ'[\py↦\pa],\wild,\wild)$
  that is about to evaluate $\px$, \ie, look up its heap entry.
  Otherwise, $\px$ is \emph{dead} in $\pe$.
\end{definition}

The elaborate setup of this definition ensures that $\pa$, the address that
$\px$ binds, does not alias with anything defined in the initial heap $μ$ and
thus not with anything in $ρ$ or $κ$.
Unsurprisingly, the no-alias property is easily defeated during evaluation, as
soon as $\px$ is passed as an argument, hence $\py$ can be chosen differently to
$\px$ in \Cref{defn:deadness}.
%For example, after transitioning through $\AppIT, \AppET$ in
%$((\Lam{y}{x+y})~x, [x↦\pa_1], [\pa_1↦...], \StopF)$, both $x$ and $y$
%bind the same address.

Using this notion of deadness, we can finally state and prove the soundness
theorem, thus%
\footnote{All proofs can be found in the Appendix; in case of the extended
version via clickable links.}

\begin{toappendix}
% Problems:
% 1. Let case introduces aliasing. Can't apply neededness directly, unless we
%    rewrite RHSs. But that would be cheating, because that is not possible for
%    more interesting analyses
% 2. Need strengthen IH. General framework: Extend analysis to configurations
%    (huge function, but entirely derived from E[[_]]), show preservation
% 3. Show that $C[[σ]] ⊆ E[[e]]$ for the initial state of the trace, then
%    property analysis result is preserved by monotonicity
% 4. Hand-wavy in several claims; preservation and UpdateT, that there exists an
%    evaluation context in which $\px$ is not in the heap yet

Whenever there exists $\tr$ such that $\tr(\px) \not⊆ \semdead{\pe}_\tr$,
then also $\tr_Δ(\px) \not⊆ \semdead{\pe}_{\tr_Δ}$.
The following lemma captures this intuition:

\begin{lemma}[Diagonal factoring]
\label{thm:diag-fact}
Every instantiation of $\semdead{\pe}$ factors through $\semdead{\pe}_{\tr_Δ}$,
that is,
\[
  \semdead{\pe}_\tr = \tr(\semdead{\pe}_{\tr_Δ}) = \{ \tr(\px) \mid \px ∈ \semdead{\pe}_{\tr_Δ} \}
\]
\end{lemma}
\begin{proof}
By induction on $\pe$.
\begin{itemize}
  \item \textbf{Case $\pe = \py$}:
    We assert $\semdead{\py}_\tr = \tr(\py) = \{ \tr(\px) \mid \px ∈ \tr_Δ(\py) \}$.
  \item \textbf{Case $\pe = \pe'~\py$}:
    Applying the induction hypothesis, we get
    \[
      \semdead{\pe'~\py}_\tr = \semdead{\pe'}_\tr ∪ \tr(\py) = \tr(\semdead{\pe'}_{\tr_Δ} ∪ \{ \tr(\px) \mid \px ∈ \tr_Δ(\py) \}).
    \]
  \item Other cases are simple application of the induction hypothesis.
\end{itemize}
\end{proof}

\begin{lemma}[Immediate fixpoint]
\label{thm:dead-fix}
Every fixpoint is reached after one iteration:
\[
  \lfp(\fn{V}{\semdead{\pe}_{\tr[\px↦V]}}) = \semdead{\pe}_{\tr[\px↦\varnothing]}
\]
\end{lemma}
\begin{proof}
Immediate by induction on $\pe$.
\end{proof}

We need to presume that every heap entry is annotated with the let-bound
variable from whence it was allocated; otherwise there is no way to map
addresses to syntax.
Hence we will write heap entries as triples $\pa↦(\px,ρ,\pe)$, where
$\px$ is from the unique let binding $\Let{\px}{...}{...}$ in the program
that allocated the heap entry.
This information is born redundant, because $\px$ is the unique variable for
which $\pa = ρ(\px)$, but it becomes non-redudant after heap update potentially
replaces $(ρ,\pe)$ with the value.

\begin{figure}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semdeadS{\wild} \colon \States → \pow{\Var} } } \\
  \\[-0.5em]
  \semdeadS{(\pe,ρ,μ,κ)} & {}={} & \semdead{\pe}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \\
  \text{where } α(μ) & {}={} & \lfp(\fn{\tm}{[ \pa ↦ \{\px\} ∪ \semdead{\pe'}_{\tm \circ ρ'} \mid μ(\pa) = (\px,ρ',\pe') ]}) \\
             \mathit{args}(κ) & {}={} & \{ \pa \mid κ = ... \pushF \ApplyF(\pa) \pushF ... \}
  \\[-0.5em]
\end{array}\]
\caption{Deadness analysis extended to small-step configurations}
  \label{fig:deadness-ext}
\end{figure}

In \Cref{fig:deadness-ext}, we give the extension of $\semdeadS{\wild}$ to whole
machine configurations $σ$.
Although $\semdeadS{\wild}$ looks like an entirely new definition, it is
actually derivative of $\semdead{\wild}$ via a context lemma à la
\citet[Lemma 3.2]{MoranSands:99}:
The environments $ρ$ simply govern the transition from syntax to
operational representation in the heap.
The bindings in the heap are to be treated as mutually recursive let bindings,
hence a fixpoint is needed.
For safety properties such as deadness, a least fixed-point is appropriate.
Apply frames on the stack correspond to the application case of $\semdead{\wild}$
and hence encode a need for the whole heap entry they point to.
Update frames are ignored because our analysis is not heap-sensitive.

Now we can prove that $\semdeadS{\wild}$ is preserved/improves during reduction:

\begin{lemma}[Preservation of $\semdeadS{\wild}$]
\label{thm:preserve-dead}
If $σ_1 \smallstep σ_2$, then $\semdeadS{σ_1} \supseteq \semdeadS{σ_2}$.
\end{lemma}
\begin{proof}
By cases on the transition.
\begin{itemize}
  \item \textbf{Case }$\LetIT$: Then $\pe = \Let{\py}{\pe_1}{\pe_2}$ and
    \[
      (\Let{\py}{\pe_1}{\pe_2},ρ,μ,κ) \smallstep (\pe_2,ρ[\py↦\pa],μ[\pa↦(\py,ρ[\py↦\pa],\pe_1)],κ).
    \]
    Abbreviating $ρ_1 \triangleq ρ[\py↦\pa], μ_1 \triangleq μ[\pa ↦ (\py,ρ_1,\pe_1)$, we have
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\Let{\py}{\pe_1}{\pe_2}}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Unfold $\semdead{\Let{\py}{\pe_1}{\pe_2}}$} \\
      {}={}& \semdead{\pe_2}_{(α(μ) \circ ρ)[\py↦\{\py\}∪\semdead{\pe_1}_{(α(μ) \circ ρ)[\py↦\varnothing]}]} ∪ α(μ)(\mathit{args}(κ)) \Arrow{\Cref{thm:dead-fix}} \\
      {}={}& \semdead{\pe_2}_{(α(μ) \circ ρ)[\py↦\{\py\}∪\lfp(\fn{S}{\semdead{\pe_1}_{(α(μ) \circ ρ)[\py↦S]}})]} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Move fixpoint outwards, refold $α$} \\
      {}={}& \semdead{\pe_2}_{α(μ_1) \circ ρ_1} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Stack was well-addressed in $μ$} \\
      {}={}& \semdead{\pe_2}_{α(μ_1) \circ ρ_1} ∪ α(μ_1)(\mathit{args}(κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\AppIT$:
    Then $(\pe'~\py,ρ,μ,κ) \smallstep (\pe',ρ,μ,\ApplyF(ρ(\py)) \pushF κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\pe'~\py}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Unfold $\semdead{\pe'~\py}_{(α(μ) \circ ρ)}$} \\
      {}={}& \semdead{\pe'}_{α(μ) \circ ρ} ∪ \{ α(μ)(ρ(\py)) \} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Rearrange} \\
      {}={}& \semdead{\pe'}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(\ApplyF(ρ(\py)) \pushF κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\AppET$:
    Then $(\Lam{\py}{\pe'},ρ,μ,\ApplyF(\pa) \pushF κ) \smallstep (\pe',ρ[\py↦\pa],μ,κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\Lam{\py}{\pe'}}_{α(μ) \circ ρ} ∪ α(μ)(\pa) ∪ α(μ)(\mathit{args}(κ)) \Arrow{Unfold $\semdead{\Lam{\py}{\pe'}}_{(α(μ) \circ ρ)}$} \\
      {}={}& \semdead{\pe'}_{(α(μ) \circ ρ)[\py↦\varnothing]} ∪ α(μ)(\pa) ∪ α(μ)(\mathit{args}(κ)) \Arrow{\Cref{thm:subst-deadness}} \\
      {}\supseteq{}& \semdead{\pe'}_{(α(μ) \circ ρ)[\py↦α(μ)(\pa)]} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Rearrange} \\
      {}={}& \semdead{\pe'}_{(α(μ) \circ ρ[\py↦\pa])} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\LookupT$:
    Then $\pe = \py$, $\pa \triangleq ρ(\py)$, $(\py,ρ',\pe') \triangleq μ(\pa)$ and
    $(\py,ρ,μ,κ) \smallstep (\pe',ρ',μ,\UpdateF(\pa) \pushF κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\py}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Unfold $\semdead{\py}$} \\
      {}={}& (α(μ) \circ ρ)(\py) ∪ ... \Arrow{Unfold $α$} \\
      {}={}& \{\py\} ∪ \semdead{\pe'}_{α(μ) \circ ρ'} ∪ ... \Arrow{Drop $\{\py\}$} \\
      {}\supset{}& \semdead{\pe'}_{α(μ) \circ ρ'} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\UpdateT$:
    Then $(\pv, ρ, μ[\pa↦(\py,ρ',\pe')], \UpdateF(\pa) \pushF κ) \smallstep (\pv,ρ,μ[\pa↦(\py,ρ,\pv)],κ)$.

    This case is a bit hand-wavy and shows how heap update during by-need
    evaluation is dreadfully complicated to handle, even though
    $\semdead{\wild}$ is correct heap-less and otherwise correct \wrt by-name
    evaluation.
    The culprit is that in order to show $\semdeadS{σ_2} ⊆ \semdeadS{σ_1}$, we
    have to show
    \begin{equation}
      \semdead{\pv}_{α(μ) \circ ρ} ⊆ \semdead{\pe'}_{α(μ') \circ ρ'}. \label{eqn:dead-upd}
    \end{equation}

    Intuitively, this is somewhat clear, because $μ$ ``evaluates to'' $μ'$ and
    $\pv$ is the value of $\pe'$, in the sense that there exists
    $σ'=(\pe',ρ',μ',κ)$ such that $σ' \smallstep^* σ_1 \smallstep σ_2$.

    Alas, who guarantees that such a $σ'$ actually exists?
    We would need to rearrange the lemma for that and argue by step indexing
    (a.k.a. coinduction) over prefixes of \emph{maximal traces} (to be
    rigorously defined later).
    That is, we presume that the statement
    \[
      \forall n.\ σ_0 \smallstep^n σ_2 \Longrightarrow \semdeadS{σ_2} ⊆ \semdeadS{σ_0}
    \]
    has been proven for all $n < k$ and proceed to prove it for $n = k$.
    So we presume $σ_0 \smallstep^{k-1} σ_1 \smallstep σ_2$ and $\semdeadS{σ_1} ⊆ \semdeadS{σ_0}$
    to arrive at a similar setup as before, only with a stronger assumption
    about $σ_1$.
    Specifically, due to the balanced stack discipline we know that
    $σ_0 \smallstep^{k-1} σ_1$ factors over $σ'$ above.
    We may proceed by induction over the balanced stack discipline (we will see
    in \Cref{sec:adequacy} that this amounts to induction over the big-step
    derivation) of the trace $σ' \smallstep^* σ_1$ to show \Cref{eqn:dead-upd}.

    This reasoning was not specific to $\semdead{\wild}$ at all.
    We will show a more general result in Lemma \labelcref{thm:memo-improves}
    that can be reused across many more analyses.

    Assuming \Cref{eqn:dead-upd} has been proven, we proceed
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\pv}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Above argument that $\semdead{\pv}_{α(μ) \circ ρ} ⊆ \semdead{\pe'}_{α(μ') \circ ρ'}$} \\
      {}\supseteq{}& \semdead{\pv}_{α(μ[\pa↦(\py,ρ,\pv)]) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}
%    NB: This result is doubly subtle in that heap update may change the data dependencies of the heap;
%    For example, $\Let{x}{\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}}{x}$ will
%    evaluate to a mutually recursive heap
%    \[
%      [\pa_1↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~y), \pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)],
%    \]
%    whereas before the final heap update to $\pa_1$ we have
%    \[
%      [\pa_1↦([x↦\pa_1],\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}),\pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)].
%    \]
\end{itemize}
\end{proof}
\end{toappendix}

\begin{theoremrep}[Correct deadness analysis]
  \label{thm:deadness-correct}
  If $\px \not∈ \semdead{\pe}_{\tr_Δ}$,
  then $\px$ is dead in $\pe$.
\end{theoremrep}
\begin{proof}
We show the contraposition, that is,
if $\px$ is needed in $\pe$, then $\px ∈ \semdead{\pe}_{\tr_Δ}$.

Since $\px$ is needed in $\pe$, there exists a trace
\[
  (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],μ[\pa↦(\px,ρ[\px↦\pa],\pe')],κ) \smallstep^* (\py,ρ'[\py↦\pa],μ',κ').
\]
Let us abbreviate $ρ_1 \triangleq ρ[\px↦\pa]$, $μ_1 \triangleq μ[\pa↦(\px,ρ[\px↦\pa],\pe')]$.

Without loss of generality, we assume that there is no other heap entry for
$\px$ yet -- this may happen under a lambda that is called multiple times, and
when that happens we can always find a simpler evaluation context in which this
is not the case.
(This is a subtle claim that we would have to prove as well if we were serious.)
Furthermore, let us assume that this is the first lookup at $\pa$, so $μ'(\pa) = μ_1(\pa) = (\px, ρ_1,\pe')$.

Let us abbreviate $\tr \triangleq (α(μ_1) \circ ρ_1)$.
Under the above assumptions, $\px ∈ \tr(\py)$ implies $\px = \py$ for all
$\py$, because $μ_1(\pa)$ is the only heap entry in which $\px$ occurs.

By unfolding $\semdeadS{\wild}$ and $\semdead{\py}$ we can see
that $\px ∈ α(μ')(\pa) ⊆ \semdeadS{(\py,ρ'[\py↦\pa],μ',κ')}$.
By \Cref{thm:preserve-dead} and transitivity, we also have
$\px ∈ \semdeadS{(\pe,ρ_1,μ_1,κ)}$.
Since there was no other heap entry for $\px$ and $\pa$ cannot occur in $κ$ or
$ρ$ due to well-addressedness, we have $\px ∈ \semdeadS{(\pe,ρ_1,μ_1,κ)}$ if
and only if $\px ∈ \semdead{\pe}_{\tr}$.
With \Cref{thm:diag-fact}, we can decompose
\[
  \px ∈ \semdead{\pe}_{\tr} = \tr(\semdead{\pe}_{\tr_Δ}) = \{ \tr(\px) \mid \px ∈ \semdead{\pe}_{\tr_Δ} \}
\]
But since $\px ∈ \tr(\py)$ implies $\px = \py$, so we must have $\px ∈
\semdead{\pe}_{\tr_Δ}$, as required.
\end{proof}

The proof follows an established preservation-style proof technique%
\footnote{A ``mundane approach`` according to \citet[Section
4.1]{Nielson:99}, applicable to \emph{trace properties}, but not to
\emph{hyperproperties}~\citep{ClarksonSchneider:10}.}
that scales beyond simple analyses such as $\semdead{\wild}$ and is roughly
structured as follows:

\begin{itemize}
  \item Extend the analysis function $\semdead{\pe}$ to a function
    $\semdeadS{σ}$ on whole machine configurations $σ$.
    This process is tedious and non-trivial busywork that leads to
    substantial duplication of $\semdead{\wild}$.
    Fortunately it is \emph{derivative} as well, because any configuration
    $(\pe,ρ,μ,κ)$ can be turned into a closed expression $\pE[\pe]$ such
    that the evaluation context $\pE$ is derived from $(ρ,μ,κ)$ via a
    \emph{context lemma}~\citep[Lemma 3.2]{MoranSands:99}, and
    $\semdead{\pE[\pe]}_{[]}$ is the specification for $\semdeadS{σ}$.
  \item Prove a preservation lemma, \ie,
    $σ_1 \smallstep σ_2 \Longrightarrow \semdeadS{σ_1} \supseteq \semdeadS{σ_2}$.
    The highlights are:
    (1) The $\AppET$ case needs \Cref{thm:subst-deadness}.
    (2) The $\LetIT$ case needs to reason about fixpoints to add the new binding to the
    heap.
    (3) The by-need-specific $\UpdateT$ proof mutates the heap and is far harder
    than one would expect for a heap-less analysis such as $\semdead{\wild}$
    that is intuitively sound for by-name evaluation.
    We resort to hand-waving and defer to our later proof in
    \Cref{sec:by-need-soundness}.
  \item The proof for \Cref{thm:deadness-correct} massages the statement into a
    form that it follows from the preservation lemma.
    Again, this step held more surprises than we thought possible, even
    as we rewrote this section \emph{after} the considerably more general
    proof in \Cref{sec:by-need-soundness} was finished.
\end{itemize}

The main takeaway:
Although analysis and semantics are simple, the proof is not.
The ``main payload'' of the proof that concerns deadness analysis is
drowned in coping with semantic subtleties that are shared with similar
analyses.
It would be preferable to find a framework to \emph{prove these distractions
separately}, once and for all, and then instantiate this framework for deadness
analysis such that only the highlights of the preservation proof need to be
shown.

Abstract interpretation provides such a framework.
Alas, \citet{Cousot:21} starts from a \emph{compositional} semantics to
derive compositional analyses, but small-step operational semantics are
non-compositional!
This begs the question if we could have started from a compositional
denotational semantics.
While we could have done so for deadness or strictness analysis, denotational
semantics is insufficient to express \emph{operational properties} such
as ``$\pe$ evaluates $\px$ at most $u$ times''%
\footnote{A more useful application of the ``at most once'' cardinality is the
identification of \emph{one-shot} lambdas~\citep{cardinality-ext} --- functions
which are called at most once for every activation --- because it allows for
inlining computations into function bodies.},
so we cannot prove that this so-called \emph{usage analysis} can be used for
update avoidance~\citep{Gustavsson:98}.

Conversely, \citet{aam,adi,Keidel:18} have successfully applied abstract interpretation
to non-compositional (small-step or big-step) operational semantics to derive
interprocedural analyses based on reachable states abstractions.
The resulting analyses are likewise non-compositional, non-modular and generally
devoid of summary mechanisms, however, and thus likely much different to
$\semdead{\wild}$.

For these reasons, we set out to find a \textbf{\emph{compositional semantics
that exhibits operational detail}} just like the trace-generating semantics of
\citet{Cousot:21}, and were successful.
The example of usage analysis in \Cref{sec:abstractions} (generalising
$\semdead{\wild}$, as suggested above) demonstrates that we can
\textbf{\emph{derive summary-based analyses as an abstract interpretation}} from
our semantics.
Since both semantics and analysis are derived from the same compositional
interpreter skeleton, the correctness proof for usage analysis in
\Cref{thm:usage-correct} takes no more than a substitution lemma and a bit of
plumbing.
Hence our \emph{Denotational Interpreter} does not only enjoy useful
compositional semantics and analyses as instances, the soundness proofs become
compositional as well, building on reusable evaluation-order-specific theorems
such as \Cref{thm:soundness-by-name}.
