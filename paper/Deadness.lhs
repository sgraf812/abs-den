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
  \multicolumn{3}{c}{ \ruleform{ \semdead{\wild}_{\wild} \colon \Exp → (\Var → \pow{\Var}) → \pow{\Var} } } \\
  \\[-0.5em]
  \semdead{\px}_\tr & {}={} & \tr(\px) \\
  \semdead{\Lam{\px}{\pe}}_\tr & {}={} & \semdead{\pe}_{\tr[\px ↦ \varnothing]} \\
  \semdead{\pe~\px}_\tr & {}={} & \semdead{\pe}_\tr ∪ \tr(\px) \\
  \semdead{\Letsmall{\px}{\pe_1}{\pe_2}}_\tr & {}={} & \semdead{\pe_2}_{\tr[\px ↦ \{\px\} ∪ \semdead{\pe_1}_{\tr[\px ↦ \varnothing]}]}
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
We argue that for analyses such as in \citet{Sergey:14}, there comes a point
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

    This case is a bit hand-wavy and shows how heap update during by-need is quite complicated to handle.

    $\pv$ is the value of $\pe'$, in the sense that there exists $σ'=(\pe',ρ',μ',κ)$ such that $σ' \smallstep^* σ_1 \smallstep σ_2$.
    Here, we'd need to rearrange the lemma we are about to prove so that it considers ever longer prefixes of
    the implied trace; then we would be able to argue coinductively, by step indexing, that $\semdeadS{σ_1} ⊆ \semdeadS{σ'}$
    and hence that $\semdead{\pv}_{α(μ) \circ ρ} ⊆ \semdead{\pe'}_{α(μ') \circ ρ'}$.
    We will show a more general result in \Cref{thm:memo-improves}.

    With that in mind, we can prove
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semdeadS{σ_1} \Arrow{Unfold $\semdeadS{σ_1}$} \\
      {}={}& \semdead{\pv}_{α(μ) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Above argument that $\semdead{\pv}_{α(μ) \circ ρ} ⊆ \semdead{\pe'}_{α(μ') \circ ρ'}$} \\
      {}\supseteq{}& \semdead{\pv}_{α(μ[\pa↦(\py,ρ,\pv)]) \circ ρ} ∪ α(μ)(\mathit{args}(κ)) \Arrow{Refold $\semdeadS{σ_2}$} \\
      {}={}& \semdeadS{σ_2}
    \end{DispWithArrows*}
    NB: This result is doubly subtle in that heap update may change the data dependencies of the heap;
    For example, $\Let{x}{\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}}{x}$ will
    evaluate to a mutually recursive heap
    \[
      [\pa_1↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~y), \pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)],
    \]
    whereas before the final heap update to $\pa_1$ we have
    \[
      [\pa_1↦([x↦\pa_1],\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}),\pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)].
    \]
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

The proof follows an established preservation-style proof pattern that scales
beyond simple analyses such as $\semdead{\wild}$ and is roughly structured as
follows:

\begin{itemize}
  \item Extend the analysis function $\semdead{\wild}$ to whole machine
    configuration $σ$.
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
    (2) The $\LetIT$ needs to reason about fixpoints to add the new binding to the
    heap.
    (3) The by-need-specific $\UpdateT$ proof mutates the heap and is far harder
    than one would expect for a heap-less analysis such as $\semdead{\wild}$
    that is intuitively sound for by-name evaluation.
    We resort to hand-waving and defer to our later proof in
    \Cref{sec:by-need-soundness}.
  \item The proof for \Cref{thm:deadness-correct} massages the statement into a
    form that it follows from the preservation lemma.
    Again, this step held more surprises than we thought possible, even
    though we rewrote this section \emph{after} the considerably more general
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
The example of usage analysis (generalising $\semdead{\wild}$, as suggested
above) in \Cref{sec:abstractions} demonstrates that we can \textbf{\emph{derive
summary-based analyses as an abstract interpretation}} from our semantics.
Since both semantics and analysis are derived from the same compositional
interpreter skeleton, the correctness proof for usage analysis in
\Cref{thm:usage-correct} takes no more than a substitution lemma and a bit of
plumbing.
Hence our \emph{denotational interpreter} does not only enjoy useful
compositional semantics and analyses as instances, the soundness proofs become
compositional as well, building on reusable evaluation-order-specific theorems
such as \Cref{thm:soundness-by-name}.

\begin{comment}
\subsection{OLD}

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

We can formalise correctness of the summary mechanism with the following
\emph{substitution lemma}:%
\footnote{All proofs can be found in the Appendix; in case of the extended
version via clickable links.}

That is, if $\pz ∈ \semdead{(\Lam{\px}{\pe})~\py}_{\tr}$, then $\pz ∈ \semdead{\pe}_{\tr[\px↦\tr(\py)]}$.
A similar lemma can be derived for $\mathbf{let}$.
The substitution lemma is often instrumental in correctness proofs, although in
this case it is so simple (the proof is right in the premise of
\textsc{Lam}) that it can be inlined when proving deadness analysis correct in
terms of semantic irrelevance below: \sg{Update this}

\begin{theoremrep}[Correct deadness analysis]
  \label{thm:deadness-correct}
  If $\tr(\px) \not⊆ \semdead{\pe}_\tr$,
  then $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
\end{theoremrep}
\begin{proof}
  By induction on $\pe$.
  \begin{itemize}
    \item \textbf{Case $\pe = \py$}: If $\px=\py$, then we have
      $\tr(\px) = \semdead{\pe}_\tr$, a contradiction.
      If $\px \not= \py$, then $ρ[\px↦d_1](\py) = ρ(\py) = ρ[\px↦d_2](\py)$.

    \item \textbf{Case $\pe = \Lam{\py}{\pe'}$}: The equality follows from
      pointwise equality on functions, so we pick an arbitrary $d$ to show
      $\semscott{\pe'}_{ρ[\px↦d_1][\py↦d]} = \semscott{\pe'}_{ρ[\px↦d_2][\py↦d]}$.

      This is simple to see if $\px=\py$. Otherwise, $\tr[\py↦\varnothing]$ witnesses the fact that
      \[
        \tr[\py↦\varnothing](\px) = \tr(\px) \not⊆
        \semdead{\Lam{\py}{\pe'}}_{\tr} = \semdead{\pe'}_{\tr[\py↦\varnothing]}
      \]
      so we can apply the induction hypothesis to see that $\px$ must be dead in
      $\pe'$, hence the equality on $\semscott{\pe'}$ holds.

    \item \textbf{Case $\pe = \pe'~\py$}:
      By rule \textsc{App}, we have $\dead{Γ}{\pe'}$ and $\py ∈ Γ$.
      We apply the induction hypothesis to get
      $\semscott{\pe'}_{ρ[\px↦d_1]} = \semscott{\pe'}_{ρ[\px↦d_2]}$, which
      either is $\bot$ or some function $f$.

      In the former case, both applications evaluate to $\bot$.
      In the latter case, we have to prove that $f(ρ[\px↦d_1](\py)) =
      f(ρ[\px↦d_2](\py))$, but that is easy to see as well,
      because $\px \not∈ Γ$ while $\py ∈ Γ$ implies that $\px \not= \py$.

    \item \textbf{Case $\pe = \pe'~\py$}:
      From $\tr(\px) \not⊆ \semdead{\pe'}_{\tr} ∪ \tr(\py)$ we can see that
      $\tr(\px) \not⊆ \semdead{\pe'}_{\tr}$ and $\tr(\px) \not⊆ \tr(\py)$.

      If $\px=\py$ then the latter inequality leads to a contradiction.
      Otherwise, $\px$ must be dead in $\pe'$, and the induction hypothesis
      yields
      $\semscott{\pe'}_{ρ[\px↦d_1]} = \semscott{\pe'}_{ρ[\px↦d_2]}$, which
      either is $\bot$ or some function $f$.

      In the former case, both applications evaluate to $\bot$.
      In the latter case, we have to prove that $f(ρ[\px↦d_1](\py)) =
      f(ρ[\px↦d_2](\py))$, but that is easy to see as well,
      because $\px \not= \py$.

    \item \textbf{Case $\pe = \Let{\py}{\pe_1}{\pe_2}$}:
      We have to show that
      \[
        \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
      \]
      where $d'_i$ satisfy $d'_i = \semscott{\pe_1}_{ρ[\px↦d_i][\py↦d'_i]}$.
      The case $\px = \py$ is simple to see, because $ρ[\px↦d_i](\px)$ is
      immediately overwritten, hence both environments equate.

      Let $\tr' \triangleq \tr[\py ↦ \{\py\} ∪ \semdead{\pe_1}_{\tr[\py↦\varnothing]}]$.
      We proceed by case on $\tr(\px) ⊆ \semdead{\pe_1}_{\tr[\py↦\varnothing]}$:
      \begin{itemize}
        \item \textbf{Case $\tr(\px) ⊆ \semdead{\pe_1}_{\tr[\py↦\varnothing]}$}:
          Then $\tr'(\px) ⊆ \tr'(\py)$ and $\py$ is also dead in $\pe_2$ by
          the above inequality.
          Both deadness facts together allow us to rewrite
          \[
            \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_2]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
          \]
          as requested.
        \item \textbf{Case $\tr(\px) = \tr[\py↦\varnothing](\px) \not⊆ \semdead{\pe_1}_{\tr[\py↦\varnothing]}$}:
          Then $\px$ is dead in $\pe_1$ and $d'_1 = d'_2$. The goal follows
          from the fact that $\px$ is dead in $\pe_2$.
      \end{itemize}
  \end{itemize}
\end{proof}

The semantics $\semscott{\wild}$ and analysis $\semdead{\wild}$ are
both defined by \emph{structural recursion} over the expression. In other words, they
are both \emph{compositional} in the sense that the meaning of an expression
is obtained by combining the meanings of its sub-expressions.
Moreover, because the semantics and the analysis are so similar in structure,
it is easy to prove the analysis sound by induction on the program expression.
The proof is simple and direct, at barely a page in length.
Indeed, leaning on the deep notion of equality in $\ScottD$,%
\footnote{Thus we stay blissfully unaware of the lack of full
abstraction~\citep{Plotkin:77}.}
we don't even need to strengthen the induction hypothesis for the application
case.

Alas, there are problems with this framework:
\slpj{I took "this framework" to mean the compositional semantics + analysis.  But then the third bullet is about oprerational semantics -- very confusing.}
\sg{I improved, by splitting the points in two. Do have another look.}
\begin{enumerate}[label=(P\arabic*)]
% Simon convinced me of his unconvincedness:
%  \item
%    Denotational semantics are fundamentally restricted in the way they
%    \textbf{\emph{represent diverging computations}}, in that any such computation must
%    be denoted by $\bot$.
%    Thus, a denotational semantics cannot be used to prove that an analysis
%    yields safe results on diverging programs.
  \item
    \Cref{thm:deadness-correct} yields credible proof that the implied
    transformation is sound, but none whatsoever on whether it is
    \textbf{\emph{contextually improving}}~\citep{MoranSands:99}, \ie, an
    optimisation.
    Contextual improvement needs a semantics in which the number of steps
    evaluation takes can be observed (\ie, its \emph{cost}).
    This is not possible in $\semscott{\wild}$, but \citet{HackettHutton:19}
    give a denotational cost semantics \wrt which we can reformulate
    \Cref{thm:deadness-correct}; then, contextual improvement follows from
    definitional equality.

    Unfortunately, for more interesting transformations, we cannot lean on
    definitional equality modulo the cost semantics for a lack of full
    abstraction~\citep{Plotkin:77}, in which case a direct proof requires both
    induction on $\pe$ as well as induction over the context $\pC$ of the
    improvement relation.
    It is often preferable to decompose this proof :
    (1) The analysis is shown to imply a strong enough semantic property,
    one mentioning the semantics but not the analysis.
    (2) That semantic property is used to show improvement of the
    transformation.

    Abstract interpretation~\citep{Cousot:21} is a successful theory to abstract
    properties of (small-step) execution traces in order to make step (1).
    We discuss in \Cref{sec:related-work} why our work would not improve on the
    second step.
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
\end{enumerate}

So let us address these points by proving $\semdead{\wild}$ correct \wrt a
small-step operational semantics instead.

\sg{TODO}

These points could be addressed by relating the analysis to a small-step
operational semantics instead of a denotational semantics.
However, that comes with its own set of drawbacks:
\begin{itemize}
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

\end{comment}

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

