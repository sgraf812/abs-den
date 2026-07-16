%if style == newcode
> module OpSem where
%endif

\section{Reference Semantics and Adequacy}

Having defined our denotational interpreter (\Cref{sec:interp}), we now hold it to
account against a reference operational semantics, proving that
|evalNeed2|%
\footnote{Similar results for |evalName| should be derivative.}
is a faithful \emph{denotational semantics}: \emph{total} (well-defined for every
input) and \emph{adequate} (faithful to the reference's termination behaviour).
Our reference is the lazy Krivine (LK) machine, and adequacy takes the strong form
of a \emph{bisimulation} between the interpreter's traces and the machine's runs.
To our knowledge, |evalNeed2| is the first denotational call-by-need semantics
with such a bisimulation proof, which lets us move freely between machine and
interpreter.
The results are mechanised in Lean (\Cref{sec:mechanisation}).

\subsection{The Lazy Krivine Machine}
\label{sec:op-sem}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep3pt
 \begin{array}{rrclcl@@{\hspace{1.5em}}rrcrclcl}
  \text{Addresses}     & \pa & ∈ & \Addresses     & \simeq & ℕ
  &
  \text{States}        & σ   & ∈ & \States        & =      & \Exp \times \Environments \times \Heaps \times \Continuations
  \\
  \text{Environments}  & ρ   & ∈ & \Environments  & =      & \Var \pfun \Addresses
  &
  \text{Heaps}         & μ   & ∈ & \Heaps         & =      & \Addresses \pfun \Var \times \Environments \times \Exp
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
\LetIT & (\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) & \smallstep & (\pe_2,ρ',μ[\pa↦(\px,ρ',\pe_1)], κ) & \pa \not∈ \dom(μ),\ ρ'\! = ρ[\px↦\pa] \\
\AppIT & (\pe~\px,ρ,μ,κ) & \smallstep & (\pe,ρ,μ,\ApplyF(\pa) \pushF κ) & \pa = ρ(\px) \\
\CaseIT & (\Case{\pe_s}{\Sel[r]},ρ,μ,κ) & \smallstep & (\pe_s,ρ,μ,\SelF(ρ,\Sel[r]) \pushF κ) & \\
\LookupT(\py) & (\px, ρ, μ, κ) & \smallstep & (\pe, ρ', μ, \UpdateF(\pa) \pushF κ) & \pa = ρ(\px),\ (\py,ρ',\pe) = μ(\pa) \\
\AppET & (\Lam{\px}{\pe},ρ,μ, \ApplyF(\pa) \pushF κ) & \smallstep & (\pe,ρ[\px ↦ \pa],μ,κ) &  \\
\CaseET & (K'~\many{y},ρ,μ, \SelF(ρ',\Sel) \pushF κ) & \smallstep & (\pe_i,ρ'[\many{\px_i ↦ \pa}],μ,κ) & K_i = K',\ \many{\pa = ρ(\py)} \\
\UpdateT & (\pv, ρ, μ, \UpdateF(\pa) \pushF κ) & \smallstep & (\pv, ρ, μ[\pa ↦ (\px,ρ,\pv)], κ) & μ(\pa) = (\px,\wild,\wild),\ ρ \vdash \pv \\
\bottomrule
\end{tabular}
} % resizebox
\caption{Lazy Krivine transition semantics $\smallstep$}
  \label{fig:lk-semantics}
\end{figure}

The semantic ground truth of this work and others~\citep{Gustavsson:98, Sergey:14,
Breitner:16} is the Mark II machine of \citet{Sestoft:97} given in
\Cref{fig:lk-semantics}, a small-step operational semantics.
(A close sibling for call-by-value would be a CESK machine \citep{Felleisen:87}.)
A reasonable call-by-name semantics can be recovered by removing the $\UpdateT$
rule and the pushing of update frames in $\LookupT$.
%Furthermore, we will ignore $\CaseIT$ and $\CaseET$ in this section because we
%do not consider data types for now.

The configurations $σ$ in this transition system resemble abstract machine
states, consisting of a control expression $\pe$, an environment $ρ$ mapping
lexically-scoped variables to their current heap address, a heap $μ$ listing a
closure for each address, and a stack of continuation frames $κ$.
There is one harmless non-standard extension, present so that the machine's
transitions line up with the |Event|s our interpreter emits (\Cref{sec:interp}):
each $\LookupT$ transition records the let-bound variable $\py$ that allocated the
heap binding about to be looked up, mirroring the interpreter's |Look y| event.
The association from address to let-bound variable is maintained in the first
component of a heap entry triple and requires slight adjustments of the $\LetIT$,
$\LookupT$ and $\UpdateT$ rules.

The notation $f ∈ A \pfun B$ used in the definition of $ρ$ and $μ$ denotes a
finite map from $A$ to $B$, a partial function where the domain $\dom(f)$ is
finite.
The literal notation $[a_1↦b_1,...,a_n↦b_n]$ denotes a finite map with domain
$\{a_1,...,a_n\}$ that maps $a_i$ to $b_i$. Function update $f[a ↦ b]$
maps $a$ to $b$ and is otherwise equal to $f$.

The initial machine state for a closed expression $\pe$ is given by the
injection function $\init(\pe) = (\pe,[],[],\StopF)$ and
the final machine states are of the form $(\pv,\wild,\wild,\StopF)$.
We bake into $σ∈\States$ the simplifying invariant of \emph{well-addressedness}:
Any address $\pa$ occurring in $ρ$, $κ$ or the range of $μ$ must be an element of
$\dom(μ)$.
It is easy to see that the transition system maintains this invariant and that
it is still possible to observe scoping errors which are thus confined to lookup
in $ρ$.

One such error concerns constructor fields. Call a \emph{value} $\pv$ (a lambda or a
constructor application $K~\many{\py}$) an \emph{answer} in $ρ$, written $ρ \vdash \pv$,
when $\pv$ is a lambda, or $\pv = K~\many{\py}$ with every field in scope,
$\many{\py} ⊆ \dom(ρ)$.
A constructor with an out-of-scope field is not an answer; it is stuck at its build
site, exactly as the interpreter's |Con| is stuck on an out-of-scope field.
The $\UpdateT$ rule and a successful final state range only over answers, so an
ill-scoped constructor stays stuck even under an update frame, keeping the machine in
lock-step with |evalNeed|.

We conclude with two example traces.
The first evaluates $\Let{i}{\Lam{x}{x}}{i~i}$, which we evaluated by-name in
\Cref{sec:walkthrough}:
\begin{align} \label{ex:trace}
  &\arraycolsep3pt
  \begin{array}{lclclclclc}
  (\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF) & \smallstep[\LetIT] & (i~i, ρ_1, μ, \StopF) & \smallstep[\AppIT] & (i, ρ_1, μ, κ) & \smallstep[\LookupT(i)] \\
  (\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF κ) & \smallstep[\UpdateT] & (\Lam{x}{x}, ρ_1, μ, κ) & \smallstep[\AppET] & (x, ρ_2, μ, \StopF) & \smallstep[\LookupT(i)] \\
  (\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF \StopF) & \smallstep[\UpdateT] & (\Lam{x}{x}, ρ_1, μ, \StopF)
  \end{array} \\ \notag
  &\qquad \text{where} \begin{array}{llll}
    κ = \ApplyF(\pa_1) \pushF \StopF, & ρ_1 = [i ↦ \pa_1], & ρ_2 = [i ↦ \pa_1, x ↦ \pa_1], & μ = [\pa_1 ↦ (i, ρ_1,\Lam{x}{x})] \\
  \end{array} \notag
\end{align}
The last $\LookupT(i)$ transition exemplifies that the lambda-bound variable in
control differs from the let-bound variable used to identify the heap entry.

The second evaluates $\pe \triangleq \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$, the
memoisation example of \Cref{sec:walkthrough-need}:
\begin{align} \label{ex:trace2}
  &\begin{array}{l}
  (\pe, [], [], \StopF)
  \smallstep[\LetIT]
  (i~i, ρ_1, μ_1, \StopF)
  \smallstep[\AppIT]
  (i, ρ_1, μ_1, κ_1)
  \smallstep[\LookupT(i)]
  ((\Lam{y}{\Lam{x}{x}})~i, ρ_1, μ_1, κ_2)
  \\
  \smallstep[\AppIT]
  (\Lam{y}{\Lam{x}{x}}, ρ_1, μ_1, \ApplyF(\pa_1) \pushF κ_2)
  \smallstep[\AppET]
  (\Lam{x}{x}, ρ_2, μ_1, κ_2)
  \smallstep[\UpdateT]
  (\Lam{x}{x}, ρ_2, μ_2, κ_1)
  \\
  \smallstep[\AppET]
  (x, ρ_3, μ_2, \StopF)
  \smallstep[\LookupT(i)]
  (\Lam{x}{x}, ρ_2, μ_2, \UpdateF(\pa_1) \pushF \StopF)
  \smallstep[\UpdateT]
  (\Lam{x}{x}, ρ_2, μ_2, \StopF)
  \end{array} \\ \notag
  &\qquad\text{where } \arraycolsep1pt \begin{array}{ll}
    ρ_1 = [i ↦ \pa_1], & μ_1 = [\pa_1 ↦ (i, ρ_1, (\Lam{y}{\Lam{x}{x}})~i)], ρ_3 = [i ↦ \pa_1, y ↦ \pa_1, x ↦ \pa_1] \\
    ρ_2 = [i ↦ \pa_1, y ↦ \pa_1], & μ_2 = [\pa_1 ↦ (i,ρ_2,\Lam{x}{x})], κ_1 = \ApplyF(\pa_1) \pushF \StopF, κ_2 = \UpdateF (\pa_1) \pushF κ_1
  \end{array} \notag
\end{align}

\subsection{Bisimulation of |evalNeed2| and the Lazy Krivine machine}
\label{sec:adequacy}

\begin{figure}
\[\ruleform{\begin{array}{c}
  α_\Events : \States \to |Event|
  \qquad
  α_\Environments : \Environments \times \Heaps \to (|Name :-> DNeed|)
  \qquad
  α_\Heaps : \Heaps \to |HeapNeed|
  \\
  α_{\STraces} : \STraces \times \Continuations \to |T (ValueNeed, HeapNeed)|
  \qquad
  α_{\Values} : \States \times \Continuations \to |ValueNeed|
\end{array}}\]
\arraycolsep=2pt
\[\begin{array}{lcl}
  α_\Events(σ) & = & \begin{cases}
    |Let1| & \text{if }σ = (\Let{\px}{\wild}{\wild},\wild,\wild,\wild) \\
    |App1| & \text{if }σ = (\pe~\px,\wild,\wild,\wild) \\
    |Case1| & \text{if }σ = (\Case{\wild}{\wild},\wild,\wild, \wild)\\
    |Look y| & \text{if }σ = (\px,ρ,μ,\wild), μ(ρ(\px)) = (\py,\wild,\wild) \\
    |App2| & \text{if }σ = (\Lam{\wild}{\wild},\wild,\wild,\ApplyF(\wild) \pushF \wild) \\
    |Case2| & \text{if }σ = (K~\wild, \wild, \wild, \SelF(\wild,\wild) \pushF \wild) \\
    |Upd| & \text{if }σ = (\pv,\wild,\wild,\UpdateF(\wild) \pushF \wild) \\
  \end{cases} \\
  \\[-0.75em]
  α_\Environments([\many{\px ↦ \pa}], μ) & = & [\many{|x| ↦ |Step (Look y) (fetch a)| \mid μ(\pa) = (\py,\wild,\wild)}] \\
  \\[-0.75em]
  α_\Heaps([\many{\pa ↦ (\wild,ρ,\pe)}]) & = & [\many{|a| ↦ |memo a (eval e (αEnv ρ μ))|}] \\
  \\[-0.75em]
  α_\Values(σ,κ_0) & = & \begin{cases}
    |Fun (\d -> Step App2 (eval e (ext (αEnv ρ μ) x d)))| & \text{if } σ = (\Lam{\px}{\pe},ρ,μ,κ_0) \\
    |Con k (map (αEnv ρ μ !) xs)|                         & \text{if } σ = (K~\overline{\px},ρ,μ,κ_0) \\
    |Stuck|                                               & \text{otherwise} \\
  \end{cases} \\
  \\[-0.75em]
  α_{\STraces}((σ_i)_{i∈\overline{n}},κ_0) & = & \begin{cases}
    |Step ({-" α_\Events(σ_0) "-}) (idiom (αSTraces (lktrace, κ_0)))| & \text{if }n > 0 \\
    |Ret ({-" α_\Values(σ_0,κ_0) "-}, αHeap μ)| & \text{where }(\wild,\wild, μ, \wild) = σ_0
  \end{cases}
\end{array}\]
\vspace{-1em}
\caption{Abstraction function $α_{\STraces}$ from LK machine to |evalNeed2|}
  \label{fig:eval-correctness}
\end{figure}

For proving |evalNeed2| bisimilar to the Lazy Krivine machine
(\Cref{fig:lk-semantics}), we give an abstraction function $α_{\STraces}$
from LK machine traces $\STraces$ to denotational traces |T|, with their |Event|s, such that
\[
  α_{\STraces}(\init(\pe) \smallstep ..., \StopF) = |evalNeed e emp emp|,
\]
where $\init(\pe) \smallstep ...$ denotes the \emph{maximal} (\ie longest
possible) LK trace evaluating the closed expression $\pe$.
For example, for the LK trace \labelcref{ex:trace2}, $α_{\STraces}$ produces
the trace in \Cref{fig:by-need-trace}.

In fact, $α_{\STraces}$ commutes with evaluation not only at the initial configuration but
at every one, giving a bisimulation between |evalNeed2| and the machine.

\begin{theorem}[Bisimulation]
  \label{thm:need-adequacy-bisimulation}
  For every well-addressed configuration $σ = (\pe,ρ,μ,κ)$,
  \[
    α_{\STraces}(σ \smallstep ..., κ) = |evalNeed e (αEnv ρ μ) (αHeap μ)|,
  \]
  where $σ \smallstep ...$ is the maximal LK trace from $σ$.
  In particular, for a closed $\pe$ the denotational trace |evalNeed e emp emp| and the
  maximal LK trace $\init(\pe) \smallstep ...$ have equal length, and every
  |ev :: Event| in |evalNeed e emp emp = many (Step ev ^^ ...)| names the transition rule
  taken at the corresponding LK step.
\end{theorem}
\begin{proofsketch}
  By Löb induction over $σ$.
  Equal length and matching events for closed programs follow because $α_{\STraces}$
  preserves both.
  Mechanised in Lean (\Cref{sec:mechanisation}).
\end{proofsketch}

\begin{corollary}[Adequacy]
  \label{cor:need-adequacy}
  For a closed expression $\pe$, |evalNeed e emp emp| is faithful to the machine's
  termination behaviour: it is stuck, diverging, or balanced~\citep{Sestoft:97} exactly
  when $\init(\pe) \smallstep ...$ is.
\end{corollary}
\begin{proof}
  Immediate from \Cref{thm:need-adequacy-bisimulation}: matching traces exhibit the same
  termination behaviour.
\end{proof}

This bisimulation is the congruence of the interpreter with the machine, and it involves
no analysis.
A conventional soundness proof instead relates the machine to the analysis directly,
threading the analysis through a logical relation over configurations, so establishing
its congruence is laborious and re-established for each analysis.
Here the operational congruence is discharged once; every analysis then relates to the
interpreter alone (\Cref{sec:soundness}).

\subsection{Totality of |evalName| and |evalNeed2|}
\label{sec:totality}

\begin{theorem}[Totality]
\label{thm:totality}
The interpreters |evalName e ρ| and |evalNeed e ρ μ| are defined for every
|e|, |ρ|, |μ|.
\end{theorem}
\begin{proofsketch}
In the Supplement, we implement the generic interpreter |eval| and its
instances at |DName| and |DNeed| in Lean, using guarded recursion~\citep{Jung:18}
to define the productive, coinductive traces.
Since Lean is a total type theory, |evalName| and |evalNeed2| are total as well;
see \Cref{sec:mechanisation} for a description of the mechanisation.
\end{proofsketch}



