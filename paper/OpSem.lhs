%if style == newcode
> module OpSem where
%endif

\section{Reference Semantics: Lazy Krivine Machine}
\label{sec:op-sem}

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

Before we get to introduce our novel denotational interpreaters, let us
recall the semantic ground truth of this work and others \citep{Sergey:14,
Breitner:16}: The Mark II machine of \citet{Sestoft:97} given in
\Cref{fig:lk-semantics}, a small-step operational semantics.
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
We conclude with the following example trace evaluating $\Let{i}{\Lam{x}{x}}{i~i}$:
\[\begin{array}{c}
  \arraycolsep2pt
  \begin{array}{clclclclcl}
             & (\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF) & \smallstep[\LetIT] & (i~i, ρ_1, μ, \StopF)
             & \smallstep[\AppIT] & (i, ρ_1, μ, κ)
             & \smallstep[\LookupT] & \highlight{(\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF κ)}
  \\ \highlight{\smallstep[\UpdateT]} & (\Lam{x}{x}, ρ_1, μ, κ) & \smallstep[\AppET] & (x, ρ_2, μ, \StopF) & \smallstep[\LookupT] & \highlight{(\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF \StopF)} & \highlight{\smallstep[\UpdateT]} & (\Lam{x}{x}, ρ_1, μ, \StopF)
  \end{array} \\
  \\[-0.5em]
  \quad \text{where} \quad \begin{array}{lll}
    κ = \ApplyF(\pa_1) \pushF \StopF, ρ_1 = [i ↦ \pa_1] & ρ_2 = [i ↦ \pa_1, x ↦ \pa_1] & μ = [\pa_1 ↦ (ρ_1,\Lam{x}{x})]. \\
  \end{array}
\end{array}\]
The corresponding by-name trace simply omits the highlighted parts.
