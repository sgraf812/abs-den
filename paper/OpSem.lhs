%if style == newcode
> module OpSem where
%endif

\section{Reference Semantics: Lazy Krivine Machine}
\label{sec:op-sem}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep3pt
 \begin{array}{rrclcl}
  \text{Addresses}     & \pa & ∈ & \Addresses     & \simeq & ℕ
  \\
  \text{States}        & σ   & ∈ & \States        & =    & \Exp \times \Environments \times \Heaps \times \Continuations
  \\
  \text{Environments}  & ρ   & ∈ & \Environments  & =    & \Var \pfun \Addresses
  \\
  \text{Heaps}         & μ   & ∈ & \Heaps         & =    & \Addresses \pfun \Var \times \Environments \times \Exp
  \\
  \text{Continuations} & κ   & ∈ & \Continuations & ::=  & \StopF \mid \ApplyF(\pa) \pushF κ \mid \UpdateF(\pa) \pushF κ \\
                       &     &   &                & \mid & \SelF(ρ,\SelArity) \pushF κ \\
 \end{array} \\
 \\[-0.5em]
\end{array}\]
\[ \ruleform{ σ_1 \smallstep σ_2 } \]
\[\begin{array}{c}
  \inferrule*[left=$\LetIT$]
    {\pa \not∈ \dom(μ) \\ ρ' = ρ[\px↦\pa]}
    {(\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) \smallstep (\pe_2,ρ',μ[\pa↦(\px,ρ',\pe_1)], κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\AppIT$]
    {\pa = ρ(\px)}
    {(\pe~\px,ρ,μ,κ) \smallstep (\pe,ρ,μ,\ApplyF(\pa) \pushF κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\AppET$]
    { \\ }
    {(\Lam{\px}{\pe},ρ,μ, \ApplyF(\pa) \pushF κ) \smallstep (\pe,ρ[\px ↦ \pa],μ,κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\LookupT(\py)$]
    {\pa = ρ(\px) \\ (\py,ρ',\pe) = μ(\pa)}
    {(\px, ρ, μ, κ) \smallstep (\pe, ρ', μ, \UpdateF(\pa) \pushF κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\UpdateT$]
    {μ(\pa) = (\px,\wild,\wild)}
    {(\pv, ρ, μ, \UpdateF(\pa) \pushF κ) \smallstep (\pv, ρ, μ[\pa ↦ (\px,ρ,\pv)], κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\CaseIT$]
    { \\ }
    {(\Case{\pe_s}{\Sel[r]},ρ,μ,κ) \smallstep (\pe_s,ρ,μ,\SelF(ρ,\Sel[r]) \pushF κ)}
  \\ \\[-0.5em]
  \inferrule*[left=$\CaseET$]
    {K_i = K',\ \many{\pa = ρ(\py)}}
    {(K'~\many{y},ρ,μ, \SelF(ρ',\Sel) \pushF κ) \smallstep (\pe_i,ρ'[\many{\px_i ↦ \pa}],μ,κ)}
\end{array}\]
\caption{Lazy Krivine transition semantics $\smallstep$}
  \label{fig:lk-semantics}
\end{figure}

Before I introduce my novel denotational interpreters, let us
recall the semantic ground truth of this work and others \citep{Sergey:14,
Breitner:16}: The Mark II machine of \citet{Sestoft:97} given in
\Cref{fig:lk-semantics}, a small-step operational semantics.
It is a Lazy Krivine (LK) machine implementing call-by-need.
(A close sibling for call-by-value would be a CESK machine \citep{Felleisen:87}.)
A reasonable call-by-name semantics can be recovered by removing the $\UpdateT$
rule and the pushing of update frames in $\LookupT$.
%Furthermore, we will ignore $\CaseIT$ and $\CaseET$ in this section because we
%do not consider data types for now.

The configurations $σ$ in this transition system resemble abstract machine
states, consisting of a control expression $\pe$, an environment $ρ$ mapping
lexically-scoped variables to their current heap address, a heap $μ$ listing a
closure for each address, and a stack of continuation frames $κ$.
There is one harmless non-standard extension: For $\LookupT$
transitions, I take note of the let-bound variable $\py$ which allocated the
heap binding that the machine is about to look up. The association from address
to let-bound variable is maintained in the first component of a heap entry
triple and requires slight adjustments of the $\LetIT$, $\LookupT$ and
$\UpdateT$ rules.

The notation $f ∈ A \pfun B$ used in the definition of $ρ$ and $μ$ denotes a
finite map from $A$ to $B$, a partial function where the domain $\dom(f)$ is
finite and $\rng(f)$ denotes its range.
The literal notation $[a_1↦b_1,...,a_n↦b_n]$ denotes a finite map with domain
$\{a_1,...,a_n\}$ that maps $a_i$ to $b_i$. Function update $f[a ↦ b]$
maps $a$ to $b$ and is otherwise equal to $f$.

The initial machine state for a closed expression $\pe$ is given by the
injection function $\init(\pe) = (\pe,[],[],\StopF)$ and
the final machine states are of the form $(\pv,\wild,\wild,\StopF)$.
I bake into $σ∈\States$ the simplifying invariant of \emph{well-addressedness}:
Any address $\pa$ occurring in $ρ$, $κ$ or the range of $μ$ must be an element of
$\dom(μ)$.
It is easy to see that the transition system maintains this invariant and that
it is still possible to observe scoping errors which are thus confined to lookup
in $ρ$.

We conclude with two example traces. The first one evaluates $\Let{i}{\Lam{x}{x}}{i~i}$:
\begin{align} \label{ex:trace}
  \arraycolsep3pt
  \begin{array}{cll}
  \multicolumn{2}{l}{(\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF)} & \text{where} \\
    \quad \smallstep[\LetIT] & (i~i, ρ_1, μ, \StopF) & \quad ρ_1 = [i ↦ \pa_1] \\
    \quad \smallstep[\AppIT] & (i, ρ_1, μ, κ)        & \quad μ = [\pa_1 ↦ (i, ρ_1,\Lam{x}{x})] \\
    \quad \smallstep[\LookupT(i)] & \highlight{(\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF κ)} & \quad κ = \ApplyF(\pa_1) \pushF \StopF \\
    \quad \highlight{\smallstep[\UpdateT]} & (\Lam{x}{x}, ρ_1, μ, κ) \\
    \quad \smallstep[\AppET] & (x, ρ_2, μ, \StopF) & \quad ρ_2 = [i ↦ \pa_1, x ↦ \pa_1] \\
    \quad \smallstep[\LookupT(i)] & \highlight{(\Lam{x}{x}, ρ_1, μ, \UpdateF(\pa_1) \pushF \StopF)} \\
    \quad \highlight{\smallstep[\UpdateT]} & (\Lam{x}{x}, ρ_1, μ, \StopF)
  \end{array}
\end{align}
The corresponding by-name trace simply omits the highlighted update steps.
The last $\LookupT(i)$ transition exemplifies that the lambda-bound variable in
control differs from the let-bound variable used to identify the heap entry.

The second example evaluates $\pe \triangleq \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$,
demonstrating recursive $\mathbf{let}$ semantics and memoisation of $i$:
\begin{align} \label{ex:trace2}
  \arraycolsep3pt
  \begin{array}{clll}
  \multicolumn{2}{l}{(\pe, [], [], \StopF)}                                                  & \text{where} \\
    \quad \smallstep[\LetIT]      & (i~i, ρ_1, μ_1, \StopF)                                  &  \quad ρ_1 = [i ↦ \pa_1] \\
    \quad \smallstep[\AppIT]      & (i, ρ_1, μ_1, \ApplyF(\pa_1) \pushF \StopF)              &  \quad μ_1 = [\pa_1 ↦ (i, ρ_1, (\Lam{y}{\Lam{x}{x}})~i)] \\
    \quad \smallstep[\LookupT(i)] & ((\Lam{y}{\Lam{x}{x}})~i, ρ_1, μ_1, κ)                   &  \quad κ = \UpdateF (\pa_1) \pushF \ApplyF(\pa_1) \pushF \StopF \\
    \quad \smallstep[\AppIT]      & (\Lam{y}{\Lam{x}{x}}, ρ_1, μ_1, \ApplyF(\pa_1) \pushF κ) \\
    \quad \smallstep[\AppET]      & (\Lam{x}{x}, ρ_2, μ_1, κ)                                &  \quad ρ_2 = [i ↦ \pa_1, y ↦ \pa_1] \\
    \quad \smallstep[\UpdateT]    & (\Lam{x}{x}, ρ_2, μ_2, \ApplyF(\pa_1) \pushF \StopF)     &  \quad μ_2 = [\pa_1 ↦ (i,ρ_2,\Lam{x}{x})] \\
    \quad \smallstep[\AppET]      & (x, ρ_3, μ_2, \StopF)                                    &  \quad ρ_3 = [i ↦ \pa_1, y ↦ \pa_1, x ↦ \pa_1] \\
    \quad \smallstep[\LookupT(i)] & (\Lam{x}{x}, ρ_2, μ_2, \UpdateF(\pa_1) \pushF \StopF) \\
    \quad \smallstep[\UpdateT]    & (\Lam{x}{x}, ρ_2, μ_2, \StopF)
  \end{array}
\end{align}
