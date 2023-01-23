\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}    & x,y,z & ∈ & \Var &      & \\
  \text{Expressions}  &     e & ∈ & \Exp & ::=  & x \mid \Lam{x}{e} \mid e~x \mid \Let{x}{e_1}{e_2} \\
  \\
  \text{Actions} & a & ∈ & \Actions & ::=  & \ValA(\mathbb{V}) \mid \AppIA \mid \AppEA \mid \LookupA \mid \BindA \\
  \text{Finite Traces} & π & ∈ & \Traces^+ & ::=  & \lbl \mid \lbl \act{a} π  \\

  \text{Values}          &     v & ∈ & \Values & ::= & \FunV(\AbsD \to \AbsD) \\
  \text{Semantic Domain} &     d & ∈ & \AbsD & & \text{Specified as needed} \\
  \\
  \text{Limit of a set of traces} & && \lim \mathcal{T} & = & \{ π \mid ∀n∈\mathbb{N}. π[0..n] ∈ \mathcal{T} \} \\
  \\
  \text{Infinite Traces} & && \Traces^{\infty} &  ::=  & \lim \Traces^+    \\
  \text{Finite and infinite Traces} & && \Traces^{+\infty} & ::=  & \Traces^+ ∪ \Traces^\infty    \\
  \\
  \text{Domain of prefix traces} & && \PrefD & = & \Traces^+ \to \poset{\Traces^+} \\
  \text{Domain of deterministic maximal traces} & && \MaxD & = & \Traces^+ \to \Traces^{+\infty} \\
  \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src(π) = \lbl \qquad dst(π) = \lbl } } \\
  \\[-0.5em]
  src(\lbl)           & = & \lbl \\
  src(\lbl \act{a} π) & = & \lbl \\
  \\[-0.5em]
  dst(\lbl)           & = & \lbl \\
  dst(\lbl \act{a} π) & = & dst(π) \\
  \\
 \end{array} \qquad
 \begin{array}{c}
  \ruleform{ π_1 \concat π_2 = π_3 } \\
  \\[-0.5em]
  π_1 \concat π_2 = \begin{cases}
    π_1              & \text{if $π_1$ infinite} \\
    undefined        & \text{if $π_1$ finite and $dst(π_1) \not= src(π_2)$} \\
    \lbl             & π_1 = π_2 = \lbl \\
    π_1' \act{a} π_2 &  π_1 = π_1' \act{a} \lbl \\
    π_1 \act{a} π_2' &  π_2 = \lbl \act{a} π_2' \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{c}
 \ruleform{ \getval{π}{v} }
 \\[-0.5em]
 \inferrule*[right=\textsc{ValVal}]
   {\quad}
   {\getval{π \act{\ValA(v)} \lbl}{v}}
 \\[-0.5em]
 \end{array} \\
\end{array}\]
\caption{Syntax of expressions, labels and traces}
  \label{fig:syntax}
\end{figure}

Labelled expression:
\begin{gather*}
   \Let{x}{\Lam{y}{y}}{x~x~x)} \\
   \slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}
\end{gather*}

Trace of the expression:
\[
\begin{array}{r@@{}l}
   \multicolumn{2}{c}{\slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}} \\
   \\
   \lbln{1} & \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \lbln{7} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}
\end{array}
\]

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  step(S,a,\lbl)(π_i)   & = & dst(π_i) \act{a} S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & dst(π_i) \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & f = d ↦ step(\seminf{e}_{ρ[x↦d]},\AppEA,\mathsf{at}[e]) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $\getval{π_e}{\FunV(f)}$}  \\
                     \lbl \act{\AppIA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ step(\seminf{e_1}_{ρ'},\LookupA,\mathsf{at}[e_1])]) \\
      \text{in}  & step(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{array} \\
  \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \mathbb{P}^* & = & \{ C \in \poset{\Traces^+} \mid C \text{ is a prefix-closed chain of traces} \} \\
  \\[-0.5em]
  \multicolumn{3}{c}{ \ruleform{ α^{*} : \Traces^{+\infty} \to \mathbb{P}^* \qquad γ^{*} : \mathbb{P}^* \to \Traces^{+\infty} } } \\
  \\[-0.5em]
  α^{*}(π) & = & \{ π' \mid π' \text{ is a prefix of } π \} \\
  γ^{*}(C) & = & \Lub C \qquad \text{where $\lub$ is defined on the prefix-closed chain $C$} \\
  \Traces^{+\infty} & \GaloiS{α^{*}}{γ^{*}} & \mathbb{P}^* \\
  \Traces^+ \to \Traces^{+\infty} & \GaloiS{\dot{α}^{*}}{\dot{γ}^{*}} & \Traces^+ \to \mathbb{P}^* \\
  \seminf{e} & \GaloiS{\ddot{α}^{*}}{\ddot{γ}^{*}} & \sempref{e} \\
  \\
 \end{array}
\end{array}\]
\caption{Structural Maximal Trace Semantics}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[
\begin{array}{ll}
  & \text{Let } ρ_x = \lfp(λρ. [x ↦ step(\seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_ρ,\LookupA,\lbln{2}]) \\
  & \text{and } ρ_{x,y} = ρ_x[y ↦ ρ_1(x)] \\
  & \text{and } f = d ↦ step(\seminf{\slbln{3}y}_{ρ[y↦d]},\AppEA,\lbln{3}) \\
  & \text{Evaluate }\slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)} \\
  & \\
  & \seminf{\slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}}_\bot(\lbln{1}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \seminf{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}_{ρ_x}(\lbln{1} \act{\BindA} \lbln{5}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \seminf{\slbln{6}(\slbln{7}x~x)}_{ρ_x}(\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \seminf{\slbln{7}x}_{ρ_x}(\overbrace{\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \lbln{7}}^{π_1}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_1 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_x(x))(π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \seminf{\slbln{3}y}_{ρ_{x,y}}(\overbrace{π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_2 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_x(x))(π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \seminf{\slbln{3}y}_{ρ_{x,y}}(\overbrace{π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_3}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_3 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \\
  & \\[-0.9em]
  & \\
  = \lbln{1} & \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \lbln{7} \\
             & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3} \\
             & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3} \\
             & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}
\end{array}
\]
\caption{Evalation of $\seminf{\wild}$}
\end{figure}

\begin{figure}
\[\begin{array}{c}
  \ruleform{ \sempref{\wild} \colon \Exp → (\Var → \PrefD) → \PrefD } \\
  \\[-0.5em]
  step(S,a,\lbl)(π_i)   = \{\; dst(π_i) \act{a} π_o \mid π_o ∈ S(π_i \act{a} \lbl) \;\} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Bot}]
    {\quad}
    {dst(π) ∈ \sempref{\slbl e}_ρ(π)}
  \qquad
  \inferrule*[right=\textsc{Var}]
    {π_c ∈ ρ(x)(π_i)}
    {π_c ∈ \sempref{\slbl x}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Let}]
    {   ρ' = \lfp(λρ'. ρ ⊔ [x ↦ step(\sempref{e_1}_{ρ'},\LookupA,\mathsf{at}[e_1])])
     \\ π_c ∈ step(\sempref{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)}
    {π_c ∈ \sempref{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Lam}]
    {f = d ↦ step(\sempref{e}_{ρ[x↦d]},\AppEA,\mathsf{at}[e])}
    {\lbln{1} \act{\ValA(\FunV(f))} \lbln{2} ∈ \sempref{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i)} \qquad
  \inferrule*[right=$\textsc{App}_1$]
    {π_c ∈ step(\sempref{e}_ρ,\AppIA,\mathsf{at}[e])(π_i)}
    {π_c ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=$\textsc{App}_2$]
    {\balanced{π_e} \quad π_e ∈ step(\sempref{e}_ρ,\AppIA,\mathsf{at}[e])(π_i)
    \\\\ \getval{π_e}{\FunV(f)} \qquad π_f ∈ f(ρ(x))(π_i \act{\AppIA} π_e)}
    {\lbl \act{\AppIA} π_e \concat π_f ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\

  \ruleform{ \balanced{π} } \\
  \inferrule*[right=\textsc{BalVal}]
    {\quad}
    {\balanced{\lbln{1} \act{\ValA(v)} \lbln{2}}}
  \qquad
  \inferrule*[right=\textsc{BalApp}]
    {\balanced{π_1}\quad\balanced{π_2}}
    {\balanced{\lbl \act{\AppIA} π_1 \act{\AppEA} π_2}} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalVar}]
    {\balanced{π}}
    {\balanced{\lbl \act{\LookupA} π}}
  \qquad
  \inferrule*[right=\textsc{BalLet}]
    {\balanced{π}}
    {\balanced{\lbl \act{\BindA} π}} \\
  \\[-0.5em]
  \\[-0.5em]
\end{array}\]
\caption{Structural Deductive Stateless Prefix Trace Semantics for call-by-name lambda calculus}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Constructors} &     K & ∈ & \Con     & \subseteq & \Nat \\
  \text{Expressions}  &     e & ∈ & \Exp     & ::=       & \ldots \mid K~\many{x} \mid \Case{e}{\Sel} \\
  \\
  \text{Actions}      &     a & ∈ & \Actions & ::=       & \ldots \mid \CaseIA \mid \CaseEA \\
  \text{Values}       &     v & ∈ & \Values  & ::=       & \ldots \mid \ConV(\Sigma_{K ∈ \Con}(\Pi_{i=1}^{A_K}d_i)) \text{ where $K$ has $A_K$ fields} \\
 \end{array} \\
 \\
  \ruleform{ \balanced{π} } \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalCase}]
    {\balanced{π_1}\quad\balanced{π_2}}
    {\balanced{\lbl \act{\CaseIA} π_1 \act{\CaseEA} π_2}} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  \seminf{\slbln{1}(K~\many{x})\slbln{2}}_ρ(π_i) & = & \lbln{1} \act{\ValA(\ConV(K,\many{ρ(x)}))} \lbln{2} \\
  \\[-0.5em]
  \seminf{\slbl(\Case{e_s}{\Sel})}_ρ(π_i) & = & \begin{cases}
      π_s \concat Rhs(K,\many{d})(π_i \concat π_s) & \text{if $\getval{π_s}{\ConV(K,\many{d})}$}  \\
      π_s & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & step(\seminf{e_s}_ρ, \CaseIA, \mathsf{at}[e_s])(π_i) \\
                       Rhs(K,\many{d}) & = & step(\seminf{e_K}_{ρ[\many{x↦d}]},\CaseEA,\mathsf{at}[e_K]) \\
                     \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Algebraic data types in Structural Maximal Trace Semantics}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Actions}      &     a & ∈ & \Actions & ::=       & \ldots \mid \LookupA(π) \mid \UpdateA(π) \\
 \end{array} \\
 \\
 \begin{array}{ll}
  \begin{array}{c}
   \ruleform{ \getval{π}{v} } \\
   \\[-0.5em]
   \inferrule*[right=\textsc{ValUpd}]
     {\getval{π}{v}}
     {\getval{π \act{\UpdateA(\wild)} \lbl}{v}} \\
  \end{array} &
  \begin{array}{c}
   \ruleform{ \balanced{π} } \\
   \\[-0.5em]
   \inferrule*[right=\textsc{BalVar}]
     {\balanced{π}}
     {\balanced{\lbln{1} \act{\LookupA} π \act{\UpdateA} \lbln{2}}} \\
  \end{array} \\
  \\[-0.5em]
 \end{array} \\
 \begin{array}{c}
  \ruleform{ \balanced{π} } \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalVar}]
    {\balanced{π}}
    {\balanced{\lbln{1} \act{\LookupA} π \act{\UpdateA} \lbln{2}}} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1,π_2. π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  π_r \rightsubtrceq π & = & π_r \subtrceq π \wedge \forall π'. (π' \subtrceq (π_r \concat π_2) \Rightarrow π' = π_r) \\
  \\[-0.5em]
  π_l \leftsubtrceq π & = & π_l \subtrceq π \wedge \forall π'. (π' \subtrceq (π_1 \concat π_l) \Rightarrow π' = π_l) \\
  \\[-0.5em]
  lookup(π_k,π) & = & \begin{cases}
    π_i \act{\LookupA} \lbln{1} \act{\ValA(v)} \lbln{2} \act{\UpdateA(π_k)} \lbln{?} & \text{if $π = π' \act{\UpdateA(π_k)} \wild$ and $rightmatch(π',\lbln{1} \act{\ValA(v)} \lbln{2})$} \\
    lookup(π_k, π')                  & \text{if $π = π' \act{\wild} \wild$} \\
    undefined                        & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  memoised(S,π_k,\lbl)(π_i)   & = & \begin{cases}
    S(π_i) \act{a} \lbl \\
  \end{cases}
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \\ & poststep(step(\seminf{e_1}_{ρ'},\LookupA(π_i),\mathsf{at}[e_1]),\UpdateA(π_i),\mathsf{at}[???])]) \\
      \text{in}  & step(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics for call-by-need}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Configurations}  &     κ & ∈ & \Configurations & ::= & (H,e,S) \\
  \\
  \text{Stacks}       &     S & ∈ & \Stacks  & ::= & \StopF \mid \ApplyF{x} \pushF S \mid \UpdateF{x} \pushF S \\
  \text{Finite Small Traces}       &     σ & ∈ & \STraces  & ::= & κ \mid σ \sstep κ \\
  \text{Domain of small-step transitions} &       &   & \SSD  & = & \Configurations \to (\Values,\STraces) \\
 \end{array} \\
 \\
  \ruleform{ \balanced{π} } \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalCase}]
    {\balanced{π_1}\quad\balanced{π_2}}
    {\balanced{\lbl \act{\CaseIA} π_1 \act{\CaseEA} π_2}} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semss{\wild} \colon \Exp → (\Var → \SSD) → \SSD } } \\
  \\[-0.5em]
  update((H,e,\UpdateF{x} \pushF S)) & = & (H,e,S) \sstep update(H[x↦e],e,S) \\
  update((H,e,S)) & = & (H,e,S) \quad \text{if $S \not= \UpdateF{x} \pushF \wild$} \\
  \\[-0.5em]
  \semss{\slbl x}_ρ    (κ)   & = & ρ(x)(κ) \\
  \\[-0.5em]
  \semss{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ & = & \fn{(H,\Lam{y}{e'},S)}{ \\
    & & (\FunV(\fn{d}{\semss{e}_{ρ[x↦d]}}), update(H,\Lam{y}{e'},S))
    } \\
  \\[-0.5em]
  \semss{\slbl(e~x)}_ρ & = & \fn{(H_1,e_1~x_1,S_1)}{\\
    & & \begin{array}{ll}
      \text{let} & (v,σ;(H_2,e_2,S_2)) = \semss{e}_ρ(H_1,e_1,\ApplyF{x_1} \pushF S_1) \\
      \text{in}  & \begin{cases}
                     σ;(H_2,e_2,S_2);f(ρ(x))(H_2,e_3[y_3/x_3],S_3) & \text{if $v = \FunV(f)$ and $e_2 = \Lam{y_3}{e_3}$ and $S_2 = \ApplyF{x_3} \pushF S_3$}  \\
                     σ;(H_2,e_2,S_2); & \text{otherwise}  \\
                   \end{cases} \\
    \end{array}
    } \\
  \\[-0.5em]
  \semss{\slbl(\Let{x}{e_1}{e_2})}_ρ& = & \fn{(H,\Let{x'}{e_1'}{e_2'},S)}{\\
    & & \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \fn{(H',y,S')}{\semss{e_1}_{ρ'}(H',H'(y),\UpdateF{y} \pushF S')}]) \\
      \text{in}  & (H,\Let{x'}{e_1'}{e_2'},S);\semss{e_2}_{ρ'}(H[x'↦e_1'],e_2',S)
    \end{array}
    } \\
  \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \mathbb{P}^* & = & \{ C \in \poset{\Traces^+} \mid C \text{ is a prefix-closed chain of traces} \} \\
  \\[-0.5em]
  \multicolumn{3}{c}{ \ruleform{ α^{*} : \Traces^{+\infty} \to \mathbb{P}^* \qquad γ^{*} : \mathbb{P}^* \to \Traces^{+\infty} } } \\
  \\[-0.5em]
  α^{*}(π) & = & \{ π' \mid π' \text{ is a prefix of } π \} \\
  γ^{*}(C) & = & \Lub C \qquad \text{where $\lub$ is defined on the prefix-closed chain $C$} \\
  \Traces^{+\infty} & \GaloiS{α^{*}}{γ^{*}} & \mathbb{P}^* \\
  \Traces^+ \to \Traces^{+\infty} & \GaloiS{\dot{α}^{*}}{\dot{γ}^{*}} & \Traces^+ \to \mathbb{P}^* \\
  \semss{e} & \GaloiS{\ddot{α}^{*}}{\ddot{γ}^{*}} & \sempref{e} \\
  \\
 \end{array}
\end{array}\]
\caption{Structural call-by-need small-step semantics}
  \label{fig:ss-semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Data Type Constructors}  & T & ∈ & \TyCon & \subseteq & \Nat \\
  \text{Types}                   & τ & ∈ & \Type & ::= & τ_1 \ArrowTy τ_2 \mid T \\
  \text{Constructor families}    & φ & ∈ & \multicolumn{3}{l}{\Con \twoheadrightarrow \TyCon} \\
  \text{Constructor field types} & σ & ∈ & \multicolumn{3}{l}{\Con \to \Pi_{i=1}^{A_K} \Type_i} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α_τ : (\Traces^+ \to \poset{\Traces^{+\infty}}) \to \poset{\Type} \qquad γ_τ : \poset{\Type} \to (\Traces^+ \to \poset{\Traces^{+\infty}})} } \\
  \\[-0.5em]
  single(S)   & = & \begin{cases}
    S & S = \{ e \} \\
    \varnothing & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  α_τ(S) & = & \{ α_v(v) \mid \exists π_i π. (π \act{\ValA(v)} \wild) ∈ S(π_i) \wedge \balanced{π} \}  \\
  α_v(\FunV(f)) & = & single(\{ τ_1 \ArrowTy τ_2 \mid τ_2 \in α_τ(f(γ_τ(τ_1))) \})  \\
  α_v(\ConV(K,\many{d})) & = & \{ φ(K) \mid \many{σ(i) \in α_τ(d_i)}^i \}  \\
  \\[-0.5em]
  γ_τ(A)(π_i) & = & \{ π \act{\ValA(v)} \wild \mid \balanced{π} \wedge v ∈ γ_v(A) \}  \\
  γ_v(A) & = &   \{ \ConV(K,\many{d}) \mid φ(K) ∈ A \wedge \many{d_i = γ_τ(σ(i))}^i \} \\
         &   & ∪ \{ \FunV(f) \mid \forall (τ_1 \ArrowTy τ_2) ∈ A. f(γ_τ(τ_1)) \subseteq γ_τ(τ_2)  \}  \\
  \\
 \end{array} \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \poset{\Type}) → \poset{\Type} } } \\
  \\[-0.5em]
  step(S,a,\lbl)(π_i)   & = & dst(π_i) \act{a} S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & \varnothing \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & f = d ↦ step(\seminf{e}_{ρ[x↦d]},\AppEA,\mathsf{at}[e]) \\
      \text{in}  & α_v(\FunV(f)) \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $π_e = \wild \act{\ValA(\FunV(f))} \wild$}  \\
                     \lbl \act{\AppIA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \seminf{e_1}_{ρ'}]) \\
      \text{in}  & step(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{array} \\
  \\
  \seminf{\slbln{1}(K~\many{x})\slbln{2}}_ρ(π_i) & = & \lbln{1} \act{\ValA(\ConV(K,\many{ρ(x)}))} \lbln{2} \\
  \\[-0.5em]
  \seminf{\slbl(\Case{e_s}{\Sel})}_ρ(π_i) & = & \begin{cases}
      π_s \concat Rhs(K,\many{d})(π_i \concat π_s) & \text{if $π_s = \wild \act{\ValA(\ConV(K,\many{d}))} \wild$}  \\
      π_s & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & step(\seminf{e_s}_ρ, \CaseIA, \mathsf{at}[e_s])(π_i) \\
                       Rhs(K,\many{d}) & = & step(\seminf{e_K}_{ρ[\many{x↦d}]},\CaseEA,\mathsf{at}[e_K]) \\
                     \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Simple type inference as abstract interpretation}
  \label{fig:semantics}
\end{figure}

