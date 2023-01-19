\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Constructors} &     K & ∈ & \Con &      & \\
  \text{Variables}    & x,y,z & ∈ & \Var &      & \\
  \text{Expressions}  &     e & ∈ & \Exp & ::=  & x \mid \Lam{x}{e} \mid e~x \mid \Let{x}{e_1}{e_2} \\
  \\
  \text{Actions} & a & ∈ & \Actions & ::=  & \ValA(\mathbb{V}) \mid \AppA \mid \BetaA \mid \LookupA \mid \BindA \\
  \text{Finite Traces} & π & ∈ & \Traces^+ & ::=  & \lbl \mid \lbl \act{a} π  \\

  \text{Values}       &       &   & \Values & ::= & \FunV(\AbsD \to \AbsD) \\
  \\
  \text{Limit of a set of traces} & && \lim \mathcal{T} & = & \{ π \mid ∀n∈\mathbb{N}. π[0..n] ∈ \mathcal{T} \} \\
  \\
  \text{Infinite Traces} & && \Traces^{\infty} &  ::=  & \lim \Traces^+    \\
  \text{Finite and infinite Traces} & && \Traces^{+\infty} & ::=  & \Traces^+ ∪ \Traces^\infty    \\
  \\
  \text{Domain of prefix traces} & && \PrefD & = & \Traces^+ \to \poset{\Traces^+} \\
  \text{Domain of maximal traces} & && \MaxD & = & \Traces^+ \to \Traces^{+\infty} \\
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
  \multicolumn{1}{c}{ \ruleform{ π_1 \concat π_2 = π_3 } } \\
  \\[-0.5em]
  π_1 \concat π_2 = \begin{cases}
    π_1              & \text{if $π_1$ infinite} \\
    undefined        & \text{if $π_1$ finite and $dst(π_1) \not= src(π_2)$} \\
    \lbl             & π_1 = π_2 = \lbl \\
    π_1' \act{a} π_2 &  π_1 = π_1' \act{a} \lbl \\
    π_1 \act{a} π_2' &  π_2 = \lbl \act{a} π_2' \\
  \end{cases} \\
  \\
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
   \lbln{1} & \act{\BindA} \lbln{5} \act{\AppA} \lbln{6} \act{\AppA} \lbln{7} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3} \\
            & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}
\end{array}
\]

\begin{figure}
\[\begin{array}{c}
 \begin{array}{lrcl}
 \end{array} \\
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
      \text{let} & f = d ↦ step(\seminf{e}_{ρ[x↦d]},\BetaA,\mathsf{at}[e]) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppA} π_e \concat f(ρ(x))(π_i \act{\AppA} π_e) & \text{if $π_e = \wild \act{\ValA(\FunV(f))} \wild$}  \\
                     \lbl \act{\AppA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \seminf{e_1}_{ρ'}]) \\
      \text{in}  & step(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{array} \\
  \\
 \end{array} \\
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
  & \text{and } f = d ↦ step(\sempref{\slbln{3}y}_{ρ[y↦d]},\BetaA,\lbln{3}) \\
  & \text{Evaluate }\slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)} \\
  & \\
  & \seminf{\slbln{1}\Let{x}{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}}_\bot(\lbln{1}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \seminf{\slbln{5}(\slbln{6}(\slbln{7}x~x)~x)}_{ρ_x}(\lbln{1} \act{\BindA} \lbln{5}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppA} \seminf{\slbln{6}(\slbln{7}x~x)}_{ρ_x}(\lbln{1} \act{\BindA} \lbln{5} \act{\AppA} \lbln{6}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppA} \lbln{6} \act{\AppA} \seminf{\slbln{7}x}_{ρ_x}(\overbrace{\lbln{1} \act{\BindA} \lbln{5} \act{\AppA} \lbln{6} \act{\AppA} \lbln{7}}^{π_1}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_1 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_x(x))(π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \seminf{\slbln{3}y}_{ρ_{x,y}}(\overbrace{π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3}}^{π_2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_2 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_x(x))(π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \seminf{\slbln{3}y}_{ρ_{x,y}}(\overbrace{π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3}}^{π_3}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_{ρ_x}(π_3 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \\
  & \\[-0.9em]
  & \\
  = \lbln{1} & \act{\BindA} \lbln{5} \act{\AppA} \lbln{6} \act{\AppA} \lbln{7} \\
             & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3} \\
             & \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\BetaA} \lbln{3} \\
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
    {   ρ' = \lfp(λρ'. ρ ⊔ [x ↦ step(\sempref{e_1}_{ρ'},\LookupA,\mathsf{at}[e_2])])
     \\ π_c ∈ step(\sempref{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)}
    {π_c ∈ \sempref{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Lam}]
    {f = d ↦ step(\sempref{e}_{ρ[x↦d]},\BetaA,\mathsf{at}[e])}
    {\lbln{1} \act{\ValA(\FunV(f))} \lbln{2} ∈ \sempref{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i)} \qquad
  \inferrule*[right=$\textsc{App}_1$]
    {π_c ∈ step(\sempref{e}_ρ,\AppA,\mathsf{at}[e])(π_i)}
    {π_c ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=$\textsc{App}_2$]
    {π_e \act{\ValA(\FunV(f))} \lbl_f ∈ \sempref{e}_ρ(π_i \act{\AppA} \mathsf{at}[e]) \quad \balanced{π_e}
    \\ π_f ∈ f(ρ(x))(π_i \act{\AppA} π_e \act{\ValA(\FunV(f))} \lbl_f)}
    {\lbl \act{\AppA} π_e \act{\ValA(\FunV(f))} π_f ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\

  \ruleform{ \balanced{π} } \\
  \inferrule*[right=\textsc{BalVal}]
    {\quad}
    {\balanced{\lbln{1} \act{\ValA(v)} \lbln{2}}}
  \qquad
  \inferrule*[right=\textsc{BalApp}]
    {\balanced{π_1}\quad\balanced{π_2}}
    {\balanced{\lbl \act{\AppA} π_1 \act{\BetaA} π_2}} \\
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
 \begin{array}{lrcl}
  \text{Infinite Traces} & \Traces^{\infty} & ::=  & \lim \Traces^+    \\
  \text{Finite and infinite Traces} & \Traces^{+\infty} & ::=  & \Traces^+ ∪ \Traces^\infty    \\
  \\
  \text{Domain of maximal traces} & \MaxD & = & \Traces^+ \to \Traces^{+\infty} \\
  \\
 \end{array} \\
 \begin{array}{rclcll}
  \multicolumn{6}{c}{ \ruleform{ \wild \concat \wild : \Traces^{+\infty} \to \Traces^{+\infty} \to \Traces^{+\infty} } } \\
  \\[-0.5em]
  \lbl             &\concat& \lbl \act{a} π & = & \lbl \act{a} π \\
  π_1 \act{a} \lbl &\concat& π_2            & = & π_1 \act{a} π_2 & \text{if $src(π_2) = \lbl$} \\
  π_1              &\concat& π_2            & = & π_1             & \text{if $π_1∈\Traces^\infty$} \\
  \\
 \end{array} \\
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
      \text{let} & f = d ↦ step(\sempref{e}_{ρ[x↦d]},\BetaA,\mathsf{at}[e]) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppA} π_e \concat f(ρ(x))(π_i \act{\AppA} π_e) & \text{if $π_e = \wild \act{\ValA(\FunV(f))} \wild$}  \\
                     \lbl \act{\AppA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{array} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{array}{ll}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \seminf{e_1}_{ρ'}]) \\
      \text{in}  & step(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{array} \\
  \\
 \end{array} \\
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

