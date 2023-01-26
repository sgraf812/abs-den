\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}    & x,y,z & ∈ & \Var &      & \\
  \text{Expressions}  &     e & ∈ & \Exp & ::=  & x \mid \Lam{x}{e} \mid e~x \mid \Let{x}{e_1}{e_2} \\
  \\
  \text{Actions} & a & ∈ & \Actions & ::=  & \AppIA \mid \AppEA \mid \LookupA \mid \BindA \\
  \text{Finite Traces} & π & ∈ & \Traces^+ & ::=  & \lbl \mid \lbl \act{a} π  \\

  \text{Semantic Domain} &     d & ∈ & \AbsD & & \text{Specified as needed} \\
  \text{Values}          &     v & ∈ & \Values & ::= & \FunV(\AbsD \to \AbsD) \mid \bot_\Values \\
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
 \begin{array}{ll}
  \begin{array}{c}
  \ruleform{ \getval{π}{v} }
  \\[-0.5em]
  \inferrule*[right=\textsc{ValVal}]
    {\quad}
    {\getval{π \act{\ValA(v)} \lbl}{v}}
  \\[-0.5em]
  \end{array} &
  \begin{array}{c}
  \ruleform{ \balanced{π} } \\
  \\[-0.5em]
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
  \end{array} \\
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
  \bot(π_i)   & = & dst(π_i) \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i)   & = & dst(π_i) \act{a} S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & \bot(π_i) \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\mathsf{at}[e],\seminf{e}_{ρ[x↦d]}) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & \lbl \act{\AppIA} π_e \concat \begin{cases}
                     f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $\getval{π_e}{\FunV(f)}$}  \\
                     \bot(π_i \act{\AppIA} π_e) & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ cons(\LookupA,\mathsf{at}[e_1],\seminf{e_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\mathsf{at}[e_2],\seminf{e_2}_{ρ'})(π_i)
    \end{letarray} \\
  \\[-0.5em]
  \text{Call-by-need:} \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  lookup(π_k,π_i) & = & \begin{cases}
    dst(π_b) \act{\ValA(v)} \lbln{2} & \begin{array}{@@{}l@@{}}\text{if $\lbln{1} \act{\LookupA(π_k)} π_b \act{\ValA(v)} \lbln{2} \subtrceq π_i$} \\[-0.4em]
                                                       \text{and $\balanced{π_b \act{\ValA(v)} \lbln{2}}$} \end{array} \\
    \square                      & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  memo(π_k,\lbl,S)(π_i)   & = & \begin{cases}
    dst(π_i) \act{\LookupA(π_k)} π_v & π_v = lookup(π_k,π_i) \\
    dst(π_i) \act{\LookupA(π_k)} S(π_i \act{\LookupA(π_k)} \lbl) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ memo(π_i,\mathsf{at}[e_1],\seminf{e_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\mathsf{at}[e_2],\seminf{e_2}_{ρ'})(π_i)
    \end{letarray} \\
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics With Crazy Traces}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
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
\caption{Prefix Trace Abstraction}
  \label{fig:semantics}
\end{figure}

\newcommand{\second}{\ensuremath{\mathbin{@<2>@}}}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  \bot_\MaxD(π_i)   & = & (\bot_\Values,dst(π_i)) \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  f \second (a,b)  & = & (a, f a) \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i)   & = & (dst(π_i) \act{a} {}) \second S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & \bot(π_i) \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\mathsf{at}[e],\seminf{e}_{ρ[x↦d]}) \\
      \text{in}  & (\FunV(f), \lbln{1} \act{\ValA} \lbln{2}) \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & (v_e, π_e) = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & (\lbl \act{\AppIA} π_e \concat {}) \second \begin{cases}
                     f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $v_e = \FunV(f)$}  \\
                     \bot(π_i \act{\AppIA} π_e) & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ cons(\LookupA,\mathsf{at}[e_1],\seminf{e_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\mathsf{at}[e_2],\seminf{e_2}_{ρ'})(π_i)
    \end{letarray} \\
  \\[-0.5em]
  \text{Call-by-need:} \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  lookup(π_k,π_i) & = & \begin{cases}
    dst(π_b) \act{\ValA} \lbln{2} & \begin{array}{@@{}l@@{}}\text{if $\lbln{1} \act{\LookupA(π_k)} π_b \act{\ValA} \lbln{2} \subtrceq π_i$} \\[-0.4em]
                                                       \text{and $\balanced{π_b \act{\ValA} \lbln{2}}$} \end{array} \\
    \square                      & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  memo(π_k,\lbl,S)(π_i)   & = & \begin{cases}
    (v,dst(π_i) \act{\LookupA(π_k)} π_v & π_v = lookup(π_k,π_i) \\
    (v,dst(π_i) \act{\LookupA(π_k)} π_e & \text{otherwise} \\
  \end{cases} \\
  & & \text{where } (v,π_e) = S(π_i \act{\LookupA(π_k)} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ memo(π_i,\mathsf{at}[e_1],\seminf{e_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\mathsf{at}[e_2],\seminf{e_2}_{ρ'})(π_i)
    \end{letarray} \\
 \end{array} \\
 \\[-0.5em]
 \begin{array}{rrclcl}
  \text{Domain of deterministic maximal traces} & && \MaxD & = & \Traces^+ \to (\Values, \Traces^{+\infty}) \\
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics With Separate Values}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[
\begin{array}{ll}
  & \text{Let } ρ_x = \lfp(λρ. [x ↦ cons(\LookupA,\lbln{2}],\seminf{\slbln{2}(\Lam{y}{\slbln{3}y})\slbln{4}}_ρ) \\
  & \text{and } ρ_{x,y} = ρ_x[y ↦ ρ_1(x)] \\
  & \text{and } f = d ↦ cons(\AppEA,\lbln{3},\seminf{\slbln{3}y}_{ρ[y↦d]}) \\
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
  cons(a,\lbl,S)(π_i)   = \{\; dst(π_i) \act{a} π_o \mid π_o ∈ S(π_i \act{a} \lbl) \;\} \\
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
    {   ρ' = \lfp(λρ'. ρ ⊔ [x ↦ cons(\LookupA,\mathsf{at}[e_1],\sempref{e_1}_{ρ'})])
     \\ π_c ∈ cons(\BindA,\mathsf{at}[e_2],\sempref{e_2}_{ρ'})(π_i)}
    {π_c ∈ \sempref{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Lam}]
    {f = d ↦ cons(\AppEA,\mathsf{at}[e],\sempref{e}_{ρ[x↦d]})}
    {\lbln{1} \act{\ValA(\FunV(f))} \lbln{2} ∈ \sempref{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i)} \qquad
  \inferrule*[right=$\textsc{App}_1$]
    {π_c ∈ cons(\AppIA,\mathsf{at}[e],\sempref{e}_ρ)(π_i)}
    {π_c ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\[-0.5em]
  \inferrule*[right=$\textsc{App}_2$]
    {\balanced{π_e} \quad π_e ∈ cons(\AppIA,\mathsf{at}[e],\sempref{e}_ρ)(π_i)
    \\\\ \getval{π_e}{\FunV(f)} \qquad π_f ∈ f(ρ(x))(π_i \act{\AppIA} π_e)}
    {\lbl \act{\AppIA} π_e \concat π_f ∈ \sempref{\slbl(e~x)}_ρ(π_i)} \\
  \\

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
  \seminf{\slbl(\Case{e_s}{\Sel})}_ρ(π_i) & = & π_s \concat \begin{cases}
      Rhs(K,\many{d})(π_i \concat π_s) & \text{if $\getval{π_s}{\ConV(K,\many{d})}$}  \\
      \bot(π_i \concat π_s) & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & cons( \CaseIA, \mathsf{at}[e_s],\seminf{e_s}_ρ)(π_i) \\
                       Rhs(K,\many{d}) & = & cons(\CaseEA,\mathsf{at}[e_K],\seminf{e_K}_{ρ[\many{x↦d}]}) \\
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
  \text{Actions}      &     a & ∈ & \Actions & ::=       & \ldots \mid \LookupA(\highlight{π}) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  lookup(π_k,π_i) & = & \begin{cases}
    dst(π_b) \act{\ValA(v)} \lbln{2} & \begin{array}{@@{}l@@{}}\text{if $\lbln{1} \act{\LookupA(π_k)} π_b \act{\ValA(v)} \lbln{2} \subtrceq π_i$} \\[-0.4em]
                                                       \text{and $\balanced{π_b \act{\ValA(v)} \lbln{2}}$} \end{array} \\
    \square                      & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  memo(π_k,\lbl,S)(π_i)   & = & \begin{cases}
    dst(π_i) \act{\LookupA(π_k)} π_v & π_v = lookup(π_k,π_i) \\
    dst(π_i) \act{\LookupA(π_k)} S(π_i \act{\LookupA(π_k)} \lbl) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ memo(π_i,\mathsf{at}[e_1],\seminf{e_1}_{ρ'})]) \\
      \text{in}  & cons(\seminf{e_2}_{ρ'},\BindA,\mathsf{at}[e_2])(π_i)
    \end{letarray} \\
  \\
  \multicolumn{3}{l}{\text{(Unchanged call-by-name equations:)}} \\
  \\[-0.5em]
  cons(S,a,\lbl)(π_i)   & = & dst(π_i) \act{a} S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & dst(π_i) \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\seminf{e}_{ρ[x↦d]},\AppEA,\mathsf{at}[e]) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $\getval{π_e}{\FunV(f)}$}  \\
                     \lbl \act{\AppIA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics for call-by-need}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Configurations}  &     κ & ∈ & \Configurations & ::= & (H,e,S) \\
  \text{Heaps}       &     H & ∈ & \Heaps  & = & \Var \pfun \Exp \\
  \text{Stacks}       &     S & ∈ & \Stacks  & ::= & \StopF \mid \ApplyF{x} \pushF S \mid \UpdateF{x} \pushF S \\
  \text{Small-step transition}     &     t & ∈ & \STransitions  & ::= & \AppIT \mid \AppET \mid \UpdateT \mid \LookupT \mid \LetT \\
  \text{Finite Small-step Traces}       &     σ & ∈ & \STraces^+      & ::= & κ \mid σ_1 \strans{t} σ_2 \\
  \text{Finite and Infinite Small-step Traces}       &     σ & ∈ & \STraces^{+\infty}      & = & \STraces^+ ∪ \lim(\STraces^+) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src_\Sigma(σ) = κ \qquad dst_\Sigma(σ) = κ } } \\
  \\[-0.5em]
  src_\Sigma(κ)                  & = & κ \\
  src_\Sigma(σ_1 \strans{t} σ_2) & = & src_\Sigma(σ_1) \\
  \\[-0.5em]
  dst_\Sigma(κ)                  & = & κ \\
  dst_\Sigma(σ_1 \strans{t} σ_2) & = & dst_\Sigma(σ_2) \\
  \\
 \end{array} \qquad
 \begin{array}{c}
  \ruleform{ σ_1 \sconcat σ_2 = σ_3 } \\
  \\[-0.5em]
  σ_1 \sconcat σ_2 = \begin{cases}
    σ_1              & \text{if $σ_1$ infinite} \\
    undefined        & \text{if $σ_1$ finite and $dst_\Sigma(σ_1) \not= src_\Sigma(σ_2)$} \\
    κ             & σ_1 = σ_2 = κ \\
    σ_1' \strans{t} σ_2 &  σ_1 = σ_1' \strans{t} κ \\
    σ_1 \strans{t} σ_2' &  σ_2 = κ \strans{t} σ_2' \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ \validtrans{κ_1 \strans{t} κ_2} \qquad \validtrace{σ} } \\
  \\[-0.5em]
  \inferrule*
    {\quad}
    {\validtrace{κ}} \quad
  \inferrule*
    {\validtrace{σ_1} \quad \validtrace{σ_2} \quad \validtrans{dst_\Sigma(σ_1) \strans{t} src_\Sigma(σ_2)}}
    {\validtrace{σ_1 \strans{t} σ_2}} \\
  \\
  \inferrule*
    {\quad}
    {\validtrans{(H[x↦e], x, S) \strans{\LookupT} (H[x↦e], e, \UpdateF{x} \pushF S)}}
  \qquad
  \inferrule*
    {\quad}
    {\validtrans{(H, v, \UpdateF{x} \pushF S) \strans{\UpdateT} (H[x↦v], v, S)}} \\
  \inferrule*
    {\quad}
    {\validtrans{(H, e~x, S) \strans{\AppIT} (H, e, \ApplyF{x} \pushF S)}}
  \qquad
  \inferrule*
    {\quad}
    {\validtrans{(H, \Lam{x}{e}, \ApplyF{y} \pushF S) \strans{\AppET} (H, e[y/x], S)}} \\
  \\
  \inferrule*
    {\fresh{x}{H}}
    {\validtrans{(H, \Let{x}{e_1}{e_2}, S) \strans{\LetT} (H[x↦e_1], e_2, S)}}
  \\
  \\[-0.5em]
 \end{array} \\
\end{array}\]
\caption{Call-by-need small-step transition system}
  \label{fig:ss-semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Domain of small-step transitions} &       &   & \SSD  & = & (\Values_\bot,\Configurations \to \STraces^{+\infty}) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semss{\wild} \colon \Exp → (\Var → \SSD) → \SSD } } \\
  \\[-0.5em]
  \bot_\Sigma & = & (\bot_\Values, \fn{κ}{κ}) \\
  \\[-0.5em]
  (f \funnyComp g)(κ) & = & f(κ) \sconcat g(dst_\Sigma(f(κ))) \\
  \\[-0.5em]
  cons(t,φ)(κ_1) & = & \begin{cases}
    κ_1 \strans{t} φ(κ_2) & \text{with $κ_2$ such that $\validtrans{κ_1 \strans{t} κ_2}$} \\
    κ_1                   & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  snoc(φ,t)(κ) & = & \begin{cases}
    φ(κ) \strans{t} κ_2 & \text{with $κ_2$ such that $\validtrans{κ_1 \strans{t} κ_2}$} \\
    φ(κ)                & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  shortcut(φ)(H,e,S) & = & \begin{cases}
    (H,e,S)  & \text{if $e = \Lam{\wild}{\wild}$} \\
    φ(H,e,S) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \semss{x}_ρ & = & ρ(x) \\
  \\[-0.5em]
  \semss{\Lam{x}{e}}_ρ & = & (\FunV(\fn{d}{\semss{e}_{ρ[x↦d]}}), \fn{κ}{κ}) \\
  \\[-0.5em]
  \semss{e~x}_ρ & = &
    \begin{letarray}
      \text{let} & (v_1,φ_1) = \semss{e}_ρ \\
                 & (v_2,φ_2) = \begin{cases}
                     f(ρ(x))     & \text{if $v = \FunV(f)$} \\
                     \bot_\Sigma & \text{otherwise}
                   \end{cases} \\
      \text{in}  & (v_2, cons(\AppIT,φ_1) \funnyComp cons(\AppET,φ_2)) \\
    \end{letarray} \\
  \\[-0.5em]
  \semss{\Let{x}{e_1}{e_2}}_ρ& = & \begin{letarray}
      \text{let} & (v_1,φ_1) = \semss{e_1}_{ρ'} \\
                 & (v_2,φ_2) = \semss{e_2}_{ρ'} \\
                 & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ (v_1,snoc(cons(\LookupT,shortcut(φ_1)),\UpdateT))]) \\
      \text{in}  & (v_2,cons(\LetT,φ_2))
    \end{letarray} \\
  \\
 \end{array} \\
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
  α_τ(S) & = & \{ α_v(v) \mid \exists π_i, π.\  (π \act{\ValA(v)} \wild) ∈ S(π_i) \wedge \balanced{π} \}  \\
  α_v(\FunV(f)) & = & single(\{ τ_1 \ArrowTy τ_2 \mid τ_2 \in α_τ(f(γ_τ(τ_1))) \})  \\
  α_v(\ConV(K,\many{d})) & = & \{ φ(K) \mid \many{σ(i) \in α_τ(d_i)}^i \}  \\
  \\[-0.5em]
  γ_τ(A)(π_i) & = & \{ π \act{\ValA(v)} \wild \mid \balanced{π} \wedge v ∈ γ_v(A) \}  \\
  γ_v(A) & = &   \{ \ConV(K,\many{d}) \mid φ(K) ∈ A \wedge \many{d_i = γ_τ(σ(i))}^i \} \\
         &   & ∪ \{ \FunV(f) \mid \forall (τ_1 \ArrowTy τ_2) ∈ A.\  f(γ_τ(τ_1)) \subseteq γ_τ(τ_2)  \}  \\
  \\
 \end{array} \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \poset{\Type}) → \poset{\Type} } } \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i)   & = & dst(π_i) \act{a} S(π_i \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl e}_ρ    (π_i)   & = & \varnothing \qquad \text{if $dst(π_i) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl x}_ρ    (π_i)   & = & ρ(x)(π_i) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{x}{e})\slbln{2}}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\mathsf{at}[e],\seminf{e}_{ρ[x↦d]}) \\
      \text{in}  & α_v(\FunV(f)) \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(e~x)}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{e}_ρ(π_i \act{\AppIA} \mathsf{at}[e]) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(x))(π_i \act{\AppIA} π_e) & \text{if $π_e = \wild \act{\ValA(\FunV(f))} \wild$}  \\
                     \lbl \act{\AppIA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{x}{e_1}{e_2})}_ρ(π_i) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [x ↦ \seminf{e_1}_{ρ'}]) \\
      \text{in}  & cons(\BindA,\mathsf{at}[e_2],\seminf{e_2}_{ρ'})(π_i)
    \end{letarray} \\
  \\
  \seminf{\slbln{1}(K~\many{x})\slbln{2}}_ρ(π_i) & = & \lbln{1} \act{\ValA(\ConV(K,\many{ρ(x)}))} \lbln{2} \\
  \\[-0.5em]
  \seminf{\slbl(\Case{e_s}{\Sel})}_ρ(π_i) & = & \begin{cases}
      π_s \concat Rhs(K,\many{d})(π_i \concat π_s) & \text{if $π_s = \wild \act{\ValA(\ConV(K,\many{d}))} \wild$}  \\
      π_s & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & cons( \CaseIA, \mathsf{at}[e_s],\seminf{e_s}_ρ)(π_i) \\
                       Rhs(K,\many{d}) & = & cons(\CaseEA,\mathsf{at}[e_K],\seminf{e_K}_{ρ[\many{x↦d}]}) \\
                     \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Simple type inference as abstract interpretation}
  \label{fig:semantics}
\end{figure}

