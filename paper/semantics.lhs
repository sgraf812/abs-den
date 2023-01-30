\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}    & \px,\py,\pz & ∈ & \Var &      & \\
  \text{Variables}    &         \pv & ∈ & \Val & ::=  & \Lam{\px}{\pe} \\
  \text{Expressions}  &         \pe & ∈ & \Exp & ::=  & \slbl \px \mid \slbln{1} \pv \slbln{2} \mid \slbl \pe~\px \mid \slbl \Let{\px}{\pe_1}{\pe_2} \\
  \\
  \text{Actions} & a & ∈ & \Actions & ::=  & \AppIA \mid \AppEA \mid \LookupA(π^+) \mid \BindA \\
  \text{Finite Traces} & π^+ & ∈ & \Traces^+ & ::=  & \lbl \mid \lbl \act{a} π^+  \\

  \text{Semantic Domain} &     d & ∈ & \AbsD & & \text{Specified as needed} \\
  \text{Values}          &     v & ∈ & \Values & ::= & \FunV(\AbsD \to \AbsD) \\
  \\
  \text{Limit of a set of traces} & && \lim \mathcal{T} & = & \{ π \mid ∀n∈\mathbb{N}. π[0..n] ∈ \mathcal{T} \} \\
  \\
  \text{Infinite Traces} & π^\infty & ∈ & \Traces^{\infty} &  ::=  & \lim \Traces^+    \\
  \text{Finite and infinite Traces} & π & ∈ & \Traces^{+\infty} & ::=  & \Traces^+ ∪ \Traces^\infty    \\
  \\
  \text{Domain of prefix traces} & && \PrefD & = & \Traces^+ \to \poset{\Traces^+} \\
  \text{Domain of deterministic maximal traces} & && \MaxD & = & \Traces^+ \to \Traces^{+\infty} \\
  \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \atlbl{\pe} = \lbl } } \\
  \\[-0.5em]
  \atlbl{ \slbln{1} \pv \slbln{2} } & = & \slbln{1} \\
  \atlbl{ \slbl \wild \ } & = & \slbl \\
  \\
 \end{array} \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src(π) = \lbl \qquad dst(π^+) = \lbl } } \\
  \\[-0.5em]
  src(\lbl)           & = & \lbl \\
  src(\lbl \act{a} π) & = & \lbl \\
  \\[-0.5em]
  dst(\lbl)           & = & \lbl \\
  dst(π^+ \act{a} \lbl) & = & \lbl \\
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
    {\balanced{\lbl \act{\LookupA(\wild)} π}}
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
   \Let{\px}{\Lam{\py}{\py}}{\px~\px~\px)} \\
   \slbln{1}\Let{\px}{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}
\end{gather*}

Trace of the expression:
\[
\begin{array}{r@@{}l}
   \multicolumn{2}{c}{\slbln{1}\Let{\px}{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}} \\
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
  \bot(π_i^+)   & = & dst(π_i^+) \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i^+)   & = & dst(π_i^+) \act{a} S(π_i^+ \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl \pe}_ρ    (π_i^+)   & = & \bot(π_i^+) \qquad \text{if $dst(π_i^+) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl \px}_ρ    (π_i^+)   & = & ρ(\px)(π_i^+) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{\px}{\pe})\slbln{2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\atlbl{\pe},\seminf{\pe}_{ρ[\px↦d]}) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\pe~\px)}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{\pe}_ρ(π_i^+ \act{\AppIA} \atlbl{\pe}) \\
      \text{in}  & \lbl \act{\AppIA} π_e \concat \begin{cases}
                     f(ρ(\px))(π_i^+ \act{\AppIA} π_e) & \text{if $\getval{π_e}{\FunV(f)}$}  \\
                     \bot(π_i^+ \act{\AppIA} π_e) & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ cons(\LookupA(π_i^+),\atlbl{\pe_1},\seminf{\pe_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
  \\[-0.5em]
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics With Crazy Traces}
  \label{fig:semantics}
\end{figure}

% Note [Design of Maximal Trace Semantics]
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% A stateless (prefix) trace semantics' defining feature is the absence of
% full-blown configurations between actions. However, states can be
% reconstructed from looking at the history of actions in the initialisation
% trace. So it is quite vital that the actions carry enough information.
%
% The need for a value action
% ---------------------------
% Values have after labels, so that when we reach at(v) we make one value
% transition to announce the value of at(v) in the trace. Without this
% action, it would be hard to differentiate between stuck and successful
% maximal traces. Furthermore, it plays a crucial role in the memoisation
% mechanism, where we reconstruct the memoised value from the trace.
%
% The need for an update action
% -----------------------------
% Memoisation could well work by looking for a balanced sub-trace in the
% initialisation trace that started with look(π_k). In fact, earlier
% versions did exactly that, and it worked great!
% Unfortunately, it has the following drawbacks:
%   * We need to define relatively early what a balanced trace is.
%     The semantics itself should not depend on that...
%   * It is simpler to define the abstraction to stateful prefix trace semantics
%     when there are corresponding update actions
%   * It is better to be explicit to announce exactly when "the heap binding
%     changes" for the perspective of weak memory models and interleavings of
%     parallel traces (TODO: Read up on that!), which is one of the prime
%     reasons to consider stateless trace semantics in the first place.
%
% Why is the stateless semantics not simply (V, T+ -> T+∞)?
% ---------------------------------------------------------
% ... and in the process could abandon the value action (if we were willing
% to detect stuckness by looking at V)?
%
% Because then we can't see the prefix T+ when we have to extend ρ at let
% bindings. But this is our primary mechanism for sharing! Similarly for
% call-by-value. So we are stuck with value actions and T+ -> T+∞.

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \mathbb{P}^* & = & \{ C \in \poset{\Traces^+} \mid C \text{ is a prefix-closed chain of traces} \} \\
  \\[-0.5em]
  \multicolumn{3}{c}{ \ruleform{ α^{*} : \Traces^{+\infty} \to \mathbb{P}^* \qquad γ^{*} : \mathbb{P}^* \to \Traces^{+\infty} } } \\
  \\[-0.5em]
  α^{*}(π) & = & \{ π^+ \mid π^+ \text{ is a prefix of } π \} \\
  γ^{*}(C) & = & \Lub C \qquad \text{where $\lub$ is defined on the prefix-closed chain $C$} \\
  \Traces^{+\infty} & \GaloiS{α^{*}}{γ^{*}} & \mathbb{P}^* \\
  \Traces^+ \to \Traces^{+\infty} & \GaloiS{\dot{α}^{*}}{\dot{γ}^{*}} & \Traces^+ \to \mathbb{P}^* \\
  \seminf{\pe} & \GaloiS{\ddot{α}^{*}}{\ddot{γ}^{*}} & \sempref{\pe} \\
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
  \bot_\MaxD(π_i^+)   & = & (\bot_\Values,dst(π_i^+)) \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  f \second (a,b)  & = & (a, f a) \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i^+)   & = & (dst(π_i^+) \act{a} {}) \second S(π_i^+ \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl \pe}_ρ    (π_i^+)   & = & \bot(π_i^+) \qquad \text{if $dst(π_i^+) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl \px}_ρ    (π_i^+)   & = & ρ(\px)(π_i^+) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{\px}{\pe})\slbln{2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\atlbl{\pe},\seminf{\pe}_{ρ[\px↦d]}) \\
      \text{in}  & (\FunV(f), \lbln{1} \act{\ValA} \lbln{2}) \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\pe~\px)}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & (v_e, π_e) = \seminf{\pe}_ρ(π_i^+ \act{\AppIA} \atlbl{\pe}) \\
      \text{in}  & (\lbl \act{\AppIA} π_e \concat {}) \second \begin{cases}
                     f(ρ(\px))(π_i^+ \act{\AppIA} π_e) & \text{if $v_e = \FunV(f)$}  \\
                     \bot(π_i^+ \act{\AppIA} π_e) & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ cons(\LookupA(π_i^+),\atlbl{\pe_1},\seminf{\pe_1}_{ρ'})]) \\
      \text{in}  & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
  \\[-0.5em]
  \text{Call-by-need:} \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  memo(π_k,S)(π_i^+)   & = & \begin{cases}
    (v, dst(π_b^+) \act{\ValA} \lbln{2}) & \begin{array}{@@{}l@@{}}\text{if $\lbln{1} \act{\LookupA(π_k)} π_b^+ \act{\ValA(v)} \lbln{2} \subtrceq π_i^+$} \\[-0.4em]
                                                       \text{and $\balanced{π_b^+ \act{\ValA(v)} \lbln{2}}$} \\
                                                       \text{and $(v,π) = S(π_i^+)$} \end{array} \\
    S(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & S' = memo(π_i^+,\seminf{\pe_1}_{ρ'}) \\
                 & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ cons(\LookupA(π_i^+),\atlbl{\pe_1},S']) \\
      \text{in}  & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
 \end{array} \\
 \\[-0.5em]
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Domain of deterministic maximal traces} & && \MaxD & = & \Traces^+ \to (\Values, \Traces^{+\infty}) \\
  \text{Values}          &     v & ∈ & \Values & ::= & \FunV(\MaxD \to \MaxD) \mid \bot_\Values \\
 \end{array} \\
\end{array}\]
\caption{Structural Maximal Trace Semantics With Separate Values}
  \label{fig:semantics}
\end{figure}

\begin{figure}
\[
\begin{array}{ll}
  & \text{Let } ρ_\px = \lfp(λρ. [\px ↦ cons(\LookupA,\lbln{2}],\seminf{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_ρ) \\
  & \text{and } ρ_{\px,\py} = ρ_\px[\py ↦ ρ_1(\px)] \\
  & \text{and } f = d ↦ cons(\AppEA,\lbln{3},\seminf{\slbln{3}\py}_{ρ[\py↦d]}) \\
  & \text{Evaluate }\slbln{1}\Let{\px}{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)} \\
  & \\
  & \seminf{\slbln{1}\Let{\px}{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}}_\bot(\lbln{1}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \seminf{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}_{ρ_\px}(\lbln{1} \act{\BindA} \lbln{5}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \seminf{\slbln{6}(\slbln{7}\px~\px)}_{ρ_\px}(\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \seminf{\slbln{7}\px}_{ρ_\px}(\overbrace{\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \lbln{7}}^{π_1}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \seminf{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_1 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_\px(\px))(π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \seminf{\slbln{3}\py}_{ρ_{\px,\py}}(\overbrace{π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \seminf{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_2 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_\px(\px))(π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \seminf{\slbln{3}\py}_{ρ_{\px,\py}}(\overbrace{π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_3}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \seminf{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_3 \act{\LookupA} \lbln{2}) \\
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
  cons(a,\lbl,S)(π_i^+)   = \{\; dst(π_i^+) \act{a} π_o \mid π_o ∈ S(π_i^+ \act{a} \lbl) \;\} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Bot}]
    {\quad}
    {dst(π) ∈ \sempref{\slbl \pe}_ρ(π)}
  \qquad
  \inferrule*[right=\textsc{Var}]
    {π_c ∈ ρ(\px)(π_i^+)}
    {π_c ∈ \sempref{\slbl \px}_ρ(π_i^+)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Let}]
    {   ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ cons(\LookupA(π_i^+),\atlbl{\pe_1},\sempref{\pe_1}_{ρ'})])
     \\ π_c ∈ cons(\BindA,\atlbl{\pe_2},\sempref{\pe_2}_{ρ'})(π_i^+)}
    {π_c ∈ \sempref{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Lam}]
    {f = d ↦ cons(\AppEA,\atlbl{\pe},\sempref{\pe}_{ρ[\px↦d]})}
    {\lbln{1} \act{\ValA(\FunV(f))} \lbln{2} ∈ \sempref{\slbln{1}(\Lam{\px}{\pe})\slbln{2}}_ρ(π_i^+)} \qquad
  \inferrule*[right=$\textsc{App}_1$]
    {π_c ∈ cons(\AppIA,\atlbl{\pe},\sempref{\pe}_ρ)(π_i^+)}
    {π_c ∈ \sempref{\slbl(\pe~\px)}_ρ(π_i^+)} \\
  \\[-0.5em]
  \inferrule*[right=$\textsc{App}_2$]
    {\balanced{π_e} \quad π_e ∈ cons(\AppIA,\atlbl{\pe},\sempref{\pe}_ρ)(π_i^+)
    \\\\ \getval{π_e}{\FunV(f)} \qquad π_f ∈ f(ρ(\px))(π_i^+ \act{\AppIA} π_e)}
    {\lbl \act{\AppIA} π_e \concat π_f ∈ \sempref{\slbl(\pe~\px)}_ρ(π_i^+)} \\
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
  \text{Expressions}  &   \pe & ∈ & \Exp     & ::=       & \ldots \mid K~\many{\px} \mid \Case{\pe}{\Sel} \\
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
  \seminf{\slbln{1}(K~\many{\px})\slbln{2}}_ρ(π_i^+) & = & \lbln{1} \act{\ValA(\ConV(K,\many{ρ(\px)}))} \lbln{2} \\
  \\[-0.5em]
  \seminf{\slbl(\Case{\pe_s}{\Sel})}_ρ(π_i^+) & = & π_s \concat \begin{cases}
      Rhs(K,\many{d})(π_i^+ \concat π_s) & \text{if $\getval{π_s}{\ConV(K,\many{d})}$}  \\
      \bot(π_i^+ \concat π_s) & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & cons( \CaseIA, \atlbl{\pe_s},\seminf{\pe_s}_ρ)(π_i^+) \\
                       Rhs(K,\many{d}) & = & cons(\CaseEA,\atlbl{\pe_K},\seminf{\pe_K}_{ρ[\many{\px↦d}]}) \\
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
  \text{Actions}      &     a & ∈ & \Actions & ::=       & \ldots \mid \UpdateA(\highlight{π}) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  snoc(\lbl, a, S)(π_i^+)   & = & S(π_i^+) \act{a} \lbl \\
  \\[-0.5em]
  memo(π_k,S)(π_i^+)   & = & \begin{cases}
    dst(π_b^+) \act{\ValA(v)} \lbln{2} & \begin{array}{@@{}l@@{}}\text{if $\lbln{1} \act{\LookupA(π_k)} π_b^+ \act{\ValA(v)} \lbln{2} \subtrceq π_i^+$} \\[-0.4em]
                                                       \text{and $\balanced{π_b^+ \act{\ValA(v)} \lbln{2}}$} \end{array} \\
    S(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & S' = \highlight{memo(π_i^+,\seminf{\pe_1}_{ρ'})} \\
                 & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ snoc(cons(\LookupA(π_i^+),\atlbl{\pe_1},S']), \UpdateA(π_i^+), ???) \\
      \text{in}  & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
  \\
  \multicolumn{3}{l}{\text{(Unchanged call-by-name equations:)}} \\
  \\[-0.5em]
  cons(S,a,\lbl)(π_i^+)   & = & dst(π_i^+) \act{a} S(π_i^+ \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl \pe}_ρ    (π_i^+)   & = & dst(π_i^+) \qquad \text{if $dst(π_i^+) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl \px}_ρ    (π_i^+)   & = & ρ(\px)(π_i^+) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{\px}{\pe})\slbln{2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\seminf{\pe}_{ρ[\px↦d]},\AppEA,\atlbl{\pe}) \\
      \text{in}  & \lbln{1} \act{\ValA(\FunV(f))} \lbln{2} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\pe~\px)}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{\pe}_ρ(π_i^+ \act{\AppIA} \atlbl{\pe}) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(\px))(π_i^+ \act{\AppIA} π_e) & \text{if $\getval{π_e}{\FunV(f)}$}  \\
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
  \text{Configurations}  &     κ & ∈ & \Configurations & ::= & (\pH,\pe,\pE,\pS) \\
  \text{Addresses}       &   \pa & ∈ & \Addresses  & \subseteq & ℕ \\
  \text{Heaps}       &     \pH & ∈ & \Heaps  & = & \Addresses \pfun (\Envs,\Exp) \\
  \text{Environments} &     \pE & ∈ & \Envs  & = & \Var \pfun \Addresses \\
  \text{Stacks}       &     \pS & ∈ & \Stacks  & ::= & \StopF \mid \ApplyF{\pa} \pushF \pS \mid \UpdateF{\pa} \pushF \pS \\
  \text{Small-step transition}     &     t & ∈ & \STransitions  & ::= & \AppIT \mid \AppET \mid \UpdateT \mid \LookupT \mid \LetT \\
  \text{Finite Small-step Traces}       &     σ & ∈ & \STraces^+      & ::= & κ \mid κ \strans{t} σ \\
  \text{Finite and Infinite Small-step Traces}       &     σ & ∈ & \STraces^{+\infty}      & = & \STraces^+ ∪ \lim(\STraces^+) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src_\Sigma(σ) = κ \qquad dst_\Sigma(σ) = κ } } \\
  \\[-0.5em]
  src_\Sigma(κ)              & = & κ \\
  src_\Sigma(κ \strans{t} σ) & = & κ \\
  \\[-0.5em]
  dst_\Sigma(κ)              & = & κ \\
  dst_\Sigma(κ \strans{t} σ) & = & dst_\Sigma(σ) \\
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
    {\validtrans{κ \strans{t} src_\Sigma(σ)} \quad \validtrace{σ}}
    {\validtrace{κ \strans{t} σ}} \\
  \\
  \inferrule*
    {\pa = \pE(\px)}
    {\validtrans{(\pH, \px, \pE, \pS) \strans{\LookupT} (\pH, \pH(\pa), \UpdateF{\pa} \pushF \pS)}}
  \qquad
  \inferrule*
    {\quad}
    {\validtrans{(\pH, \pv, \pE, \UpdateF{\pa} \pushF \pS) \strans{\UpdateT} (\pH[\pa↦(\pE,\pv)], \pv, \pE, \pS)}} \\
  \\[-0.5em]
  \inferrule*
    {\pa = \pE(\px)}
    {\validtrans{(\pH, \pe~\px, \pE, \pS) \strans{\AppIT} (\pH, \pe, \pE, \ApplyF{\pa} \pushF \pS)}}
  \qquad
  \inferrule*
    {\quad}
    {\validtrans{(\pH, \Lam{\px}{\pe}, \pE, \ApplyF{\pa} \pushF \pS) \strans{\AppET} (\pH, \pe, \pE[\px↦\pa], \pS)}} \\
  \\[-0.5em]
  \inferrule*
    {\fresh{\pa}{\pH} \quad \pE' = \pE[\px↦\pa]}
    {\validtrans{(\pH, \Let{\px}{\pe_1}{\pe_2}, \pE, \pS) \strans{\LetT} (\pH[\pa↦(\pE',\pe_1)], \pe_2, \pE', \pS)}}
  \\
  \\[-0.5em]
 \end{array} \\
\end{array}\]
\caption{Call-by-need small-step transition system Σ}
  \label{fig:ss-syntax}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Domain of small-step transitions} &       &   & \SSD  & = & (\Values_\bot,\Configurations \to \STraces^{+\infty}) \\
  \text{Values}          &     v & ∈ & \Values & ::= & \FunV(\SSD \to \SSD) \mid \bot_\Values \\
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
  shortcut(φ)(\pH,\pe,\pS) & = & \begin{cases}
    (\pH,\pe,\pS)  & \text{if $\pe = \Lam{\wild}{\wild}$} \\
    φ(\pH,\pe,\pS) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \semss{\px}_ρ & = & ρ(\px) \\
  \\[-0.5em]
  \semss{\Lam{\px}{\pe}}_ρ & = & (\FunV(\fn{d}{\semss{\pe}_{ρ[\px↦d]}}), \fn{κ}{κ}) \\
  \\[-0.5em]
  \semss{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & (v_1,φ_1) = \semss{\pe}_ρ \\
                 & (v_2,φ_2) = \begin{cases}
                     f(ρ(\px))     & \text{if $v = \FunV(f)$} \\
                     \bot_\Sigma & \text{otherwise}
                   \end{cases} \\
      \text{in}  & (v_2, cons(\AppIT,φ_1) \funnyComp cons(\AppET,φ_2)) \\
    \end{letarray} \\
  \\[-0.5em]
  \semss{\Let{\px}{\pe_1}{\pe_2}}_ρ& = & \begin{letarray}
      \text{let} & (v_1,φ_1) = \semss{\pe_1}_{ρ'} \\
                 & (v_2,φ_2) = \semss{\pe_2}_{ρ'} \\
                 & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ (v_1,snoc(cons(\LookupT,shortcut(φ_1)),\UpdateT))]) \\
      \text{in}  & (v_2,cons(\LetT,φ_2))
    \end{letarray} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Structural call-by-need small-step semantics}
  \label{fig:ss-semantics}
\end{figure}

\begin{figure}
  \begin{lemma}
    Let $(v,φ) = \semss{\pe}_ρ$. Then $\validtrace{φ(κ)}$ for every initial configuration $κ$.
  \end{lemma}
  \begin{definition}[Maximal small-step trace]
    A small-step trace $σ$ is \emph{maximal} iff
    \begin{itemize}
      \item $\validtrace{σ}$, and
      \item if $σ$ is finite, then there is no $κ'$ and $t$ such that
            $\validtrans{dst_\Sigma(σ) \strans{t} κ'}$.
    \end{itemize}
  \end{definition}

  \begin{definition}[Balanced small-step trace]
    A finite small-step trace
    $σ=(\pH,\pe,\pS) \strans{} ... \strans{} (\pH',\pe',\pS')$
    is \emph{balanced} if $\validtrace{σ}$, $\pv$ is a value, $\pS=\pS'$, and
    every intermediate stack
    extends $\pS$.
  \end{definition}

  The maximal trace of the initial configuration of an expression is either
  infinite, stuck, or balanced.

  Clearly, a term's defining property wrt. a small-step transition system is the
  maximal trace of its initial configuration.

  \begin{definition}[Maximally balanced small-step trace]
    A finite small-step trace
    $σ=(\pH,\pe,\pS) \strans{} ... \strans{} (\pH',\pe',\pS')$
    is \emph{maximally balanced} if $\validtrace{σ}$, $\pv$ is a value, $\pS=\pS'$, and
    every intermediate stack
    extends $\pS$.
  \end{definition}

  \begin{definition}[Correctness relation]
    Consider the relation $\wild \vdash \wild \sim \wild \triangleq \gfp(F)$, where
    \[
      F(X) = \{ (\pH, \pE, ρ) \mid \forall \pa \in \dom(\pE).\ (\pE',\pe') = \pH(\pa) \wedge ρ(\px) = \semss{\pe'}_{ρ'} \wedge (\pH, \pE', ρ') \in X \}
    \]
    We say that a denotational environmant ρ is \emph{consistent} with an environment
    $\pE$ in a heap $\pH$ iff $\pH \vdash \pE \sim ρ$.
  \end{definition}

  \begin{theorem}Let $(v,φ) = \semss{\pe}_ρ$. Then for all configurations
  $κ=(\pH,\pe,\pE,\pS)$ where $\pH \vdash \pE \sim ρ$ the small-step trace $φ(κ)$ is the
  small-step trace starting from $κ$ that is either balanced or, if no balanced
  trace exists, it is maximal.
  \end{theorem}

  Note that for the initial configuration of an expression, the balanced
  small-step trace is exactly the maximal finite trace that ends with a value.

\end{figure}

\begin{figure}
\[
\begin{array}{ll}
  & \text{Let } ρ_\px = \lfp(λρ. [\px ↦ cons(\LookupT,\semss{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_ρ]) \\
  & \text{and } ρ_{\px,\py} = ρ_\px[\py ↦ ρ_1(\px)] \\
  & \text{and } f = d ↦ cons(\AppET,\semss{\slbln{3}\py}_{ρ[\py↦d]}) \\
  & \text{Evaluate }\Let{\px}{\Lam{\py}{\py}}{\px~\px~\px)} \\
  & \\
  & \semss{\slbln{1}\Let{\px}{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}}_\bot(\lbln{1}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \semss{\slbln{5}(\slbln{6}(\slbln{7}\px~\px)~\px)}_{ρ_\px}(\lbln{1} \act{\BindA} \lbln{5}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \semss{\slbln{6}(\slbln{7}\px~\px)}_{ρ_\px}(\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6}) \\
  & \\[-0.9em]
  ⇒ & \lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \semss{\slbln{7}\px}_{ρ_\px}(\overbrace{\lbln{1} \act{\BindA} \lbln{5} \act{\AppIA} \lbln{6} \act{\AppIA} \lbln{7}}^{π_1}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \semss{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_1 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_\px(\px))(π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \semss{\slbln{3}\py}_{ρ_{\px,\py}}(\overbrace{π_1 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \semss{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_2 \act{\LookupA} \lbln{2}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} f(ρ_\px(\px))(π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4}) \\
  & \\[-0.9em]
  ⇒ & π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \semss{\slbln{3}\py}_{ρ_{\px,\py}}(\overbrace{π_2 \act{\LookupA} \lbln{2} \act{\ValA(\FunV(f))} \lbln{4} \act{\AppEA} \lbln{3}}^{π_3}) \\
  & \\[-0.9em]
  ⇒ & π_3 \act{\LookupA} \semss{\slbln{2}(\Lam{\py}{\slbln{3}\py})\slbln{4}}_{ρ_\px}(π_3 \act{\LookupA} \lbln{2}) \\
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
\caption{Evalation of $\semss{\wild}$}
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
    S & S = \{ \pe \} \\
    \varnothing & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  α_τ(S) & = & \{ α_v(v) \mid \exists π_i^+, π.\  (π \act{\ValA(v)} \wild) ∈ S(π_i^+) \wedge \balanced{π} \}  \\
  α_v(\FunV(f)) & = & single(\{ τ_1 \ArrowTy τ_2 \mid τ_2 \in α_τ(f(γ_τ(τ_1))) \})  \\
  α_v(\ConV(K,\many{d})) & = & \{ φ(K) \mid \many{σ(i) \in α_τ(d_i)}^i \}  \\
  \\[-0.5em]
  γ_τ(A)(π_i^+) & = & \{ π \act{\ValA(v)} \wild \mid \balanced{π} \wedge v ∈ γ_v(A) \}  \\
  γ_v(A) & = &   \{ \ConV(K,\many{d}) \mid φ(K) ∈ A \wedge \many{d_i = γ_τ(σ(i))}^i \} \\
         &   & ∪ \{ \FunV(f) \mid \forall (τ_1 \ArrowTy τ_2) ∈ A.\  f(γ_τ(τ_1)) \subseteq γ_τ(τ_2)  \}  \\
  \\
 \end{array} \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \poset{\Type}) → \poset{\Type} } } \\
  \\[-0.5em]
  cons(a,\lbl,S)(π_i^+)   & = & dst(π_i^+) \act{a} S(π_i^+ \act{a} \lbl) \\
  \\[-0.5em]
  \seminf{\slbl \pe}_ρ    (π_i^+)   & = & \varnothing \qquad \text{if $dst(π_i^+) \not= \lbl$} \\
  \\[-0.9em]
  \seminf{\slbl \px}_ρ    (π_i^+)   & = & ρ(\px)(π_i^+) \\
  \\[-0.5em]
  \seminf{\slbln{1}(\Lam{\px}{\pe})\slbln{2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & f = d ↦ cons(\AppEA,\atlbl{\pe},\seminf{\pe}_{ρ[\px↦d]}) \\
      \text{in}  & α_v(\FunV(f)) \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\pe~\px)}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & π_e = \seminf{\pe}_ρ(π_i^+ \act{\AppIA} \atlbl{\pe}) \\
      \text{in}  & \begin{cases}
                     \lbl \act{\AppIA} π_e \concat f(ρ(\px))(π_i^+ \act{\AppIA} π_e) & \text{if $π_e = \wild \act{\ValA(\FunV(f))} \wild$}  \\
                     \lbl \act{\AppIA} π_e & \text{otherwise}  \\
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\slbl(\Let{\px}{\pe_1}{\pe_2})}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{let} & ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ \seminf{\pe_1}_{ρ'}]) \\
      \text{in}  & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
  \\
  \seminf{\slbln{1}(K~\many{\px})\slbln{2}}_ρ(π_i^+) & = & \lbln{1} \act{\ValA(\ConV(K,\many{ρ(\px)}))} \lbln{2} \\
  \\[-0.5em]
  \seminf{\slbl(\Case{\pe_s}{\Sel})}_ρ(π_i^+) & = & \begin{cases}
      π_s \concat Rhs(K,\many{d})(π_i^+ \concat π_s) & \text{if $π_s = \wild \act{\ValA(\ConV(K,\many{d}))} \wild$}  \\
      π_s & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & cons( \CaseIA, \atlbl{\pe_s},\seminf{\pe_s}_ρ)(π_i^+) \\
                       Rhs(K,\many{d}) & = & cons(\CaseEA,\atlbl{\pe_K},\seminf{\pe_K}_{ρ[\many{\px↦d}]}) \\
                     \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Simple type inference as abstract interpretation}
  \label{fig:semantics}
\end{figure}

