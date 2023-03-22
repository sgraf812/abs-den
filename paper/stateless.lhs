\section{Stateless Semantics}
\label{sec:stateless}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Program point}   & \pp      & ∈ & \ProgramPoints        &  =  & \{ \return \} ∪ \Exp \\
  \text{Actions}         & a        & ∈ & \Actions              & ::= & \AppIA(\pa) \mid \AppEA(\pa) \mid \BindA \mid \LookupA(\pa) \mid \UpdateA(\pa) \mid \ValA(v) \\
  \text{Finite Traces}   & π^+      & ∈ & \Traces^+             & ::= & \pp\trend \mid \pp \act{a} π^+  \\
  \text{Infinite Traces} & π^\infty & ∈ & \Traces^{\infty}      & ::=_{\gfp} & \pp \act{a} π^\infty \hspace{1ex} = \lim \Traces^+    \\
  \text{Finite and infinite Traces} & π & ∈ & \Traces^{+\infty} & ::=_{\gfp} & \pp\trend \mid \pp \act{a} π \hspace{1ex} =  \Traces^+ ∪ \Traces^\infty    \\
  \\
  \text{Limit of a set of traces} & && \lim \mathcal{T} & = & \{ π \mid ∀n∈\mathbb{N}. π[0..n] ∈ \mathcal{T} \} \\
  \\
  \text{Domain of maximal traces} & d & ∈ & \MaxD   & ⊂ & \Traces^+ \to_c \Traces^{+\infty} \\
  \text{Values}                   & v & ∈ & \Values & ::= & \FunV(\MaxD \to_c \MaxD) \\
 \end{array} \\
 \\[-0.5em]
 \ruleform{hash : \Traces^+ \to \Addresses} \quad \text{an injective function on the number of $\BindA$ actions in the trace} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src(π) = \pp \qquad tgt(π) = \pp } } \\
  \\[-0.5em]
  src(\pp\trend)     & = & \pp \\
  src(\pp \act{a} π) & = & \pp \\
  \\[-0.5em]
  tgt(π)    & = & \begin{cases}
    undefined & \text{if $π$ infinite} \\
    \pp       & \text{if $π = ... \act{a} \pp\trend$}
  \end{cases} \\
 \end{array} \quad
 \begin{array}{c}
  \ruleform{ π_1 \concat π_2 = π_3 } \\
  \\[-0.5em]
  π_1 \concat π_2 = \begin{cases}
    \pp \act{a} (π_1' \concat π_2) & \text{if $π_1 = \pp \act{a} π_1'$} \\
    π_2                     & \text{if $π_1 = \pp\trend$ and $src(π_2) = \pp$} \\
    undefined               & \text{if $π_1 = \pp\trend$ and $src(π_2) \not= \pp$} \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{ll}
  \begin{array}{c}
  \ruleform{ \getval{π}{(\pv,v)} }
  \\[-0.5em]
  \inferrule*[right=\textsc{ValVal}]
    {\quad}
    {\getval{π^{+} \act{} \pv \act{\ValA(v)} \return\trend}{(\pv,v)}} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{ValUpd}]
    {\getval{π^+}{(\pv,v)}}
    {\getval{π^{+} \act{\UpdateA(\wild)} \return\trend}{(\pv,v)}}
  \\[-0.5em]
  \end{array} &
  \begin{array}{c}
  \ruleform{ \balanced{π} } \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalVal}]
    {\quad}
    {\balanced{\pp \act{\ValA(v)} \return\trend}}
  \qquad
  \inferrule*[right=\textsc{BalApp}]
    {\balanced{π_1}\quad\balanced{π_2}}
    {\balanced{\pp \act{\AppIA} π_1 \act{\AppEA} π_2}} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{BalVar}]
    {\balanced{π}}
    {\balanced{\pp \act{\LookupA(\wild)} π \act{\UpdateA(\wild)} \return\trend}}
  \qquad
  \inferrule*[right=\textsc{BalLet}]
    {\balanced{π}}
    {\balanced{\pp \act{\BindA} π}} \\
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
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var \pfun \MaxD) → \MaxD } } \\
  \\[-0.5em]
  \bot(π_i^+)   & = & tgt(π_i^+)\trend \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  \stepm{p}{a}{\pp}(π_i^+)   & = & \begin{cases}
    tgt(π_i^+) \act{a} \pp\trend & \text{if $tgt(π_i^+)$ matches $p$} \\
    \bot(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  (d_1 \fcomp d_2)(π_i^+)   & = & d_1(π_i^+) \concat d_2(π_i^+ \concat d_1(π_i^+)) \\
  \\[-0.5em]
  apply(d_\px)(π_\pe^+)   & = & \begin{cases}
    f(d_\px)(π_\pe^+) & \text{if $\getval{π_\pe^+}{(\wild,\FunV(f))}$}  \\
    \bot(π_\pe^+) & \text{otherwise}  \\
  \end{cases} \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ (π = π_1 \concat π_s \concat π_2)  \\
  \\[-0.5em]
%  μ(π_i^+)(\pa) & = & \begin{cases}
%    (\pv, v) & \text{if $\pv \act{\ValA(v)} \return \left(\act{\UpdateA(\wild)} \return \right)^* \act{\UpdateA(\pa)} \return \trend \subtrceq π_i^+$} \\
%    undefined & \text{otherwise} \\
%  \end{cases}  \\
%  \\[-0.5em]
  μ(π_i^+)(\pa) & = & \begin{cases}
    (\pv, v) & \text{if $π_{\pv} \act{\UpdateA(\pa)} \return \trend \subtrceq π_i^+$ and $\getval{π_{\pv}}{(\pv,v)}$} \\
    undefined & \text{otherwise} \\
  \end{cases}  \\
  \\[-0.5em]
  memo(\pa,\pe,d)(π_i^+)   & = & \begin{cases}
    tgt(π_i^+) \act{\LookupA(\pa)} \pv \act{\ValA(v)} \return \act{\UpdateA(\pa)} \return \trend & \text{if $μ(π_i^+)(\pa) = (\pv,v)$} \\
    (\step{\LookupA(\pa)}{\pe} \fcomp d \fcomp \stepm{\return}{\UpdateA(\pa)}{\return})(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\pe}_ρ    (π_i^+)   & = & \bot(π_i^+) \qquad \text{if $tgt(π_i^+) \not= \pe$} \\
  \\[-0.5em]
  \seminf{\px}_ρ              & = & \ternary{\px ∈ \dom(ρ)}{ρ(\px)}{\bot} \\
  \\[-0.5em]
  \seminf{\Lam{\px}{\pe}}_ρ & = &
    \begin{letarray}
      \text{let} & f = d ↦ \stepm{\return}{\AppEA}{\pe} \fcomp \seminf{\pe}_{ρ[\px↦d]} \\
      \text{in}  & \step{\ValA(\FunV(f))}{\return} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\pe~\px}_ρ & = & \ternary{\px ∈ \dom(ρ)}{\step{\AppIA}{\pe} \fcomp \seminf{\pe}_ρ \fcomp apply(ρ(\px))}{\bot} \\
  \\[-0.5em]
  \seminf{\Let{\px}{\pe_1}{\pe_2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{letrec}~ρ'. & \pa = hash(π_i^+) \\
                        & ρ' = ρ ⊔ [\px ↦ memo(\pa,\pe_1,\seminf{\pe_1}_{ρ'})] \\
      \text{in}         & (\step{\BindA}{\pe_2} \fcomp \seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
 \end{array} \\
\end{array}\]
\caption{Stateless Maximal Trace Semantics}
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
%   * CESK semantics does have update frames and we want to match those
%     rather simply. It is a matter of producing "complete" states, see
%     "Which info do we need to attach to an action?"
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
% call-by-value.
%
% So we are stuck with value actions. Still, we could decide to return the
% value "out of band", in a pair, T+ -> (V, T+∞). That yields the worse of
% both worlds; the definition is similar to T+ -> T+∞ but we often need to
% adjust the second component of the pair; plus, in `memo`, we still have
% to "execute" the semantics S for its value, because we can't recover it
% from the trace.
%
% Which info do we need to attach to an action?
% ---------------------------------------------
% TLDR; that is determined by transition semantics that we want to
% be to abstract a trace into. The reasoning is as follows:
%
%   * "The transition semantics" is really the semantics we get by
%     applying the transition abstraction α_τ to a *stateful* trace
%     semantics, where the states capture enough information for
%     the resulting transition system to become deterministic.
%     (The transition system we get by abstracting the *stateless* trace
%     semantics isn't very useful precisely for that reason; taking
%     labels as state yields too many spurious transitions.)
%   * So determinism of the abstracted transition system is a quality
%     of the semantic richness of states (given that the sequence of states
%     is fixed); let's call state structure that allows for deterministic
%     abstraction "complete"
%   * (Are all complete state structures isomorph? Probably not)
%   * The stateful trace semantics is an abstraction of the stateless trace
%     semantics by way of α_S. We want to produce (at least one) stateful
%     semantics where the state space is complete. To produce such states, the
%     necessary information must be part of the stateless trace, otherwise we
%     can't write the abstraction function from stateless to stateful.
%
% So given the completeness of the states produced by α_S as a goal, we can
% make the following claims for action kinds in a trace:
%
%   * AppI, AppE, Lookup, Bind are all necessary actions because they make
%     a step from one label to a label of a subexpression.
%   * Val actions are the trace semantics' means of communicating a successful
%     (e.g., not stuck) execution as well as playing the role of `Just value`.
%     They correspond to Val transtitions in CESK or STG's ReturnCon
%   * We do *not* strictly need Update actions -- we just need update frames
%     in the stateful trace, but those could be reconstructed from when a
%     Lookup's balanced trace ended. Update actions make our life simpler in
%     other ways, though: See "The need for an update action".
%
% In fact, given that each action corresponds to a CESK transition, α_S can be
% defined inductively (by prefixes) on actions and states:
%
%   * The data on actions is simply erased and the corresopnding CESK transition
%     is taken. (Vital to realise that a well-formed stateless trace results in
%     an ok stateful trace.)
%   * For the state after prefix π, we simply call \varrho(π). It is a function
%     that Cousot uses throughout his book, and so should we.
%
% Now as to what information we need on the actions:
%
%   * AppI: We need the Var so that α_S can produce an Apply frame
%   * AppE: We need both the Var *and* the D so that varrho can produce the
%           proper environment.
%   * Lookup: We need the address so that we can push an update frame in α_S.
%             Also we need it to find the corresponding Bind.
%   * Bind: We need the address, so α_S can find it when encountering a Lookup
%           at that address. Then we also need the Var and the D for varrho.
%   * Update: The address is convenient (as are update actions to begin with),
%             otherwise we'd have to fiddle with balanced traces in memo to find
%             the corresponding Lookup.
%   * Values: It is convenient to attach values to Val actions; this is not strictly
%     necessary, just convenient. (See page 4 of 61e6f8a, quite ugly.)

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{\States} : ((\Var \pfun \MaxD) \to \MaxD) \to \StateD } } \\
  \\[-0.5em]
  α^{\States}(S)(σ) & = &
  \\
 \end{array}
\end{array}\]
\caption{Prefix Trace Abstraction}
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
  cons(a,\lbl,S)(π_i^+)   = \{\; tgt(π_i^+) \act{a} π_o \mid π_o ∈ S(π_i^+ \act{a} \lbl) \;\} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Bot}]
    {\quad}
    {tgt(π) ∈ \sempref{\slbl \pe}_ρ(π)}
  \qquad
  \inferrule*[right=\textsc{Var}]
    {π_c ∈ ρ(\px)(π_i^+)}
    {π_c ∈ \sempref{\slbl \px}_ρ(π_i^+)} \\
  \\[-0.5em]
  \inferrule*[right=\textsc{Let}]
    {   ρ' = \lfp(λρ'. ρ ⊔ [\px ↦ cons(\LookupA(hash(π_i^+)),\atlbl{\pe_1},\sempref{\pe_1}_{ρ'})])
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
  \seminf{K~\many{\px}}_ρ(π_i^+) & = & K~\many{\px} \act{\ValA(\ConV(K,\many{ρ(\px)}))} \return \\
  \\[-0.5em]
  \seminf{\Case{\pe_s}{\Sel}}_ρ(π_i^+) & = & π_s \concat \begin{cases}
      Rhs(K,\many{d})(π_i^+ \concat π_s) & \text{if $\getval{π_s}{\ConV(K,\many{d})}$}  \\
      \bot(π_i^+ \concat π_s) & \text{otherwise}  \\
    \end{cases} \\
    & & \text{where} \begin{array}{lcl}
                       π_s & = & cons( \CaseIA, \pe_s,\seminf{\pe_s}_ρ)(π_i^+) \\
                       Rhs(K,\many{d}) & = & cons(\CaseEA,\pe_K,\seminf{\pe_K}_{ρ[\many{\px↦d}]}) \\
                     \end{array} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Algebraic data types in Structural Maximal Trace Semantics}
  \label{fig:semantics}
\end{figure}
