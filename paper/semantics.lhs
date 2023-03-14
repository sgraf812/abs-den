\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}    & \px,\py,\pz & ∈ & \Var        &     & \\
  \text{Values}    &         \pv & ∈ & \Val        & ::= & \Lam{\px}{\pe} \\
  \text{Expressions}  &         \pe & ∈ & \Exp        & ::= & \slbl \px \mid \slbl \pv \mid \slbl \pe~\px \mid \slbl \Let{\px}{\pe_1}{\pe_2} \\
  \text{Addresses}    &         \pa & ∈ & \Addresses  &  ⊆  & ℕ \\
  \\
  \text{Actions} & a & ∈ & \Actions & ::=  & \AppIA \mid \AppEA \mid \LookupA(\pa) \mid \BindA \mid \ValA(v) \\
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
 \\[-0.5em]
 \ruleform{hash : \Traces^+ \to \Addresses} \quad \text{an injective function on the number of $\BindA$ actions in the trace} \\
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

% Note [On the role of labels]
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% Simon does not like program labels; he'd much rather just talk about
% the expressions those labels are attached to. Yet it is important for
% the simplicity of analyses *not* to identify structurally equivalent
% sub-expressions, example below.
%
% Our solution is to assume that every expression is implicitly labelled
% (uniquely, so). When we use the expression as an index, we implicitly use the
% label as its identity rather than its structure. When labels are explicitly
% required, we can obtain them via the at() function.
%
% When do we *not* want structural equality on expressions? Example:
%
%   \g -> f a + g (f a)
%
% Now imagine that given a call to the lambda with an unknown `g`, we'd like to
% find out which subexpressions are evaluated strictly. We could annotate our
% AST like this
%
%   \g -> ((f^S a^L)^S + (g (f^L a^L)^L)^S)^S
%
% Note how the two different occurrences of `f a` got different annotations.
%
% For obvious utility (who wants to redefine the entire syntax for *every*
% analysis?), we might want to maintain the analysis information *outside* of
% the syntax tree, as a map `Expr -> Strictness`. But doing so would conflate
% the entries for both occurrences of `f a`! So what we rather do is assume
% that every sub-expression of the syntax tree is labelled with a unique token
% l∈Label and then use that to maintain our external map `Label -> Strictness`.
%
% We write ⌊Expr⌋ to denote the set of expressions where labels are "erased",
% meaning that structural equivalent expressions are identified.
% The mapping `Label -> Expr` is well-defined and injective; the mapping
% `Label -> ⌊Expr⌋` is well-defined and often *not* injective.
% Conversely, `at : Expr -> Label` extracts the label of an expression, whereas
% `⌊Expr⌋ -> Label` is not well-defined.
%
% Note that as long as a function is defined by structural recursion over an
% expression, we'll never see two concrete, structurally equivalent expressions,
% so it's OK to omit labels and use the expression we recurse over (and its immediate
% subexpressions captured as meta variables) as if it contained the omitted labels.

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var \pfun \MaxD) → \MaxD } } \\
  \\[-0.5em]
  \bot(π_i^+)   & = & dst(π_i^+) \text{ is the bottom element of $\MaxD$} \\
  \\[-0.5em]
  \stepm{p}{a}{\pe}(π_i^+)   & = & \begin{cases}
    dst(π_i^+) \act{a} \pe & \text{if $dst(π_i^+)$ matches $p$} \\
    \bot(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  (d_1 \fcomp d_2)(π_i^+)   & = & d_1(π_i^+) \concat d_2(π_i^+ \concat d_1(π_i^+)) \\
  \\[-0.5em]
  \seminf{\pe}_ρ    (π_i^+)   & = & \bot(π_i^+) \qquad \text{if $dst(π_i^+) \not= \pe$} \\
  \\[-0.5em]
  \seminf{\px}_ρ              & = & ρ(\px) \\
  \\[-0.5em]
  \seminf{\Lam{\px}{\pe}}_ρ & = &
    \begin{letarray}
      \text{let} & f = d ↦ \stepm{\ddagger}{\AppEA}{\pe} \fcomp \seminf{\pe}_{ρ[\px↦d]} \\
      \text{in}  & \step{\ValA(\FunV(f))}{\ddagger} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & apply(π_e^+) = \begin{cases}
                     f(ρ(\px))(π_e^+) & \text{if $\getval{π_e^+}{\FunV(f)}$}  \\
                     \bot(π_e^+) & \text{otherwise}  \\
                   \end{cases} \\
      \text{in}  & \ternary{\px ∈ \dom(ρ)}{\step{\AppIA}{\pe} \fcomp \seminf{\pe}_ρ \fcomp apply}{\bot} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\Let{\px}{\pe_1}{\pe_2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{letrec}~ρ'. & \pa = hash(π_i^+) \\
                        & ρ' = ρ ⊔ [\px ↦ \step{\LookupA(\pa)}{\pe_1} \fcomp \seminf{\pe_1}_{ρ'}] \\
      \text{in}         & (\step{\BindA}{\pe_2} \fcomp \seminf{\pe_2}_{ρ'})(π_i^+)
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
  \seminf{K~\many{\px}}_ρ(π_i^+) & = & K~\many{\px} \act{\ValA(\ConV(K,\many{ρ(\px)}))} \ddagger \\
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

\cleardoublepage

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Actions}      &     a & ∈ & \Actions & ::=       & \ldots \mid \UpdateA(\pa) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \seminf{\wild} \colon \Exp → (\Var → \MaxD) → \MaxD } } \\
  \\[-0.5em]
  π_s \subtrceq π & = & \exists π_1, π_2.\ π = π_1 \concat π_s \concat π_2  \\
  \\[-0.5em]
  μ(π_i^+)(\pa) & = & \begin{cases}
    (\pv, v) & \text{if $\pv \act{\ValA(v)} \ddagger \left(\act{\UpdateA(\wild)} \ddagger \right)^* \act{\UpdateA(\pa)} \ddagger \subtrceq π_i^+$} \\
    undefined & \text{otherwise} \\
  \end{cases}  \\
  \\[-0.5em]
  memo(\pa,\pe,d)(π_i^+)   & = & \begin{cases}
    dst(π_i^+) \act{\LookupA(\pa)} \pv \act{\ValA(v)} \ddagger \act{\UpdateA(\pa)} \ddagger & \text{if $μ(π_i^+)(\pa) = (\pv,v)$} \\
    (\step{\LookupA(\pa)}{\pe} \fcomp d \fcomp \stepm{\ddagger}{\UpdateA(\pa)}{\ddagger})(π_i^+) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \seminf{\Let{\px}{\pe_1}{\pe_2}}_ρ(π_i^+) & = &
    \begin{letarray}
      \text{letrec}~ρ'. & \pa = hash(π_i^+) \\
                        & ρ' = ρ ⊔ [\px ↦ \highlight{memo(\pa,\pe_1,\seminf{\pe_1}_{ρ'})}] \\
      \text{in}         & (\step{\BindA}{\pe_2} \fcomp \seminf{\pe_2}_{ρ'})(π_i^+)
    \end{letarray} \\
  \\
  \multicolumn{3}{l}{\text{(Unchanged call-by-name equations:)}} \\
  \\[-0.5em]
  \seminf{\pe}_ρ    (π_i^+)   & = & \bot(π_i^+) \qquad \text{if $dst(π_i^+) \not= \pe$} \\
  \\[-0.5em]
  \seminf{\px}_ρ              & = & ρ(\px) \\
  \\[-0.5em]
  \seminf{\Lam{\px}{\pe}}_ρ & = &
    \begin{letarray}
      \text{let} & f = d ↦ \stepm{\ddagger}{\AppEA}{\pe} \fcomp \seminf{\pe}_{ρ[\px↦d]} \\
      \text{in}  & \step{\ValA(\FunV(f))}{\ddagger} \\
    \end{letarray} \\
  \\[-0.5em]
  \seminf{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & apply(π_e^+) = \begin{cases}
                     f(ρ(\px))(π_e^+) & \text{if $\getval{π_e^+}{\FunV(f)}$}  \\
                     \bot(π_e^+) & \text{otherwise}  \\
                   \end{cases} \\
      \text{in}  & \ternary{\px ∈ \dom(ρ)}{\step{\AppIA}{\pe} \fcomp \seminf{\pe}_ρ \fcomp apply}{\bot} \\
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
  \text{Variables}    & \px,\py,\pz & ∈ & \Var        &     & \\
  \text{Values}    &         \pv & ∈ & \Val        & ::= & \Lam{\px}{\pe} \\
  \text{Expressions}  &         \pe & ∈ & \Exp        & ::= & \slbl \px \mid \slbl \pv \mid \slbl \pe~\px \mid \slbl \Let{\px}{\pe_1}{\pe_2} \\
  \text{Addresses}    &         \pa & ∈ & \Addresses  &  ⊆  & ℕ \\
  \\
  \text{States}                             & σ      & ∈ & \States  & = & \Control \times \Environments \times \Heaps \times \Continuations \\
  \text{Control}                            & γ      & ∈ & \Control & = & \Exp ∪ (\Val \times \Values^\States) \\
  \text{Environments}                       & ρ      & ∈ & \Environments & = & \Var \pfun \Addresses \\
  \text{Heaps}                              & μ      & ∈ & \Heaps & = & \Addresses \pfun \Exp \times \Environments \times \StateD \\
  \text{Continuations}                      & κ      & ∈ & \Continuations & ::= & \StopF \mid \ApplyF(\pa) \pushF κ \mid \UpdateF(\pa) \pushF κ \\
  \\[-0.5em]
  \text{Stateful traces}                    & π      & ∈ & \STraces  & ::=_\gfp & σ\straceend \mid σ; π \\
  \text{Domain of stateful trace semantics} & d      & ∈ & \StateD  & = & \States \to \STraces \\
  \text{Values}                             & v      & ∈ & \Values^\States & ::= & \FunV(\Addresses \to \StateD) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src_\States(π) = σ \qquad dst_\States(π) = σ } } \\
  \\[-0.5em]
  src_\States(σ\straceend)    & = & σ \\
  src_\States(σ; π) & = & σ \\
  \\[-0.5em]
  dst_\States(π)    & = & \begin{cases}
    undefined & \text{if $π$ infinite} \\
    σ         & \text{if $π = ...; σ \straceend$}
  \end{cases} \\
 \end{array} \quad
 \begin{array}{c}
  \ruleform{ π_1 \sconcat π_2 = π_3 } \\
  \\[-0.5em]
  π_1 \sconcat π_2 = \begin{cases}
    σ; (π_1' \sconcat π_2) & \text{if $π_1 = σ; π_1'$} \\
    π_2                    & \text{if $π_1 = σ\straceend$ and $src_\States(π_2) = σ$} \\
    undefined              & \text{if $π_1 = σ\straceend$ and $src_\States(π_2) \not= σ$} \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ σ_1 \smallstep σ_2 \qquad \validtrace{π} } \\
  \\[-0.5em]
  \inferrule*
    [right=$\ValueT$]
    {\quad}
    {(\pv, ρ, μ, κ) \smallstep ((\pv, v), ρ, μ, κ)}
  \qquad
  \inferrule*
    [right=$\LookupT$]
    {\pa = ρ(\px) \quad (\pe,ρ',\wild) = μ(\pa)}
    {(\px, ρ, μ, κ) \smallstep (\pe, ρ', μ, \UpdateF(\pa) \pushF κ)}
  \\
  \inferrule*
    [right=$\UpdateT$]
    {\quad}
    {((\pv,v), ρ, μ, \UpdateF(\pa) \pushF κ) \smallstep ((\pv,v), ρ, μ[\pa ↦ (\pv,ρ,d)], κ)} \\
  \\[-0.5em]
  \inferrule*
    [right=$\AppIT$]
    {\pa = ρ(\px)}
    {(\pe~\px,ρ,μ,κ) \smallstep (\pe,ρ,μ,\ApplyF(\pa) \pushF κ)}
  \quad
  \inferrule*
    [right=$\AppET$]
    {\quad}
    {((\Lam{\px}{\pe},\wild),ρ,μ, \ApplyF(\pa) \pushF κ) \smallstep (\pe,ρ[\px ↦ \pa],μ,κ)} \\
  \\[-0.5em]
  \inferrule*
    [right=$\LetT$]
    {\fresh{\pa}{μ} \quad ρ' = ρ[\px↦\pa]}
    {(\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) \smallstep (\pe_2,ρ',μ[\pa↦(\pe_1,ρ',d_1)], κ)} \\
  \\
  \\
  \inferrule*
    {\quad}
    {\validtrace{σ\straceend}}
  \qquad
  \inferrule*
    {σ \smallstep src_\States(π) \quad \validtrace{π}}
    {\validtrace{σ; π}} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Call-by-need CESK transition system $\smallstep$}
  \label{fig:cesk-syntax}
\end{figure}

% Note [The use of a CESK trace semantics]
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% Why is CESK trace semantics useful?
%
% 1. Its transition semantics (derivable by typical transition system
%    abstraction function) *is* CESK, if you leave out the denotational stuff!
%    An ideal test bed for a bisimulation proof.
% 2. It is generated by a compositional function
% 3. Conjecture: We can provide order isos to any other useful trace semantics
%
% Note [Influences on the semantics]
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%   * It's a lazy semantics in ANF, hence inspired by Sestoft's Mark II machine
%   * The Val transition is key to line up with the trace-based semantics and is
%     inspired by CESK's \ddagger as well as STG's ReturnCon code.
%

\FloatBarrier

\subsection{Informal Specification}

Let us start with an informal specification: Our goal is to give a
structural definition of a function $\semst{\pe}$ that produces a denotation
$d ∈ \StateD$ of $\pe$, with the following properties: For every CESK state $σ$
where the control is $\pe$, $d(σ)$ is a trace in the transition system
$\smallstep$ with $σ$ as its source state. In itself, that is a trivial
specification, because $d(σ) = σ \straceend$ is a valid but hardly
useful model. So we refine: Every such trace $d(σ)$ must follow the evaluation
of $\pe$. For example, given a (sub-)expression $\Lam{x}{x}$ of
some program $\pe$, we expect the following equation:
\[
  \semst{\Lam{x}{x}} (\Lam{x}{x}, ρ, μ, κ) = (\Lam{x}{x}, ρ, μ, κ); ((\Lam{x}{x},\FunV(f)), ρ, μ, κ) \straceend
\]
Note that even if $κ$ had an apply frame on top, we require $\semst{\wild}$ to
stop after the value transition. In general, each intermediate continuation
$κ_i$ in the produced trace will be an extension of the first $κ$, so
$κ_i = ... \pushF κ$. We call traces with this property \emph{balanced}, as in
\cite{sestoft}.

Why produce balanced traces rather than letting the individual traces eat their
evaluation contexts to completion? Ultimately, we think it is just a matter of
taste, but certainly it's simpler to identify and talk about the \emph{semantic
value} of $\Lam{x}{x}$ this way: It is always the second component of the final
state's control (if it exists), and the semantic value determines how evaluation
continues.

Unsurprisingly, the semantic value of $\Lam{x}{x}$ is a $\FunV(f)$-value, the
$f$ of which will involve the semantics of the sub-program $\semst{x}$. The
transition semantics is indifferent to which semantic value is put in the control,
but for $\semst{\wild}$ we specify that $f$ continues where our balanced trace
left off. More precisely, we expect the $f$ in a semantic value $\FunV(f)$ to
closely follow β-reduction of the syntactic value $\Lam{x}{x}$ with the address
of the argument variable $\pa$, as follows
\[
  f(\pa)((\Lam{x}{x},\FunV(f)), ρ, μ, \ApplyF(\pa) \pushF κ) = ((\Lam{x}{x},\FunV(f)), ρ, μ, \ApplyF(\pa) \pushF κ); \semst{x}(x, ρ[x ↦ \pa], μ, κ)
\]
That is, semantic values pop exactly one frame from the continuation
and then produce another balanced trace of the redex. This statement extends
to other kinds of values such as data constructors, as we shall see in
\cref{ssec:adts}.

There is another occurrence of semantic denotations $d$ in the heap that is
uninstantiated by the transition system. If $(\pa ↦ (\pe, ρ, d)) ∈ μ$, then we
specify that $d = \semst{\pe}$. Since $\UpdateT$ modifies heap entries,
the corresponding denotation $d$ of the heap entry will have to be updated
accordingly to maintain this invariant.

Finally, it is a matter of good hygiene that $\semst{\pe}$ continues \emph{only}
those states that have $\pe$ as control; it should produce a singleton trace on
any other expression of the program, indicating stuck-ness. So even if $x~x$ and
$y~y$ both structurally are well-scoped application expressions,
$\semst{x~x}(y~y,ρ,μ,κ) = (y~y,ρ,μ,κ)\straceend$. In other words, if $(\pe_i)_i$
enumerates the sub-expressions of a program $\pe$, then for every state
$σ$ that is not stuck in the transition semantics, there is at most one function
$\semst{\pe_i}$ that is not stuck on $σ$.%
\footnote{Particularly peculiar is the situation where two distinctly labelled
sub-expressions of the program share the same erasure. \sg{Give an example here?
Perhaps earlier, where we'll discuss labels.}}

\subsection{Formal Specification}

A stuck trace is one way in which $\semst{\wild}$ does not \emph{always} return
a balanced trace. The other way is when the trace diverges before yielding to
the initial continuation. We call a trace \emph{maximally-balanced} if it is a
valid CESK trace and falls in either of the three categories. More precisely:

\begin{definition}[Non-retreating and maximally-balanced traces]\ \\
  A CESK trace $π = (e_1,ρ_1,μ_1,κ_1); ... (e_i,ρ_i,μ_i,κ_i); ... $ is
  \emph{non-retreating} if
  \begin{itemize}
    \item $\validtrace{π}$, and
    \item Every intermediate continuation $κ_i$ extends $κ_1$ (so $κ_i = κ_1$ or $κ_i = ... \pushF κ_1$)
  \end{itemize}
  A non-retreating CESK trace $π$ is \emph{maximally-balanced} if it is either
  infinite or there is no $σ$ such that $π \sconcat (dst_\States(π); σ \straceend)$
  is non-retreating.
  We notate maximally-balanced traces as $\maxbaltrace{π}$.
\end{definition}

\begin{lemma}[Extension relation on continuations is prefix order]
  The binary relation on continuations
  \[
    (\contextendsflipped) = \{ (κ_1,κ_2) ∈ \Continuations \times \Continuations \mid \text{$κ_2 = κ_1$ or $κ_2 = ... \pushF κ_1$} \}
  \]
  is a prefix order.
\end{lemma}
\begin{proof}
  $(\contextendsflipped)$ is isomorphic to the usual prefix order on strings
  over the alphabet of continuation frames.
\end{proof}

\begin{definition}[Return and evaluation states]
  $σ$ is a \emph{return state} if its control is of the form $(\pv, v)$.
  Otherwise, the control is of the form $\pe$ and $σ$ is an \emph{evaluation} state.
\end{definition}

The final states of the CESK semantics are the return states with a $\StopF$
continuation.
A state $σ$ that cannot make a step (so there exists no $σ'$ such that $σ
\smallstep σ'$) and is not a final state is called \emph{stuck}.

\begin{example}[Stuck]
  \label{ex:stuck}
  The following trace is stuck because $x$ is not in scope:
  \[
    \semst{x~y}(x~y,[y↦\pa], [\pa↦...], κ) = (x~y,[y↦\pa], [\pa↦...], κ); (x,[y↦\pa], [\pa↦...], \ApplyF(\pa) \pushF κ)\straceend
  \]
\end{example}

A trace is stuck if its destination state is stuck.

\begin{lemma}[Characterisation of destination states of maximally-balanced traces]
  Let $π$ be a non-retreating trace. Then, $π$ is maximally-balanced if and
  only if
  \begin{itemize}
    \item $π$ is infinite, or
    \item $π$ is stuck, or
    \item $π$ is \emph{balanced}, meaning that $dst_\States(π)$ is a return
          state, the continuation of which is that of the initial state
          $src_\States(π)$.
  \end{itemize}
\end{lemma}
\begin{proof}
  =>:
  Let $π$ be maximally-balanced.
  If $π$ is infinite or stuck, we are done; so assume that $π$ is finite and not
  stuck. Let $σ_1 = src_\States(π)$, $σ_n = dst_\States(π)$ and let $κ_1$ denote
  the continuation of $σ_1$ and $κ_n$ that of $σ_n$.
  Our goal is to show that $κ_n = κ_1$ and that $σ_n$ is a return state.

  If $σ_n$ is a final state, then clearly $σ_n$ is a return state with $κ_n =
  \StopF = κ_1$, where the latter equality follows from $π$ non-retreating
  and the fact that $\StopF$ is the unique minimal element of
  $(\contextendsflipped)$.

  Now assume that $σ_n$ is neither stuck nor final.
  Then there is $σ_{n+1}$ such that $σ_n \smallstep σ_{n+1}$; let $π' = π
  \sconcat (σ_n; σ_{n+1} \straceend)$ be the continued trace.
  $π'$ forms a valid CESK trace, but since $π$ is maximally-balanced, it can't
  be non-retreating.
  Hence the continuation $κ_{n+1}$ of $σ_{n+1}$ cannot be an extension of $κ_1$,
  so $κ_{n+1} \not\contextends κ_1$.
  On the other hand, $κ_n \contextends κ_1$ because $π$ is non-retreating.

  We proceed by cases over $σ_n \smallstep σ_{n+1}$:
  \begin{itemize}
    \item \textbf{Case} $\ValueT$, $\LookupT$, $\AppIT$, $\LetT$:
      These are all non-retreating transitions, so
      $κ_{n+1} \contextends κ_n \contextends κ_1$; contradiction.
    \item \textbf{Case} $\UpdateT$, $\AppET$:
      In both cases we see that $σ$ is a return state and
      we have $κ_n \contextends κ_{n+1}$.

      But we also have $κ_n \contextends κ_1$ and by downward totality of the
      prefix order $(\contextendsflipped)$, we must have either $κ_{n+1}
      \contextends κ_1$ or $κ_1 \contextends κ_{n+1}$. The former leads to a
      contradiction, hence we have $κ_n \contextends κ_1 \contextendsstrict
      κ_{n+1}$, and the first inequality must be an equality because the
      difference between $κ_n$ and $κ_{n+1}$ is just a single frame.
  \end{itemize}
  <=: TODO
\end{proof}

In other words, a trace is maximally-balanced if it follows the transition
semantics, never leaves the initial evaluation context and is either infinite,
stuck, or successfully returns a value to its initial evaluation context.
The latter case intuitively corresponds to the existence of derivation in a
suitable big-step semantics.

For the initial state with an empty stack, the maximally-balanced trace is
exactly the result of running the transition semantics to completion.

Unsurprisingly, infinite traces are never stuck or balanced.
We could also show that no balanced trace is ever stuck, thus proving the three
categories disjoint. Unfortunately, the introduction of algebraic data types
gives rise to balanced but stuck traces, so we won't make use of that fact in
the theory that follows.

\Cref{ex:stuck} gives an example program that is stuck because of an
out-of-scope reference. This is in fact the only way in which our simple lambda
calculus without algebraic data types can get stuck; it is useful to limit such
out-of-scope errors to the lookup of program variables in the environment $ρ$
and require that lookups in the heap $μ$ are always well-defined, captured in
the following predicate:

\begin{definition}[Well-addressed]
  We say that
  \begin{itemize}
    \item An environment $ρ$ is \emph{well-addressed} \wrt
          a heap $μ$ if $\rng(ρ) ⊆ \dom(μ)$.
    \item A continuation $κ$ is \emph{well-addressed} \wrt
          a heap $μ$ if $\fa(κ) ⊆ \dom(μ)$, where
          \[\begin{array}{rcl}
            \fa(\ApplyF(\pa) \pushF κ) & = & \{ \pa \} ∪ \fa(κ) \\
            \fa(\UpdateF(\pa) \pushF κ) & = & \{ \pa \} ∪ \fa(κ) \\
            \fa(\StopF) & = & \{ \} \\
          \end{array}\]
    \item A heap $μ$ is \emph{well-addressed} if, for every entry $(\wild,ρ,\wild) ∈ μ$,
          $ρ$ is well-addressed \wrt $μ$.
    \item A state $(\wild, ρ, μ, κ)$ is \emph{well-addressed} if $ρ$
          and $κ$ are well-addressed with respect to $μ$.
  \end{itemize}
\end{definition}

\begin{lemma}[Transitions preserve well-addressedness]
  \label{lemma:preserve-well-addressed}
  Let $σ$ be a well-addressed state. If there exists $σ'$ such that $σ
  \smallstep σ'$, then $σ'$ is well-addressed.
\end{lemma}
\begin{proof}
  By cases over the transition relation.
\end{proof}

\begin{corollary}
  If $\validtrace{π}$ and $src_\States(π)$ is well-addressed, then every state
  in $π$ is well-addressed.
\end{corollary}

For $\semst{\wild}$ to continue a well-addressed state sensibly, we need to
relate the occurring denotations to their respective syntactic counterparts:

\begin{definition}[Well-elaborated]
  We say that a well-addressed state $σ$ is \emph{well-elaborated}, if
  \begin{itemize}
    \item For every heap entry $(\pe, ρ, d) ∈ \rng(μ)$, where $μ$ is the heap of
          $σ$, we have $d=\semst{\pe}$.
    \item If $σ$ is a return state with control $(\Lam{\px}{\pe}, \FunV(f))$,
          then for any state $σ'$ of the form $((\Lam{\px}{\pe}, \FunV(f)), ρ, μ, \ApplyF(\pa) \pushF κ)$,
          we have $f(\pa)(σ') = σ'; \semst{\pe}(\pe, ρ[\px ↦ \pa], μ, κ)$.
  \end{itemize}
\end{definition}
The initial state of $\smallstep$, $(\pe,[],[],\StopF)$, is well-elaborated,
because it is never a return state and its heap is empty.

Finally, we can give the specification for $\semst{\wild}$:

\begin{definition}[Specification of $\semst{\wild}$]
\label{defn:semst-spec}
Let $σ$ be a well-elaborated state and $\pe$ an arbitrary expression. Then
\begin{itemize}
  \item[(S1)] If the control of $σ$ is not $\pe$, then $\semst{\pe}(σ) = σ \straceend$.
  \item[(S2)] $σ$ is the source state of the trace $\semst{\pe}(σ)$.
  \item[(S3)] If the control of $σ$ is $\pe$, then
              $\maxbaltrace{\semst{\pe}(σ)}$ and all states in the trace
              $\semst{\pe}(σ)$ are well-elaborated.
\end{itemize}
\end{definition}
% Urgh, flesh it out when we know better what to do with S1-S3
%The purpose of $(S1)$ is to guarantee that $\semst{\pe}$ does not continue:
%to make the mapping $\pe \mapsto \semst{\pe}$ injective
%and thus invertible.
%\begin{lemma}
%  Let $E$ denote the set of the expression $\pe$ and its (labelled)
%  sub-expressions. Then the mapping $\fn{\pe}{\semst{\pe}}$ is injective.
%\end{lemma}
%\begin{proof}
%  It is simple to see that for every $\pe$ there exists $σ, σ'$ such that $\pe$
%  is the control of $σ$ and $σ \smallstep σ'$.
%  \sg{Do we need to prove this? I think not.}
%  Let $s(\pe)$ denote this state.
%  Then $\semst{\pe}(s(\pe)) \not= \semst{\pe'}(s(\pe))$ unless $\pe = \pe'$:
%
%\end{proof}
%Clearly, $(S3)$ is the key property for adequacy, but we can't prove it without
%the other 2 properties.

\subsection{Definition}

\Cref{fig:cesk-semantics} defines $\semst{\wild}$. Before we prove that
$\semst{\wild}$ satisfies the specification in \Cref{defn:semst-spec},
let us understand the function by way of evaluating the example program
$\pe \triangleq \Let{i}{\Lam{x}{x}}{i~i}$:
\[\begin{array}{l}
  \newcommand{\myleftbrace}[4]{\draw[mymatrixbrace] (m-#2-#1.west) -- node[right=2pt] {#4} (m-#3-#1.west);}
  \begin{tikzpicture}[baseline={-0.5ex},mymatrixenv]
      \matrix [mymatrix] (m)
      {
        1  & (\pe, [], [], \StopF); & \hspace{3.5em} & \hspace{3.5em} & \hspace{3.5em} & \hspace{4.5em} & \hspace{7.5em} \\
        2  & (i~i, ρ_1, μ, \StopF); & & & & & \\
        3  & (i, ρ_1, μ, κ_1); & & & & & \\
        4  & (\Lam{x}{x}, ρ_1, μ, κ_2); & & & & & \\
        5  & ((\Lam{x}{x}, \FunV(f)), ρ_1, μ, κ_2); & & & & & \\
        6  & ((\Lam{x}{x}, \FunV(f)), ρ_1, μ, κ_1); & & & & & \\
        7  & (x, ρ_2, μ, \StopF); & & & & & \\
        8  & (\Lam{x}{x}, ρ_1, μ, κ_3); & & & & & \\
        9  & ((\Lam{x}{x}, \FunV(f)), ρ_1, μ, κ_3); & & & & & \\
        10 & ((\Lam{x}{x}, \FunV(f)), ρ_1, μ, \StopF) \straceend & & & & & \\
      };
      % Braces, using the node name prev as the state for the previous east
      % anchor. Only the east anchor is relevant
      \foreach \i in {1,...,\the\pgfmatrixcurrentrow}
        \draw[dotted] (m.east||-m-\i-\the\pgfmatrixcurrentcolumn.east) -- (m-\i-2);
      \myleftbrace{3}{1}{10}{$\semst{\pe}$}
      \myleftbrace{4}{1}{2}{$let(\semst{\Lam{x}{x}})$}
      \myleftbrace{4}{2}{10}{$\semst{i~i}$}
      \myleftbrace{5}{2}{3}{$app_1(i~i)$}
      \myleftbrace{5}{3}{6}{$\semst{i}$}
      \myleftbrace{5}{6}{7}{$app_2(\Lam{x}{x},\pa_1)$}
      \myleftbrace{5}{7}{10}{$\semst{x}$}
      \myleftbrace{6}{3}{4}{$look(i)$}
      \myleftbrace{6}{4}{5}{$\semst{\Lam{x}{x}}$}
      \myleftbrace{6}{5}{6}{$upd$}
      \myleftbrace{6}{7}{8}{$look(x)$}
      \myleftbrace{6}{8}{9}{$\semst{\Lam{x}{x}}$}
      \myleftbrace{6}{9}{10}{$upd$}
      \myleftbrace{7}{4}{5}{$ret(\Lam{x}{x},\FunV(f))$}
      \myleftbrace{7}{8}{9}{$ret(\Lam{x}{x},\FunV(f))$}
  \end{tikzpicture} \\
  \quad \text{where} \quad \begin{array}{ll}
  ρ_1 = [i ↦ \pa_1] & κ_1 = \ApplyF(\pa_1) \pushF \StopF \\
  ρ_2 = [i ↦ \pa_1, x ↦ \pa_1] & κ_2 = \UpdateF(\pa_1) \pushF κ_1 \\
  μ = [\pa_1 ↦ (\Lam{x}{x},ρ_1,\semst{\Lam{x}{x}})] & κ_3 = \UpdateF(\pa_1) \pushF \StopF \\
  f = \pa \mapsto step(app_2(\Lam{\px}{\px},\pa)) \sfcomp \semst{\px} \\
  \end{array} \\
\end{array}\]
The annotations to the right of the trace can be understood as denoting the
``call graph'' of the $\semst{\pe}$, with the primitive transition $step$s such
as $let_1$, $app_1$, $look$ \etc as leaves, each \emph{elaborating} the
application of the corresponding transition rule $\LetT$, $\AppIT$, $\LookupT$,
and so on, in the transition semantics with a matching denotation where
necessary.

Evaluation begins by decomposing the let binding and continuing the let body in
the extended environment and heap, transitioning from state 1 to state 2.
Beyond recognising the expected application of the $\LetT$ transition rule,
it is interesting to see that indeed the $d$ in the heap is elaborated to
$\semst{\Lam{x}{x}}$, which ends up in $ρ_1$.

The auxiliary $step$ function and the forward composition operator $\sfcomp$
have been inlined everywhere, as all steps and compositions are well-defined.
One can find that $\sfcomp$ is quite well-behaved: It forms a monoid with
$\bot_\StateD$ (which is just $step$ applied to the function that is undefined
everywhere) as its neutral element.

Evaluation of the let binding recurses into $\semst{i~i}$ on state 2,
where an $\AppIT$ transition to state 3, on which $\semst{i}$ is run.
Note that the final state 6 of the call to $\semst{i}$ will later be fed
(via $\sfcomp$) into the auxiliary function $apply$.

$\semst{i}$ guides the trace from state 3 to state 6, during which we
observe a heap update for the first time: Not only does $look$ look up
the binding $\Lam{x}{x}$ of $i$ in the heap and push and update frame,
it also hands over control to the $d = \semst{\Lam{x}{x}}$ stored alongside it.
(And we make a mental note to pick up with $step(upd)$ when $d$ has finished.)
Crucially, that happens without $\semst{\Lam{x}{x}}$ occurring in the definition
of $\semst{i}$, thus the definition remains structural.

By comparison, the value transition governed by $\semst{\Lam{x}{x}}$ from state
4 to 5 is rather familiar from our earlier example, where we specified more or
less the same $\FunV(f)$.

$\semst{\Lam{x}{x}}$ finishes in state 5, where $upd$ picks up to guide the
$\UpdateT$ transition. Crucially, it also updates the $d$ stored in the heap
so that its semantics matches that of the updated value; take note of the
similarity to the lambda clause in the definition of $\semst{\wild}$. Since
$\Lam{x}{x}$ was a value to begin with, there is no observable change to the
heap.

After $\semst{i}$ concludes in state 6, the $apply$ function from $\semst{i~i}$
picks up. Since $apply$ is defined on state 6, it reduces to $f(\pa_1)$%
\footnote{We omitted $apply$ and $f(\pa_1)$ from the call graph for space reasons, but
their activation spans from state 7 to the final state 10.}.
$f(\pa_1)$ will perform an $\AppET$ transition to state 7, binding $x$ to $i$'s
address $\pa_1$ and finally entering the lambda body $\semst{x}$. Since $x$ is
an alias for $i$, steps 7 to 10 just repeat the same same heap update sequence
we observed in steps 3 to 6.

It is useful to review another example involving an observable heap update.
The following trace begins right before the heap update occurs in
$\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$, that is, after reaching the value
in $\semst{(\Lam{y}{\Lam{x}{x}})~i}$:
\[\begin{array}{l}
  \newcommand{\myleftbrace}[4]{\draw[mymatrixbrace] (m-#2-#1.west) -- node[right=2pt] {#4} (m-#3-#1.west);}
  \begin{tikzpicture}[baseline={-0.5ex},mymatrixenv]
      \matrix [mymatrix] (m)
      {
        1  & ((\Lam{x}{x},\FunV(f)), ρ_2, μ_1, κ_2); & \hspace{3.5em} & \hspace{3.5em} & \hspace{4.5em} & \hspace{7.5em} \\
        2  & ((\Lam{x}{x},\FunV(f)), ρ_2, μ_2, κ_1); & & & & \\
        3  & (x, ρ_3, μ, \StopF); & & & & \\
        4  & (\Lam{x}{x}, ρ_2, μ, κ_3); & & & & \\
        5  & ((\Lam{x}{x}, \FunV(f)), ρ_2, μ, κ_3); & & & & \\
        6  & ((\Lam{x}{x}, \FunV(f)), ρ_1, μ, \StopF); & & & & \\
      };
      % Braces, using the node name prev as the state for the previous east
      % anchor. Only the east anchor is relevant
      \foreach \i in {1,...,\the\pgfmatrixcurrentrow}
        \draw[dotted] (m.east||-m-\i-\the\pgfmatrixcurrentcolumn.east) -- (m-\i-2);
      \myleftbrace{3}{1}{6}{$\semst{i~i}$}
      \myleftbrace{4}{1}{2}{$\semst{i}$}
      \myleftbrace{4}{2}{3}{$app_2(\Lam{x}{x},\pa_1)$}
      \myleftbrace{4}{3}{6}{$\semst{x}$}
      \myleftbrace{5}{1}{2}{$upd$}
      \myleftbrace{5}{3}{4}{$look(x)$}
      \myleftbrace{5}{4}{5}{$\semst{\Lam{x}{x}}$}
      \myleftbrace{5}{5}{6}{$upd$}
      \myleftbrace{6}{4}{5}{$ret(\Lam{x}{x},\FunV(f))$}
  \end{tikzpicture} \\
  \quad \text{where} \quad \begin{array}{ll}
  ρ_1 = [i ↦ \pa_1] & κ_1 = \ApplyF(\pa_1) \pushF \StopF \\
  ρ_2 = [i ↦ \pa_1, y ↦ \pa_1] & κ_2 = \UpdateF(\pa_1) \pushF κ_1 \\
  μ_1 = [\pa_1 ↦ ((\Lam{y}{\Lam{x}{x}})~i,ρ_1,\semst{(\Lam{y}{\Lam{x}{x}})~i})] & κ_3 = \UpdateF(\pa_1) \pushF \StopF \\
  μ_2 = [\pa_1 ↦ (\Lam{x}{x},ρ_2,\semst{\Lam{x}{x}})] & f = \pa \mapsto step(app_2(\Lam{\px}{\px},\pa)) \sfcomp \semst{\px} \\
  \end{array} \\
\end{array}\]
Note that both the environment \emph{and} the denotation in the heap is updated
in state 2, and that the new denotation is immediately visible on the next heap
lookup in state 3, so that $\semst{\Lam{x}{x}}$ takes control rather than
$\semst{(\Lam{y}{\Lam{x}{x}})~i}$, just as the transition system requires.

\subsection{Conformance}

Having a good grasp on the workings of $\semst{\wild}$ now, let us show that
$\semst{\wild}$ conforms to its specification in \Cref{defn:semst-spec}.

For the following three lemmas, let $σ$ denote a well-addressed state and $\pe$
an expression.

\begin{lemma}[(S1)]
  If the control of $σ$ is not $\pe$, then $\semst{\pe}(σ) = σ\straceend$.
\end{lemma}
\begin{proof}
  By the first clause of $\semst{\wild}$.
\end{proof}

\begin{lemma}[(S2)]
  $σ$ is the source state of $\semst{\pe}(σ)$.
\end{lemma}
\begin{proof}
  Trivial for the first clause of $\semst{\wild}$.
  Now, realising that $src_\States((l \sfcomp r)(σ)) = src_\States(l(σ))$
  and that $src_\States(step(f)(σ)) = σ$ for any $f$, we can see that the
  proposition follows for other clauses by applying these two rewrites to
  completion.
\end{proof}

\begin{lemma}[(S3)]
  If the control of $σ$ is $\pe$, then $\maxbaltrace{\semst{\pe}(σ)}$ and all
  states in the trace $\semst{\pe}(σ)$ are well-elaborated.
\end{lemma}
\begin{proof}
  Let us abbreviate the property of interest to
  \[
    OK(d) = ∀σ. σ\text{ well-addressed} \Longrightarrow \validtrace{d(σ)}
  \]
  Let $σ$ be a well-addressed state.
  For the first clause of $\semst{\wild}$, the proposition follows by
  $\validtraceTriv$.

  Every other clause of $\semst{\wild}$ is built from applications of
  $\sfcomp$, $step$ or $apply$ and it suffices to show that these combinators
  yield valid CESK traces when applied to $σ$.

  We can see that $OK(d_1 \sfcomp d_2)$ whenever $OK(d_1)$ and $OK(d_2)$ holds,
  because the destination state of $d_1(σ)$, if it exists, is well-addressed by
  \Cref{lemma:preserve-well-addressed} and $OK(d_2)$ can be usefully applied.
  An interesting case is when $d_1(σ)$ is infinite; then
  $(d_1 \sfcomp d_2)(σ) = d_1(σ)$ and $\validtrace{(d_1 \sfcomp d_2)(σ)}$ follows
  from $\validtrace{d_1(σ)}$.

  We can see that $\validtrace{step(f)(σ)}$ whenever $f(σ)$ is undefined
  (by $\validtraceTriv$) or $\validtrace{σ;f(σ)}$ (by $\validtraceTrans$).
  Enumerating the arguments to $step$, we can see that $val, upd, app_1, app_2$
  and $let$ follow $\ValueT, \UpdateT, \AppIT, \AppET$ and $\LetT$ closely by
  making exactly one transition. That leaves $loop$, which corresponds to doing
  one step with $\LookupT$ and then evaluating the heap-bound expression $\pe$
  as expressed by $d$.

  By (bi-)induction that is always the case.
\end{proof}

Let us begin by defining that a denotation $d$ is \emph{valid everywhere} when
for every initial $σ$, we have $\validtrace{σ}$. This definition lets us express
an important observation:

We can now formulate our correctness theorem as follows:

\begin{theorem}[Adequacy of the stateful trace semantics]
Let $d = \semst{\pe}$. Then for all $ρ,μ$ with $\vdash_\Heaps μ$, we have $μ
\vdash_\StateD \pe \sim_ρ d$.
\end{theorem}

\begin{corollary} Let $d = \semst{\pe}$. Then $π=d(\pe,[],[],\StopF)$ is a
maximally-balanced trace for the transition semantics starting at $(\pe,[],[],\StopF)$.
\end{corollary}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semst{\wild} \colon \Exp → \StateD } } \\
  \\[-0.5em]
  \bot_\StateD(σ) & = & \fn{σ}{σ\straceend} \\
  \\[-0.5em]
  (d_1 \sfcomp d_2)(σ) & = & d_1(σ) \sconcat d_2(dst_\States(d_1(σ))) \\
  \\[-0.5em]
  step(f)(σ) & = & \begin{cases}
    σ; f(σ)     & \text{if $f(σ)$ is defined} \\
    σ\straceend & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  val(\pv,v)(\pv,ρ,μ,κ) & = & ((\pv,v),ρ,μ,κ) \straceend \\
  \\[-0.5em]
  look(\px)(\px,ρ,μ,κ) & = &
    \begin{letarray}
      \text{let} & \pa = ρ(\px) \\
                 & (\pe,ρ',d) = μ(\pa) \\
      \text{in}  & d(\pe,ρ',μ,\UpdateF(\pa) \pushF κ) \\
    \end{letarray} \\
  \\[-0.5em]
  upd((\pv,v),ρ,μ,\UpdateF(\pa) \pushF κ) & = & ((\pv,v),ρ,μ[\pa ↦ (\pv,ρ,step(val(v)))], κ)\straceend \\
  \\[-0.5em]
  app_1(\pe~\px)(\pe~\px,ρ,μ,κ) & = & (\pe,ρ,μ,\ApplyF(ρ(\px)) \pushF κ)\straceend \\
  \\[-0.5em]
  app_2(\Lam{\px}{\pe},\pa)((\Lam{\px}{\pe},\FunV(\wild)),ρ,μ, \ApplyF(\pa) \pushF κ) & = & (\pe,ρ[\px ↦ \pa],μ,κ) \straceend \\
  \\[-0.5em]
  let(d_1)(\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) & = &
    \begin{letarray}
      \text{let} & ρ' = ρ[\px ↦ \pa] \quad \text{where $\fresh{\pa}{μ}$} \\
      \text{in}  & (\pe_2,ρ',μ[\pa ↦ (\pe_1, ρ', d_1)],κ)\straceend \\
    \end{letarray} \\
  \\[-0.5em]
  apply(σ) & = & \begin{cases}
    f(\pa)(σ) & \text{if $σ=((\wild,\FunV(f)),\wild,\ApplyF(\pa) \pushF \wild)$} \\
    σ \straceend & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  % We need this case, otherwise we'd continue e.g.
  %   S[x]((sv,v),ρ,μ,upd(a).κ) = ((sv,v),ρ,μ,upd(a).κ); ((sv,v),ρ,μ[a...],κ)
  % Because of how the composition operator works.
  \semst{\pe}(σ) & = & σ\straceend\ \text{if the control of $σ$ is not $\pe$} \\
  \\[-0.5em]
  \semst{\px} & = & step(look(\px)) \sfcomp step(upd) \\
  \\[-0.5em]
  \semst{\Lam{\px}{\pe}} & = & \begin{letarray}
    \text{let} & f = \pa \mapsto step(app_2(\Lam{\px}{\pe},\pa)) \sfcomp \semst{\pe} \\
    \text{in}  & step(val(\Lam{\px}{\pe},\FunV(f))) \\
  \end{letarray} \\
  \\[-0.5em]
  \semst{\pe~\px} & = & step(app_1(\pe~\px)) \sfcomp \semst{\pe} \sfcomp apply \\
  \\[-0.5em]
  \semst{\Let{\px}{\pe_1}{\pe_2}} & = & step(let(\semst{\pe_1})) \sfcomp \semst{\pe_2} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Structural call-by-need stateful trace semantics $\semst{-}$}
  \label{fig:cesk-semantics}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Liveness Domain} & d^{∃l} & ∈ & \LiveD & = & \poset{\Var} \times \Values^{∃l} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semlive{\wild} \colon \Exp → (\Var → \LiveD) → \LiveD } } \\
  \\[-0.5em]
  \bot_{∃l} & = & (\varnothing, \bot_{\Values^{∃l}}) \\
  \\[-0.5em]
  L_1 ∪_1 (L_2,v) & = & (L_1 ∪ L_2,v) \\
  \\[-0.5em]
  %L_1 \fcomp^l L_2 & = & α^{∃l}_φ(γ^{∃l}_φ(L_1) \fcomp γ^{∃l}_φ(L_2)) ⊑ L_1 ∪ L_2 \\
  %\\[-0.5em]
  %shortcut^l & = & α^{∃l}_φ \circ shortcut \circ γ^{∃l}_φ = id \\
  %\\[-0.5em]
  \semlive{\px}_ρ & = & ρ(\px) \\
  \\[-0.5em]
  \semlive{\Lam{\px}{\pe}}_ρ & = & (\varnothing, \FunV(\fn{d^l}{\semlive{\pe}_{ρ[\px↦d^l]}})) \\
  \\[-0.5em]
  \semlive{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & (L_1,v_1) = \semlive{\pe}_ρ \\
      \text{in}  & L_1 ∪_1 \begin{cases}
                     f(ρ(\px)) & \text{if $v = \FunV(f)$} \\
                     \bot_{∃l} & \text{otherwise}
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \semlive{\Let{\px}{\pe_1}{\pe_2}}_ρ& = & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ ⊔ [\px ↦ \{\px\} ∪_1 \semlive{\pe_1}_{ρ'}] \\
      \text{in}         & \semlive{\pe_2}_{ρ'}
    \end{letarray} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ v_1 ⊑ v_2 \qquad d_1 ⊑ d_2 } \\
  \\[-0.5em]
  \inferrule*
    {\quad}
    {\bot_{\Values^{∃l}} ⊑ v}
  \qquad
  \inferrule*
    {\forall d.\ f_1(d) ⊑ f_2(d)}
    {\FunV(f_1) ⊑ \FunV(f_2)} \\
  %TODO: We want the gfp, I think
  \\[-0.5em]
  \inferrule*
    {L_1 ⊆ L_2 \qquad v_1 ⊑ v_2}
    {(L_1,v_1) ⊑ (L_2,v_2)}
  \qquad
  \inferrule*
    {L_1 ⊆ L_2 \quad (\forall L,v.\ L_2 ⊆ L \Rightarrow f_1(L,v) ⊑ f_2(L,v)) }
    {(L_1,\FunV(f_1)) ⊑ (L_2,\FunV(f_2))} \\
  %TODO: We want the gfp, I think
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{∃l}_\SSD \colon \SSD → \LiveD \qquad α^{∃l}_φ \colon (\Configurations \to \SSTraces^{+\infty}) → \poset{\Var} \qquad α^{∃l}_{\Values^\Sigma} \colon \Values^\Sigma → \Values^{∃l} } } \\
  \\[-0.5em]
  α^{∃l}(σ) & = & \{ \px \in \Var \mid ∃i.\ σ_i = (\wild, \px, \wild, \wild) \wedge σ_{i+1}\ \text{exists} \} \\
  α^{∃l}_φ(φ) & = & \bigcup_{κ∈\Configurations}\{ α^{∃l}(φ(κ)) \} \\
  α^{∃l}_{\Values^\Sigma}(\FunV(f)) & = & \FunV(α^{∃l}_\SSD \circ f \circ γ^{∃l}_\SSD) \\
  α^{∃l}_{\Values^\Sigma}(\bot_{\Values^{\Sigma}}) & = & \bot_{\Values^{∃l}} \\
  α^{∃l}_\SSD(φ,v) & = & (α^{∃l}_φ(φ), α^{∃l}_{\Values^\Sigma}(v)) \\
  \dot{α}^{∃l}(ρ) & = & λx. α^{∃l}_\SSD(ρ(x)) \\
  \ddot{α}^{∃l}(S) & = & λρ. α^{∃l}_\SSD(S_{\dot{α}^{∃l}(ρ)}) \\
  \ddot{α}^{∃l}(\semss{e}) & ⊑ & \semlive{e} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ γ^{∃l}_\SSD \colon \LiveD → \poset{\SSD} \qquad γ^{∃l}_φ \colon \poset{\Var} → \poset{\Configurations \to \SSTraces^{+\infty}} \qquad γ^{∃l}_{\Values^\Sigma} \colon \Values^{∃l} → \poset{\Values^\Sigma} } } \\
  \\[-0.5em]
  γ^{∃l}(L) & = & \{ σ \mid ∀\px ∈ L.\ ∃i.\ σ_i = (\wild, \px, \wild, \wild) \wedge σ_{i+1}\ \text{exists}  \} \\
  γ^{∃l}_φ(L) & = & \{ (κ,σ) \mid σ ∈ γ^{∃l}(L) \} \\
  γ^{∃l}_\SSD(L,v) & = & \{ (φ,v') \mid φ ∈ γ^{∃l}_φ(L) \wedge v' ∈ γ'^{∃l}_{\Values^\Sigma}(L,v) \} \\
  γ^{∃l}_{\Values^\Sigma}(v) & = & γ'^{∃l}_{\Values^\Sigma}(\varnothing,v) \\
  γ'^{∃l}_{\Values^\Sigma}(\wild,\bot_{\Values^{\Sigma}}) & = & \{ \bot_{\Values^{∃l}} \} \\
  γ'^{∃l}_{\Values^\Sigma}(L_1,\FunV(f^\sharp)) & = & \{ \bot_{\Values^{∃l}} \} ∪ \{ \FunV(f) \mid \forall L_2,v.\ L_1 ⊆ L_2 \Rightarrow α^{∃l}_\SSD(f(γ^{∃l}_\SSD(L_2,v))) ⊑ f^\sharp(L_2,v) \} \\
  %     α(γ(L,fun(f#))) ⊑ (L,fun(f#))
  %    ⊔{ (α(φ),α(v)) | φ∈γ(L), v∈γ(L,fun(f#)) } ⊑ (L,fun(f#))
  %    forall φ v. φ∈γ(L) n v∈γ(L,fun(f#)) => (α(φ),α(v)) ⊑ (L,fun(f#))
  %    (case v=bottom => trivial)
  %    forall φ f. φ∈γ(L) n fun(f)∈γ(L,fun(f#)) => (α(φ),α(fun(f))) ⊑ (L,fun(f#))
  %    forall φ f. φ∈γ(L) n (forall L' v. L ⊆ L' => f(γ(L',v)) ⊆ γ(f#(L',v))) => (α(φ),α(fun(f))) ⊑ (L,fun(f#))
  %    forall φ f. φ∈γ(L) n (forall L' v. L ⊆ L' => f(γ(L',v)) ⊆ γ(f#(L',v))) => (α(φ),fun(α.f.γ)) ⊑ (L,fun(f#))
  %    (special rule)
  %    forall φ f. φ∈γ(L) n (forall L' v. L ⊆ L' => f(γ(L',v)) ⊆ γ(f#(L',v))) => α(φ) ⊑ L n (forall L' v. L⊆L' => (α.f.γ)(L',v) ⊑ f#(L',v))
  %    (α(γ(L)) ⊑ L)
  %    forall f. (forall L' v. L ⊆ L' => f(γ(L',v)) ⊆ γ(f#(L',v))) => (forall L' v. L⊆L' => (α.f.γ)(L',v) ⊑ f#(L',v))
  %    (rearrange)
  %    forall f L' v. L⊆L' => (forall L' v. L ⊆ L' => f(γ(L',v)) ⊆ γ(f#(L',v))) => (α.f.γ)(L',v) ⊑ f#(L',v)
  %    forall f L' v. L⊆L' => f(γ(L',v)) ⊆ γ(f#(L',v)) => (α.f.γ)(L',v) ⊑ f#(L',v)
  %    forall f L' v. L⊆L' => f(γ(L',v)) ⊆ γ(f#(L',v)) => (α.f.γ)(L',v) ⊑ f#(L',v)
  %
  %    Urgh, we need (α.f.γ)(L',v) ⊑ f#(L',v), not f(γ(L',v)) ⊆ γ(f#(L',v))!
  %
  %
  %    α(φ,v) ⊑ (L,v#) => (φ,v) ∈ γ(L,v#)
  %    α(φ,v) ⊑ (L,v#) => φ∈γ(L) n v∈γ(L,v#)
  %    (v = bot is trivial; consider v=fun(f),v#=fun(f#))
  %    α(φ,fun(f)) ⊑ (L,fun(f#)) => φ∈γ(L) n (forall L' v. L⊆L' => f(γ(L',v)) ⊆ γ(f#(L',v)))
  %    (α(φ),α(fun(f))) ⊑ (L,fun(f#)) => φ∈γ(L) n (forall L' v. L⊆L' => f(γ(L',v)) ⊆ γ(f#(L',v)))
  %    α(φ) ⊆ L n (forall L' v. L⊆L' => (γ.f.α)(L',v) ⊑ f#(L',v)) => φ∈γ(L) n (forall L' v. L⊆L' => f(γ(L',v)) ⊆ γ(f#(L',v)))
  %    (α(φ) ⊆ L <=> φ∈γ(L) Galois, eta)
  %    forall L' v. L⊆L' => (γ.f.α)(L',v) ⊑ f#(L',v) => f(γ(L',v)) ⊆ γ(f#(L',v))
  %
  %    Again, we need (α.f.γ)(L',v) ⊑ f#(L',v), not f(γ(L',v)) ⊆ γ(f#(L',v))!
 \end{array}
\end{array}\]
\caption{Potential liveness}
  \label{fig:liveness-abstraction}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Symbolic variables} & X & ∈ & \SVar &   & \\
  \text{Symbolic Liveness Domain} & d^{sl} & ∈ & \LiveSD & = & \poset{\Var ∪ \SVar} \times \Values^{sl} \\
  \text{Symbolic Liveness Values} & v^{sl} & ∈ & \Values^{sl} & = & \FunV_{\Values^{sl}}(X.\ d^{sl}) \mid \bot_{\Values^{sl}} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semslive{\wild} \colon \Exp → (\Var → \LiveSCD) → \LiveSCD } } \\
  \\[-0.5em]
  \bot_{sl} & = & (\varnothing, \bot_{\Values^{sl}}) \\
  \\[-0.5em]
  L_1 ∪_1 \wild & = & \fn{(L_2,v)}{(L_1 ∪ L_2, v)} \\
  \\[-0.5em]
  sym(X) & = & (\{ X \}, inert_{\Values^{sl}}) \\
  \\[-0.5em]
  \semslive{\px}_ρ & = & ρ(\px) \\
  \\[-0.5em]
  \semslive{\Lam{\px}{\pe}}_ρ & = & (\varnothing, \FunV(X_\px.\ \semslive{\pe}_{ρ[\px↦sym(X_\px)]})) \\
  \\[-0.5em]
  \semslive{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & (L_1,v_1) = \semslive{\pe}_ρ \\
      \text{in}  & L_1 ∪_1 \begin{cases}
                     d[ρ(\px) \mapsfrom X] & \text{if $v = \FunV(X.\ d)$} \\
                     \bot_{∃l}             & \text{otherwise}
                   \end{cases} \\
    \end{letarray} \\
  \\[-0.5em]
  \semslive{\Let{\px}{\pe_1}{\pe_2}}_ρ& = & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ ⊔ [\px ↦ \{\px\} ∪_1 \semslive{\pe_1}_{ρ'}] \\
      \text{in}         & \semslive{\pe_2}_{ρ'}
    \end{letarray} \\
  \\
 \end{array}
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{sl}_{\Values^{∃l}} \colon \Values^{∃l} → \Values^{sl}} } \\
  \\[-0.5em]
  α^{sl}_{\Values^{∃l}}(\FunV(f)) & = & \FunV(X.\ f(X)) \\
  γ^{sl}_{\Values^{∃l}}(\FunV(X,d)) & = & \FunV(\fn{d'}{d[d' \mapsfrom X]}) \\
  \\[-0.5em]
  (L,v)[(L',v') \mapsfrom X] & = & (L \setminus \{X\} ∪ \{ deep(L',v') \mid X ∈ L \}, v[(L',v') \mapsfrom X]) \\
  \FunV(f)[d' \mapsfrom X] & = & \FunV({\fn{d^{sl}}{f(d^{sl})[d' \mapsfrom X]}}) \\
  \\[-0.5em]
  deep_{\LiveSD}(L',v') & = & L' ∪ deep_{\Values^{sl}}(v') \\
  deep_{\Values^{sl}}(\FunV(f)) & = & \bigcup_v\{deep_{\LiveSD}(f(\varnothing,v))\} \\  % TODO: Think harder. Not correct I think
  inert_{\Values^{sl}} & = & \FunV(\fn{d^{sl}}{(deep(d^{sl}),inert_{\Values^{sl}})}) \\
 \end{array} \\
\end{array}\]
\begin{theorem}
  $(L,v) ⊑ (deep(L,v),inert_{\Values^{sl}})$
\end{theorem}
\begin{theorem}
  $\semslive{e}_{ρ[x↦d]} ⊑ \semslive{e}_{ρ[x↦sym(X)]}[d \mapsfrom X]$
\end{theorem}
\caption{Potential liveness, symbolic}
  \label{fig:liveness-abstraction-symb}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Contextual Small-Step Domain} & d^{c\Sigma} & ∈ & \SSCD & = & \Values^{c\Sigma} \times (\Configurations \to \SSTraces^{+\infty}) \to \Values^{c\Sigma} \times (\Configurations \to \SSTraces^{+\infty}) \\
  \text{Contextual Liveness Domain} & d^{cl} & ∈ & \LiveCD & = & \Values^{cl} \times \poset{\Var} \to \Values^{cl} \times \poset{\Var} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{c}_\AbsD \colon \AbsD → \AbsCD \qquad α^{c\Sigma}_\SSD \colon \SSD → \SSCD \qquad α^{cl}_\SSD \colon \SSD → \LiveCD} } \\
  \\[-0.5em]
  α^{c}_\AbsD(d) & = & \fn{c}{c(d)} \\
  γ^{c}_\AbsD(f) & = & f(id) \\
  α^{c}_{\Values}(\FunV(f)) & = & \FunV(α^{c}_\AbsD \circ f \circ γ^{c}_\AbsD) \\
  α^{c}_{\Values}(\bot_{\Values}) & = & \bot_{\Values^{c}} \\
  \\[-0.5em]
  α^{c\Sigma}_\SSD(v,φ) & = & \fn{c}{c(α^{c\Sigma}_{\Values^\Sigma}(v),φ)} \\
  α^{cl}_\SSD(v,φ) & = & \fn{c}{c(α^{c}_{\Values^{∃l}}(v),α^{∃l}(φ))} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semclive{\wild} \colon \Exp → (\Var → \LiveCD) → \LiveCD } } \\
  \\[-0.5em]
  \bot_{cl} & = & \fn{c}{c (\bot_{\Values^{cl}}, \varnothing)} \\
  \\[-0.5em]
  L_1 ∪_1 \wild & = & \fn{(L_2,v)}{(L_1 ∪ L_2, v)} \\
  \\[-0.5em]
  apply(d^{cl},c) & = & \fn{(v_1,L_1)}{\begin{cases}
      f(d^{cl})~(c \circ (L_1 ∪_1 \wild)) & \text{if $v_1 = \FunV(f)$} \\
      \bot_{cl}~(c \circ (L_1 ∪_1 \wild)) & \text{otherwise}
    \end{cases}} \\
  \\[-0.5em]
  \semclive{\px}_ρ~c & = & ρ(\px)~c \\
  \\[-0.5em]
  \semclive{\Lam{\px}{\pe}}_ρ~c & = & c(\FunV(\fn{d^{cl}}{\semclive{\pe}_{ρ[\px↦d^{cl}]}}), \varnothing) \\
  \\[-0.5em]
  \semclive{\pe~\px}_ρ~c & = & \semclive{\pe}_ρ~(apply(ρ(\px),c)) \\
  \\[-0.5em]
  \semclive{\Let{\px}{\pe_1}{\pe_2}}_ρ~c& = & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ ⊔ [\px ↦ \fn{c}{~\semclive{\pe_1}_{ρ'}~(c \circ (\{\px\} ∪_1 \wild))}] \\
      \text{in}         & \semclive{\pe_2}_{ρ'}~c
    \end{letarray} \\
  \\
 \end{array}
\end{array}\]
\begin{theorem} About pushing/reifying continuations
  \[
  f(α^{c}_\AbsD(d)(c')) = f(c'(d)) = α^{c}_\AbsD(d)(f \circ c')
  \]
\end{theorem}
\caption{Potential liveness, contextual}
  \label{fig:liveness-abstraction}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Symbolic variables} & X & ∈ & \SVar &   & \\
  \text{Symbolic call} & sc & ∈ & \SCall & = & X(c) \\
  \text{Symbolic Liveness Domain} & d^{sl} & ∈ & \LiveSD & = & \poset{\Var ∪ \SCall} \times \Values^{sl} \\
  \text{Symbolic Liveness Values} & v^{sl} & ∈ & \Values^{sl} & = & \FunV_{\Values^{sl}}(X,d^{sl}) \mid \bot_{\Values^{sl}} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ sc_1 ⊑ sc_2 \qquad L_1 ⊑ L_2 \qquad d_1 ⊑ d_2 } \\
  \\[-0.5em]
  \inferrule*
    {L_1 ∩ \Var ⊆ L_2 ∩ \Var \qquad ∀X(c_1)∈(L_1∩\SCall).\ ∃X(c_2)∈(L_1∩\SCall).\ c_1 ⊑ c_2}
    {L_1 ⊑ L_2}
  \qquad
  \inferrule*
    {L_1 ∩ \Var ⊆ L_2 ∩ \Var \qquad ∀X(c_1)∈(L_1∩\SCall).\ ∃X(c_2)∈(L_1∩\SCall).\ c_1 ⊑ c_2}
    {L_1 ⊑ L_2}
  \\[-0.5em]
  \inferrule*
    {L_1 ⊆ L_2 \qquad v_1 ⊑ v_2}
    {(L_1,v_1) ⊑ (L_2,v_2)}
  \qquad
  \inferrule*
    {L_1 ⊆ L_2 \quad (\forall L,v.\ L_2 ⊆ L \Rightarrow f_1(L,v) ⊑ f_2(L,v)) }
    {(L_1,\FunV(f_1)) ⊑ (L_2,\FunV(f_2))} \\
  %TODO: We want the gfp, I think
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{sl}_{\Values^{∃l}} \colon \Values^{∃l} → \Values^{sl}} } \\
  \\[-0.5em]
  α^{sl}_{\Values^{∃l}}(\FunV(f)) & = & \FunV(X,f(X)) \\
  γ^{sl}_{\Values^{∃l}}(\FunV(X,d)) & = & \FunV(\fn{d'}{d[d' \mapsfrom X]}) \\
  %α^{sl}_{\Values^{∃l}}(\bot_{\Values^{∃l}}) & = & \bot_{\Values^{c}} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semsclive{\wild} \colon \Exp → (\Var → \LiveSCD) → \LiveSCD } } \\
  \\[-0.5em]
  \bot_{sl} & = & (\varnothing, \bot_{\Values^{sl}}) \\
  \\[-0.5em]
  L_1 ∪_1 \wild & = & \fn{(L_2,v)}{(L_1 ∪ L_2, v)} \\
  \\[-0.5em]
  inert_{\Values^{scl}} & = & \FunV(\fn{d^{scl}}{\fn{c}{c(inert_{\Values^{scl}}, snd(d^{scl}~\top_{c}))}}) \\
  %TODO: is inert well-defined???
  \\[-0.5em]
  sym(X) & = & \fn{c}{c (inert_{\Values^{scl}}, \{ X(c) \})} \\
  \\[-0.5em]
  apply(d^{scl},c) & = & \fn{(v_1,L_1)}{\begin{cases}
      f(d^{scl})~(c \circ (L_1 ∪_1 \wild)) & \text{if $v_1 = \FunV(f)$} \\
      \bot_{scl}~(c \circ (L_1 ∪_1 \wild)) & \text{otherwise}
    \end{cases}} \\
  \\[-0.5em]
  \semslive{\px}_ρ~c & = & ρ(\px)~c \\
  \\[-0.5em]
  \semslive{\Lam{\px}{\pe}}_ρ~c & = & c(\FunV(\fn{d^{scl}}{~(\semslive{\pe}_{ρ[\px↦sym(X_\px)]})[X_\px \mapsfrom d^{scl}]}), \varnothing) \\
  \\[-0.5em]
  \semslive{\pe~\px}_ρ~c & = & \semslive{\pe}_ρ~(apply(ρ(\px),c)) \\
  \\[-0.5em]
  \semslive{\Let{\px}{\pe_1}{\pe_2}}_ρ~c& = & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ ⊔ [\px ↦ \fn{c}{~\semslive{\pe_1}_{ρ'}~(c \circ look(\px))}] \\
      \text{in}         & \semslive{\pe_2}_{ρ'}~c
    \end{letarray} \\
  \\
 \end{array}
\end{array}\]
\begin{theorem}
  $(\semslive{e}_{ρ[x↦d]}~c)$ ⊑ $(\semslive{e}_{ρ[x↦sym(X)]}~c)[d \mapsfrom X]$
\end{theorem}
\caption{Potential liveness, symbolic}
  \label{fig:liveness-abstraction-symb}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Abstract stack} &   \lS & ∈ & \lStacks & ::= & \lSBot \mid \lSAp{\lS} \mid \lSTop \\
  \text{Liveness}       &     l & ∈ & \lLiveness & ::= & \lAbs \mid \lUsed{\lS} \\
 \end{array} \\
 \\
 \begin{array}{c}
   \\[-0.5em]
   \inferrule*
     {\quad}
     {\lSBot ⊑ \lS} \qquad
   \inferrule*
     {\lS_1 ⊑ \lS_2}
     {\lSAp{\lS_1} ⊑ \lSAp{\lS_2}} \qquad
   \inferrule*
     {\quad}
     {\lS ⊑ \lSTop} \\
   \\[-0.5em]
   \inferrule*
     {\quad}
     {\lAbs ⊑ l} \qquad
   \inferrule*
     {\lS_1 ⊑ \lS_2}
     {\lUsed{\lS_1} ⊑ \lUsed{\lS_2}} \\
   \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ α^{∃l}_\SSD \colon \SSD → \LiveD \qquad α^{∃l}_φ \colon (\Configurations \to \SSTraces^{+\infty}) → \poset{\Var} \qquad α^{∃l}_{\Values^\Sigma} \colon \Values^\Sigma → \Values^{∃l} } } \\
  \\[-0.5em]
  α^{∃l}_\Stacks(\StopF) & = & \lSBot \\
  α^{∃l}_\Stacks(\UpdateF(\pa) \pushF \lS) & = & α^{∃l}_\Stacks(\lS) \\
  α^{∃l}_\Stacks(\ApplyF(\pa) \pushF \lS) & = & \lSAp{α^{∃l}_\Stacks(\lS)} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semlive{\wild} \colon \Exp → (\Var → \LiveD) → \LiveD } } \\
  \\[-0.5em]
  \bot_{∃l} & = & (\bot_{\Values}, \varnothing) \\
  \\[-0.5em]
  L_1 \fcomp^l L_2 & = & α^{∃l}_φ(γ^{∃l}_φ(L_1) \fcomp γ^{∃l}_φ(L_2)) ⊑ L_1 ∪ L_2 \\
  \\[-0.5em]
  shortcut^l & = & α^{∃l}_φ \circ shortcut \circ γ^{∃l}_φ = id \\
  \\[-0.5em]
  \semlive{\px}_ρ & = & ρ(\px) \\
  \\[-0.5em]
  \semlive{\Lam{\px}{\pe}}_ρ & = & (\FunV(\fn{d^l}{\semlive{\pe}_{ρ[\px↦d^l]}}, \varnothing) \\
  \\[-0.5em]
  \semlive{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & (v_1,L_1) = \semlive{\pe}_ρ \\
                 & (v_2,L_2) = \begin{cases}
                     f(ρ(\px)) & \text{if $v = \FunV(f)$} \\
                     \bot_{∃l} & \text{otherwise}
                   \end{cases} \\
      \text{in}  & (v_2, L_1 ∪ L_2) \\
    \end{letarray} \\
  \\[-0.5em]
  \semlive{\Let{\px}{\pe_1}{\pe_2}}_ρ& = & \begin{letarray}
      \text{letrec}~ρ'. & (v_1,L_1) = \semlive{\pe_1}_{ρ'} \\
                        & ρ' = ρ ⊔ [\px ↦ (v_1,\{\px\} ∪ L_1))] \\
      \text{in}         & \semlive{\pe_2}_{ρ'}
    \end{letarray} \\
  \\
 \end{array}
 \\
\end{array}\]
\caption{Potential liveness}
  \label{fig:liveness-abstraction}
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
      \text{letrec}~ρ'. & ρ' = ρ ⊔ [\px ↦ \seminf{\pe_1}_{ρ'}] \\
      \text{in}         & cons(\BindA,\atlbl{\pe_2},\seminf{\pe_2}_{ρ'})(π_i^+)
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

