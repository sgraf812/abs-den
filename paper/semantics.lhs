\section{Semantics}
\label{sec:semantics}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}    & \px,\py,\pz & ∈ & \Var        &     & \\
  \text{Variables}    &         \pv & ∈ & \Val        & ::= & \Lam{\px}{\pe} \\
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
      \text{let} & f = d ↦ \step{\AppEA}{\pe} \fcomp \seminf{\pe}_{ρ[\px↦d]} \\
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
%   * Small-step semantics does have update frames and we want to match those
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
%   * (Are all complete state structures are isomorph?)
%   * The stateful trace semantics is an abstraction of the stateless trace
%     semantics by way of α_S. We want to produce (at least one) stateful
%     semantics where the state space is complete. To produce such states, the
%     necessary information must be part of the stateless trace, otherwise we
%     can't write the abstraction function from statelss to stateful.
%
% So given the completeness of the states produced by α_S as a goal, we can
% make the following claims for action kinds in a trace:
%
%   * AppI, AppE, Lookup, Bind are all necessary actions because they make
%     a step from one label to a label of a subexpression.
%   * Val actions are the trace semantics' means of communicating a successful
%     (e.g., not stuck) execution as well as playing the role of `Just value`.
%     It is crucial that values have a second label, otherwise the transition
%     system would loop endlessly, as there would be no correspondence operation
%     on (e.g., small-step) states.
%     (Although stuckness that doesn't mean they are *necessary* for the trace
%     semantics: The primary means to determine a successful trace is whether it
%     is balanced... So we don't actually need the action, just the value, which
%     could be communicated out of band. It's just horribly ugly to do so; I
%     tried, see page 4 of 61e6f8a.)
%   * We do *not* strictly need Update actions -- we just need update frames
%     in the stateful trace, but those can be reconstructed from when a Lookup's
%     balanced trace ended. Update actions make our life simpler in other ways,
%     though: See "The need for an update action".
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
%     necessary, just convenient (as I said above).

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
      \text{let} & f = d ↦ \step{\AppEA}{\pe} \fcomp \seminf{\pe}_{ρ[\px↦d]} \\
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
  \text{States}                             & σ      & ∈ & \States  & = & (\Exp ∪ \{\ddagger\}) \times \Environments \times \Heaps \times \Continuations \\
  \text{Environments}                       & ρ      & ∈ & \Environments & = & \Var \pfun \Addresses \\
  \text{Heaps}                              & μ      & ∈ & \Heaps & = & \Addresses \pfun \Exp \times \Environments \times \StateD \\
  \text{Continuations}                      & κ      & ∈ & \Continuations & ::= & \StopF \mid \ReturnF(\pv,ρ,v) \pushF κ \mid \ApplyF(\pa) \pushF κ \mid \UpdateF(\pa) \pushF κ \\
  \\[-0.5em]
  \text{Stateful traces}                    & π      & ∈ & \STraces  & ::=_\gfp & σ\straceend \mid π; π \\
  \text{Domain of stateful trace semantics} & d      & ∈ & \StateD  & = & \States \to \STraces \\
  \text{Values}                             & v      & ∈ & \Values^\States & ::= & \FunV(d) \\
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
    π_1       & \text{if $π_1$ infinite} \\
    undefined & \text{if $π_1$ finite and $dst_\States(π_1) \not= src_\States(π_2)$} \\
    σ         & π_1 = π_2 = σ\straceend \\
    π_1'; π_2 &  π_1 = π_1'; σ\straceend \\
    π_1; π_2' &  π_2 = σ; π_2' \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ σ_1 \smallstep σ_2 \qquad \validtrace{π} } \\
  \\[-0.5em]
  \inferrule*
    [right=$\ValueT$]
    {\quad}
    {(\pv, ρ, μ, κ) \smallstep (\ddagger,[],μ,\ReturnF(\pv,ρ,v) \pushF κ)}
  \qquad
  \inferrule*
    [right=$\LookupT$]
    {\pa = ρ(\px) \quad (\pe,ρ',\wild) = μ(\pa)}
    {(\px, ρ, μ, κ) \smallstep (\pe,ρ',μ,\UpdateF(\pa) \pushF κ)}
  \\
  \inferrule*
    [right=$\UpdateT$]
    {\quad}
    {(\ddagger,[],μ,\ReturnF(\pv,ρ',v) \pushF \UpdateF(\pa) \pushF κ) \smallstep (\ddagger,[],μ[\pa ↦ (\pv,ρ',d)],\ReturnF(\pv,ρ',v) \pushF κ)} \\
  \\[-0.5em]
  \inferrule*
    [right=$\AppIT$]
    {\pa = ρ(\px)}
    {(\pe~\px,ρ,μ,κ) \smallstep (\pe,ρ,μ,\ApplyF(\pa) \pushF κ)}
  \quad
  \inferrule*
    [right=$\AppET$]
    {\quad}
    {(\ddagger,[],μ,\ReturnF(\Lam{\px}{\pe},ρ,\wild) \pushF \ApplyF(\pa) \pushF κ) \smallstep (\pe,ρ[\px ↦ \pa],μ,κ)} \\
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
\caption{Call-by-need (stateful) transition system $\smallstep$}
  \label{fig:ss-syntax}
\end{figure}

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
  ret(v)(\pv,ρ,μ,κ) & = & (\ddagger,[],μ,\ReturnF(\pv,ρ,v) \pushF κ) \straceend \\
  \\[-0.5em]
  var_1(\px,ρ,μ,κ) & = &
    \begin{letarray}
      \text{let} & \pa = ρ(x) \\
                 & (\pe,ρ',d) = μ(\pa) \\
      \text{in}  & d(\pe,ρ',μ,\UpdateF(\pa) \pushF κ) \\
    \end{letarray} \\
  \\[-0.5em]
  var_2(\ddagger,[],μ,\ReturnF(\pv,ρ,v) \pushF \UpdateF(\pa) \pushF κ) & = &
    \begin{letarray}
      \text{let} & d(\pv, ρ, μ', κ') = (\ddagger, [], μ', \ReturnF(\pv,ρ,v) \pushF κ')\straceend \\
      \text{in}  & (\ddagger,[],μ[\pa ↦ (\pv,ρ,step(d))],\ReturnF(\pv,ρ,v) \pushF κ) \\
    \end{letarray} \\
  \\[-0.5em]
  app_1(\pe~\px,ρ,μ,κ) & = & (\pe,ρ,μ,\ApplyF(ρ(\px)) \pushF κ)\straceend \\
  \\[-0.5em]
  app_2(\ddagger,[],μ,\ReturnF(\Lam{\px}{\pe},ρ',\FunV(d)) \pushF \ApplyF(\pa) \pushF κ) & = & d(\pe,ρ'[\px ↦ \pa],μ,κ) \\
  \\[-0.5em]
  let(d_1)(\Let{\px}{\pe_1}{\pe_2},ρ,μ,κ) & = &
    \begin{letarray}
      \text{let} & ρ' = ρ[\px ↦ \pa] \quad \text{where $\fresh{\pa}{μ}$} \\
      \text{in}  & (\pe_2,ρ',μ[\pa ↦ (\pe_1, ρ', d_1)],κ) \\
    \end{letarray} \\
  \\[-0.5em]
  \semst{\pe}(\pe',ρ,μ,κ) & = & (\pe',ρ,μ,κ)\straceend\ \text{when $\atlbl{\pe} \not= \atlbl{\pe'}$} \\
  \\[-0.5em]
  \semst{\px} & = & step(var_1) \sfcomp step(var_2) \\
  \\[-0.5em]
  \semst{\Lam{\px}{\pe}} & = & step(ret(\FunV(\semst{\pe}))) \\
  \\[-0.5em]
  \semst{\pe~\px} & = & step(app_1) \sfcomp \semst{\pe} \sfcomp step(app_2) \\
  \\[-0.5em]
  \semst{\Let{\px}{\pe_1}{\pe_2}} & = & step(let(\semst{\pe_1})) \sfcomp \semst{\pe_2} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Structural call-by-need stateful trace semantics $\semst{-}$}
  \label{fig:ss-semantics}
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

\FloatBarrier

\begin{lemma}
  Let $d = \semst{\pe}$. Then $\validtrace{d(σ)}$ for every initial configuration $σ$.
\end{lemma}
\begin{proof}
  Every $d$ is either $\fn{σ}{σ\straceend}$, where $\validtrace{σ\straceend}$,
  or it is produced by $\fcomp$, $cons$ or $snoc$. These combinators
  produce valid small-step derivations whenever their input $d$ produces
  valid derivations. By (bi-)induction that is always the case.
\end{proof}

\begin{definition}[Maximally balanced trace]
  A small-step trace $π = (e_1,ρ_1,μ_1,κ_1) ... (e_i,ρ_i,μ_i,κ_i); ... $ is \emph{maximally balanced} if
  \begin{itemize}
    \item $\validtrace{σ}$, and
    \item Every intermediate continuation $κ_i$ extends $κ_1$ (so $κ_i = ... \pushF κ_1$), and
    \item If $π$ is finite, then there is no $σ'$ such that $π; σ'$ is maximally balanced.
  \end{itemize}
  We notate maximally-balanced traces as $\maxbaltrace{π}$.
\end{definition}

In other words, a trace is maximally balanced if it follows the transition
semantics, never leaves the current evaluation context and is either infinite,
stuck, or its final state $σ_n$ has $\ddagger$ in its focus and $κ_n = \ReturnF(v) \pushF κ_i$.

For the initial state with an empty stack, the balanced maximal trace is
exactly the result of running the transition semantics to completion.

We make this connection explicit in the following relation:

\begin{definition}[Adequate denotations]
We say that an element $d ∈ \StateD$ is an adequate denotation of an expression
$\pe$ in a binding context $ρ,μ$ (written $μ \vdash_\StateD e \sim_ρ d$) if, for
any $κ$,
\begin{itemize}
  \item $\vdash_\Heaps μ$, as defined below.
  \item The state $σ=(\pe,ρ,μ,κ)$ is the initial state of the trace
    $d(σ)$, and
  \item $d(σ)$ is maximally balanced, and
  \item If $dst_\States(d(σ)) = (\ddagger, \wild, μ', \ReturnF(\pv, ρ', v) \pushF κ)$, then
    $μ' \vdash_{\Values_\States} \pv \sim_{ρ'} v$, as defined below.
\end{itemize}
A semantic value $v ∈ \Values_\States$ is an adequate denotation of a syntactic value $\pv$ in a binding context $ρ,μ$
(written $μ' \vdash_{\Values_\States} \pv \sim_{ρ'} v$), if $\pv$ is of the form $\Lam{\px}{\pe}$, $v$ is of the form $\FunV(d)$ and for any $\pa$,
we have $μ \vdash_\StateD \pe \sim_{ρ[\px↦\pa]} d$.

Formally, the inference rule is
\[
  \inferrule*
    {∀κ.\ ∃σ.\ σ=(\pe,ρ,μ,κ) ∧ src_\States(d(σ)) = σ ∧ \maxbaltrace{d(σ)} ∧ (∃(μ',\pv,ρ',v).\ dst_\States(d(σ)) = (\ddagger, \wild, μ', \ReturnF(\pv, ρ', v) \pushF κ) \Rightarrow μ' \vdash_{\Values_\States} \pv \sim_{ρ'} v)}
    {μ \vdash_\StateD \pe \sim_ρ d}
\]
\[
  \inferrule*
    {∀\pa.\ μ \vdash_\StateD \pe \sim_{ρ[\px↦\pa]} d}
    {μ \vdash_{\Values_\States} \Lam{\px}{\pe} \sim_ρ \FunV(d)}
\]
\end{definition}

The notion of adequate denotation can be applied to whole heaps $μ$:
\[
  \inferrule*
    {∀(\pe,ρ,d)∈\rng{μ}.\ μ \vdash_\StateD \pe \sim_ρ d}
    {\vdash_\Heaps μ}
\]
Since there is mutual recursion, it is important that $\vdash_\Heaps \wild$ is
defined as the \emph{greatest} fixpoint over this inference rule.

We'll often omit the binding context when talking about $d$ being a valid denotation of $\pe$, implying that
$μ \vdash_\StateD \pe \sim_ρ d$ for all $ρ,μ$ where $\vdash_\Heaps μ$.

We can now formulate our correctness theorem as follows:

\begin{theorem}[Adequacy of the stateful trace semantics]
Let $d = \semst{\pe}$. Then for all $ρ,μ$ with $\vdash_\Heaps μ$, we have $μ
\vdash_\StateD \pe \sim_ρ d$.
\end{theorem}

\begin{corollary}Let $d = \semst{\pe}$. Then $π=d(\pe,[],[],\StopF)$ is a
maximally balanced trace for the transition semantics starting at $(\pe,[],[],\StopF)$.
\end{corollary}

Note that for the initial configuration of an expression, the balanced
small-step trace is exactly the maximal finite trace that ends with a value.

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Configurations}                        & κ   & ∈ & \Configurations    & ::= & (\pH,\pe,\pE,\pS) \\
  \text{Heaps}                                 & \pH & ∈ & \Heaps             & =   & \Addresses \pfun (\Envs,\Exp) \\
  \text{Environments}                          & \pE & ∈ & \Envs              & =   & \Var \pfun \Addresses \\
  \text{Stacks}                                & \pS & ∈ & \Stacks            & ::= & \StopF \mid \ApplyF(\pa) \pushF \pS \mid \UpdateF(\pa) \pushF \pS \\
  \text{Finite Small-step Traces}              & σ   & ∈ & \SSTraces^+         & ::= & κ\straceend \mid κ; σ \\
  \text{Finite and Infinite Small-step Traces} & σ   & ∈ & \SSTraces^{+\infty} & =   & \SSTraces^+ ∪ \lim(\SSTraces^+) \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ src_\Sigma(σ) = κ \qquad dst_\Sigma(σ) = κ } } \\
  \\[-0.5em]
  src_\Sigma(κ\straceend)    & = & κ \\
  src_\Sigma(κ; σ) & = & κ \\
  \\[-0.5em]
  dst_\Sigma(κ\straceend)    & = & κ \\
  dst_\Sigma(κ; σ) & = & dst_\Sigma(σ) \\
  \\
 \end{array} \qquad
 \begin{array}{c}
  \ruleform{ σ_1 \ssconcat σ_2 = σ_3 } \\
  \\[-0.5em]
  σ_1 \ssconcat σ_2 = \begin{cases}
    σ_1              & \text{if $σ_1$ infinite} \\
    undefined        & \text{if $σ_1$ finite and $dst_\Sigma(σ_1) \not= src_\Sigma(σ_2)$} \\
    κ             & σ_1 = σ_2 = κ \\
    σ_1'; σ_2 &  σ_1 = σ_1'; κ \\
    σ_1; σ_2' &  σ_2 = κ; σ_2' \\
  \end{cases} \\
 \end{array} \\
 \\
 \begin{array}{c}
  \ruleform{ κ_1 \smallstep κ_2 \qquad \validtrace{σ} } \\
  \\[-0.5em]
  \inferrule*
    [right=$\LookupT$]
    {\pa = \pE(\px)}
    {(\pH, \px, \pE, \pS) \smallstep (\pH, \pH(\pa), \UpdateF(\pa) \pushF \pS)}
  \qquad
  \inferrule*
    [right=$\UpdateT$]
    {\quad}
    {(\pH, \pv, \pE, \UpdateF(\pa) \pushF \pS) \smallstep (\pH[\pa↦(\pE,\pv)], \pv, \pE, \pS)} \\
  \\[-0.5em]
  \inferrule*
    [right=$\AppIT$]
    {\pa = \pE(\px)}
    {(\pH, \pe~\px, \pE, \pS) \smallstep (\pH, \pe, \pE, \ApplyF(\pa) \pushF \pS)}
  \qquad
  \inferrule*
    [right=$\AppET$]
    {\quad}
    {(\pH, \Lam{\px}{\pe}, \pE, \ApplyF(\pa) \pushF \pS) \smallstep (\pH, \pe, \pE[\px↦\pa], \pS)} \\
  \\[-0.5em]
  \inferrule*
    [right=$\LetT$]
    {\fresh{\pa}{\pH} \quad \pE' = \pE[\px↦\pa]}
    {(\pH, \Let{\px}{\pe_1}{\pe_2}, \pE, \pS) \smallstep (\pH[\pa↦(\pE',\pe_1)], \pe_2, \pE', \pS)} \\
  \\
  \\
  \inferrule*
    {\quad}
    {\validtrace{κ\straceend}}
  \qquad
  \inferrule*
    {κ \smallstep src_\Sigma(σ) \quad \validtrace{σ}}
    {\validtrace{κ; σ}} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Call-by-need small-step transition system $\smallstep$}
  \label{fig:ss-syntax}
\end{figure}

\begin{figure}
\[\begin{array}{c}
 \begin{array}{rrclcl}
  \text{Domain of small-step transitions} &       &   & \SSD  & = & (\Configurations \to \SSTraces^{+\infty},\Values^\Sigma) \\
  \text{Values}          &     v & ∈ & \Values^\Sigma & ::= & \FunV(\SSD \to \SSD) \mid \bot_{\Values^\Sigma} \\
 \end{array} \\
 \\
 \begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semss{\wild} \colon \Exp → (\Var → \SSD) → \SSD } } \\
  \\[-0.5em]
  \bot_\Sigma & = & (\fn{κ}{κ\straceend}, \bot_{\Values^\Sigma}) \\
  \\[-0.5em]
  (f \fcomp g)(κ) & = & f(κ) \ssconcat g(dst_\Sigma(f(κ))) \\
  \\[-0.5em]
  cons(t,φ)(κ_1) & = & \begin{cases}
    κ_1; φ(κ_2) & \text{with $κ_2$ such that $κ_1 \smallstep κ_2$ with rule $t$} \\
    κ_1                   & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  snoc(φ,t)(κ) & = & \begin{cases}
    φ(κ); κ_2 \straceend & \text{with $κ_2$ such that $dst_\Sigma(φ(κ)) \smallstep κ_2$ with rule $t$} \\
    φ(κ)                & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  shortcut(φ)(\pH,\pe,\pS) & = & \begin{cases}
    (\pH,\pv,\pS)  & \text{if $\pe$ is a value $\pv$} \\
    φ(\pH,\pe,\pS) & \text{otherwise} \\
  \end{cases} \\
  \\[-0.5em]
  \semss{\px}_ρ & = & ρ(\px) \\
  \\[-0.5em]
  \semss{\Lam{\px}{\pe}}_ρ & = & (\fn{κ}{κ\straceend}, \FunV(\fn{d}{\semss{\pe}_{ρ[\px↦d]}})) \\
  \\[-0.5em]
  \semss{\pe~\px}_ρ & = &
    \begin{letarray}
      \text{let} & (φ_1,v_1) = \semss{\pe}_ρ \\
                 & (φ_2,v_2) = \begin{cases}
                     f(ρ(\px))   & \text{if $v = \FunV(f)$} \\
                     \bot_\Sigma & \text{otherwise}
                   \end{cases} \\
      \text{in}  & (cons(\AppIT,φ_1) \fcomp cons(\AppET,φ_2), v_2) \\
    \end{letarray} \\
  \\[-0.5em]
  \semss{\Let{\px}{\pe_1}{\pe_2}}_ρ& = & \begin{letarray}
      \text{letrec}~ρ'. & (φ_1,v_1) = \semss{\pe_1}_{ρ'} \\
                        & (φ_2,v_2) = \semss{\pe_2}_{ρ'} \\
                        & ρ' = ρ ⊔ [\px ↦ (snoc(cons(\LookupT,shortcut(φ_1)),\UpdateT),v_1)] \\
      \text{in}  & (cons(\LetT,φ_2),v_2)
    \end{letarray} \\
  \\
 \end{array} \\
\end{array}\]
\caption{Structural call-by-need small-step trace semantics $\semss{-}$}
  \label{fig:ss-semantics}
\end{figure}

\begin{figure}
  \begin{lemma}
    Let $(v,φ) = \semss{\pe}_ρ$. Then $\validtrace{φ(κ)}$ for every initial configuration $κ$.
  \end{lemma}
  \begin{proof}
    Every $φ$ is either $\fn{κ}{κ\straceend}$, where $\validtrace{κ\straceend}$,
    or it is produced by $\fcomp$, $cons$ or $snoc$. These combinators
    produce valid small-step derivations whenever their input $φ$ produces
    valid derivations. By (bi-)induction that is always the case.
  \end{proof}

  \begin{definition}[Maximal small-step trace]
    A small-step trace $σ$ is \emph{maximal} iff $\validtrace{σ}$ and either
    \begin{itemize}
      \item σ is infinite, or
      \item there is no $κ'$ such that $dst_\Sigma(σ) \smallstep κ'$
    \end{itemize}
  \end{definition}

  Clearly, a term's defining property wrt. a small-step transition system such
  as $\smallstep$ is the maximal trace of its initial configuration.

  \begin{definition}[Balanced small-step trace]
    A finite small-step trace
    $σ=(\pH,\pe,\pE,\pS); ...; (\pH',\pe', \pE', \pS')\straceend$
    is \emph{balanced} if $\validtrace{σ}$, $\pe'$ is a value, $\pS=\pS'$, and
    every intermediate stack extends $\pS$.
  \end{definition}

  \begin{definition}[Maximally balanced small-step trace]
    A small-step trace σ is \emph{maximally balanced} iff $\validtrace{σ}$,
    all stacks in σ extend the stack of its initial configuration, and either
    \begin{itemize}
      \item $σ$ is infinite, or
      \item there is no $κ'$ such that $dst_\Sigma(σ) \smallstep κ'$, or
      \item σ is balanced
    \end{itemize}
  \end{definition}

  In other words, a trace is maximally balanced if it is either balanced or
  the trace is maximal and it has no balanced prefix trace.

  For the initial configuration/configurations with an empty stack, the
  balanced, maximal and maximally balanced traces coincide.

  \begin{definition}[Correctness relation]
    Consider the relation $\wild \vdash \wild \sim \wild \triangleq \gfp(F)$, where
    \[
      F(X) = \{ (\pH, \pE, ρ) \mid \forall \px \in \dom(\pE).\ \exists (\pE',\pe').\ (\pE',\pe') = \pH(\pE(\px)) \wedge ρ(\px) = \semss{\pe'}_{ρ'} \wedge (\pH, \pE', ρ') \in X \}
    \]
    We say that a denotational environmant ρ is \emph{consistent} with an environment
    $\pE$ in a heap $\pH$ iff $\pH \vdash \pE \sim ρ$.
  \end{definition}

  \begin{theorem}Let $(v,φ) = \semss{\pe}_ρ$. Then for all configurations
  $κ=(\pH,\pe,\pE,\pS)$ where $\pH \vdash \pE \sim ρ$ the small-step trace $φ(κ)$ is the
  maximally balanced small-step trace starting from $κ$.
  \end{theorem}

  Note that for the initial configuration of an expression, the balanced
  small-step trace is exactly the maximal finite trace that ends with a value.

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

