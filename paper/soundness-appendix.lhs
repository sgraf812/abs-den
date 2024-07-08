\subsection{Guarded Fixpoints, Safety Properties and Safety Extension of a Galois Connection}
\label{sec:safety-extension}

\Cref{fig:abstract-name-need} describes a semantic trace property as a ``fold'', in
terms of a |Trace| instance.
Of course such a fold (an inductive elimination procedure) has no meaning when
the trace is infinite!
Yet it is always clear what we mean: When the trace is infinite and described by
a guarded fixpoint, we consider the meaning of the fold as the limit (\ie least
fixpoint) of its finite prefixes.
In this subsection, we discuss when and why this meaning is correct.

Suppose that we were only interested in the trace component of our
semantic domain, thus effectively restricting ourselves to
$\Traces \triangleq |T ()|$, and that we were to approximate properties $P ∈
\pow{\Traces}$ about such traces by a Galois connection
$|α| : (\pow{\Traces},⊆) \rightleftarrows (|hat D|, ⊑) : |γ|$.
Alas, although the abstraction function |α| is well-defined as a mathematical
function, it most certainly is \emph{not} computable at infinite inputs (in
$\Traces^{\infty}$), for example at
|fix (Step (Look x)) = Step (Look x) (Step (Look x) ...)|!

The whole point about \emph{static} analyses is that they approximate program
behavior in finite data.
As we have discussed in \Cref{sec:usage-fixpoint}, this rules out use of
\emph{guarded} fixpoints |fix| for usage analysis, so it uses computes the
\emph{least} fixpoint |lfp| instead.
Concretely, static analyses often approximate the abstraction of the guarded
fixpoint by the least fixpoint of the abstracted iteratee, assuming the
following approximation relationship:
\[
|α ((set (fix (Step (Look x)))))| ⊑ |lfp (α . powMap (Step (Look x)) . γ)|.
\]
This inequality does not hold for \emph{all} trace properties, but we will
show that it holds for \emph{safety} properties~\citep{Lamport:77}:

\begin{definition}[Safety property]
A trace property $P ⊆ \Traces$ is a \emph{safety property} iff,
whenever $|τ1|∈\Traces^{\infty}$ violates $P$ (so $|τ1| \not∈ P$), then there exists some proper
prefix $|τ2|∈\Traces^{*}$ (written $|τ2| \lessdot |τ1|$) such that $|τ2| \not∈ P$.
\end{definition}

Note that both well-typedness (``|τ| does not go wrong'') and usage cardinality
abstract safety properties.
Conveniently, guarded recursive predicates (on traces) always describe safety
properties~\citep{Spies:21,iris-lecture-notes}.

The contraposition of the above definition is
\[
  \forall |τ1|∈\Traces^{\infty}.\ (\forall |τ2|∈\Traces^{*}.\ |τ2| \lessdot |τ1| \Longrightarrow |τ2| ∈ P) \Longrightarrow |τ1| ∈ P,
\]
and we can exploit safety to extend a finitary Galois connection, such as
$α_{\mathcal{S}}$ in \Cref{fig:abstract-name-need} defined by a fold over the
trace, to infinite inputs:
\begin{lemma}[Safety extension]
\label{thm:safety-extension}
Let |hat D| be a domain with an instance for |Lat|,
$|α| : (\pow{\Traces^{*}},⊆) \rightleftarrows (|hat D|, ⊑) : |γ|$ a Galois
connection and $P ∈ \pow{\Traces}$ a safety property.
Then any domain element |hat d| that soundly approximates $P$ via |γ| on finite
traces soundly approximates $P$ on infinite traces as well:
\[
  \forall |hat d|.\ P ∩ \Traces^{*} ⊆ |γ|(|hat d|) \Longrightarrow P ∩ \Traces^{\infty} ⊆ |γinf|(|hat d|),
\]
where the \emph{extension} $|αinf| : (\pow{\Traces^{*}},⊆) \rightleftarrows (|hat D|, ⊑) : |γinf|$ of
$|α|\rightleftarrows|γ|$ is defined by the following abstraction function:
\[
  |αinf|(P) \triangleq |α|(\{ |τ2| \mid \exists |τ1|∈P.\ |τ2| \lessdot |τ1| \})
\]
\end{lemma}
\begin{proof}
First note that |αinf| uniquely determines the Galois connection by the
representation function~\citep[Section 4.3]{Nielson:99}
\[
  |βinf|(|τ1|) \triangleq |α|({\textstyle \bigcup} \{ |τ2| \mid |τ2| \lessdot |τ1| \}).
\]
Now let $|τ| ∈ P ∩ \Traces^{\infty}$.
The goal is to show that $|τ| ∈ |γinf|(|hat d|)$, which we rewrite as follows:
\begin{spec}
      τ ∈ γinf (hat d)
<==>  {- Galois -}
      βinf τ ⊑ hat d
<==>  {- Definition of |βinf| -}
      α (Cup (τ2 | τ2 <. τ1)) ⊑ hat d
<==>  {- Galois -}
      Cup (τ2 | τ2 <. τ1) ⊆ γ (hat d)
<==>  {- Definition of Union -}
      forall τ2. τ2 <. τ ==> τ2 ∈ γ (hat d)
\end{spec}
Now, $P$ is a safety property and $|τ| ∈ P$, so for any
prefix |τ2| of |τ| we have $|τ2| ∈ P ∩ \Traces^{*}$.
Hence the goal follows by assumption that $P ∩ \Traces^{*} ⊆ |γ|(|hat d|)$.
\end{proof}

From now on, we tacitly assume that all trace properties of interest are safety
properties, and that any Galois connection defined in Haskell has been extended
to infinite traces via \Cref{thm:safety-extension}.
Any such Galois connection can be used to approximate guarded fixpoints via
least fixpoints:

\begin{lemma}[Guarded fixpoint abstraction for safety extensions]
\label{thm:guarded-fixpoint-abstraction}
Let |hat D| be a domain with an instance for
|Lat|, and let $|α| : (\pow{\Traces},⊆) \rightleftarrows (|hat D|, ⊑) : |γ|$ a Galois
connection extended to infinite traces via \Cref{thm:safety-extension}.
Then, for any iteratee |f :: Traces -> Traces|,
\[
  |α|(\{ |fix f| \}) ⊑ |lfp (α . powMap f . γ)|,
\]
where |lfp (hat f)| denotes the least fixpoint of |hat f| and |powMap f :: pow Traces -> pow
Traces| is the lifting of |f| to powersets.
\end{lemma}
\begin{proof}
We should note that we are sloppy in the treatment of the \emph{later} modality
$\later$ here.
Since we have proven totality of all expressions worth considering in
\Cref{sec:totality}, the utility of being explicit in |next| is rather low (much
more so since a pen and paper proof is not type checked) and we will admit
ourselves this kind of sloppiness from now on.

Let us assume that |τ = fix f| is finite and proceed by Löb induction.
\begin{spec}
    α (set (fix f)) ⊑ lfp (α . powMap f . γ)
=   {- |fix f = f (fix f)| -}
    α (set (f (fix f)))
=   {- Commute |f| and |set| -}
    α (powMap f (set (fix f)))
⊑   {- |id ⊑ γ . α| -}
    α (powMap f (γ (α (set (fix f)))))
⊑   {- Induction hypothesis -}
    α (powMap f (γ (lfp (α . powMap f . γ))))
⊑   {- |lfp (hat f) = hat f (lfp (hat f))| -}
    lfp (α . powMap f . γ)
\end{spec}
When |τ| is infinite, the result follows by \Cref{thm:safety-extension}
and the fact that all properties of interest are safety properties.
\end{proof}

\subsection{Abstract By-name Soundness, in Detail}
\label{sec:by-name-soundness}

\begin{figure}
\[\ruleform{\begin{array}{c}
  α_{\mathcal{S}} : (|(Name :-> DName) -> DName|) \rightleftarrows (|(Name :-> hat D) -> hat D|) : γ_{\mathcal{S}}
  \\
  α_{\Environments} : \pow{|Name :-> DName|} \rightleftarrows (|Name :-> hat D|) : γ_{\Environments}
  \\
  α_{\Domain{}} : \pow{|DName|} \rightleftarrows |hat D| : γ_{\Domain{}}
  \qquad
  β_\Traces : |T (Value (ByName T))| \to |hat D|
  \qquad
\end{array}}\]
\belowdisplayskip=0pt
\arraycolsep=2pt
\[\begin{array}{lcl}
α_{\mathcal{S}}(S)(\widehat{ρ}) & = & α_\Traces(\{\  S(ρ) \mid ρ ∈ γ_{\Environments}(\widehat{ρ}) \ \}) \\
α_{\Environments}(R)(x) & = & \Lub \{\  α_{\Domain{}}(\{ρ(x)\}) \mid ρ ∈ R \ \} \\
α_{\Domain{}}(D) & = & \Lub \{\  β_\Traces(d) \mid d ∈ D \ \}  \\
\\[-0.75em]
β_\Traces(|τ|) & = & \begin{cases}
  |step e (βT^(τ))|               & \text{if |τ = Step e τ'|} \\
  |stuck|                         & \text{if |τ = Ret Stuck|} \\
  |fun (αD . powMap f . γD)|      & \text{if |τ = Ret (Fun f)|} \\
  |con k (map (αD . set) ds)|     & \text{if |τ = Ret (Con k ds)|} \\
  \end{cases} \\
\\[-0.75em]
\end{array}\]
\caption{Galois connection $α_{\mathcal{S}}$ for by-name abstraction derived from |Trace|, |Domain| and |Lat| instances on |hat D|}
\label{fig:abstract-name}
\end{figure}

We will now prove that the by-name abstraction laws in \Cref{fig:abstraction-laws}
induce an abstract interpretation of by-name evaluation via |αS| defined in
\Cref{fig:abstract-name}.
The Galois connection and the corresponding proofs are very similar, yet
somewhat simpler than for by-need because no heap update is involved.

We write $|powMap f| : \pow{A} \to \pow{B}$ to lift a function $|f| : A \to B$
to powersets, and write $|set| : A \to \pow{A}$ to construct a singleton set in
pointfree style.
Note that we will omit |ByName| newtype wrappers, as in many other preceding
sections, as well as the |Name| passed to |fun| as a poor man's De Bruijn level.

\sg{Revisit after by-need}
Compared to the by-need trace abstraction in \Cref{fig:abstract-name-need}, the
by-name trace abstraction function in \Cref{fig:abstract-name} is rather
straightforward, because it simply follows the type structure.

Note that the recursion in |βT| is defined in terms of the least fixpoint;
we discussed in \Cref{sec:safety-extension} why this is a natural choice.

We will now prove sound by-name interpretation by appealing to parametricity.

Following the semi-formal style of \citet[Section 3]{Wadler:89},
we apply the abstraction theorem to the System $F$ encoding
of the type of |eval|
\[
  |eval| : \forall X.\ \mathsf{Dict}(X) → \mathsf{Exp} → (\mathsf{Name} \pfun X) → X
\]
where $\mathsf{Dict}(|d|)$ is the type of the type class
dictionary for |(Trace d, Domain d, HasBind d)|.
The abstraction theorem yields the following assertion about relations:
\[
  (|eval|, |eval|) ∈ \forall \mathcal{X}.\ \mathsf{Dict}(\mathcal{X}) → \mathsf{Exp} → (\mathsf{Name} \pfun \mathcal{X}) → \mathcal{X}
\]
Wadler overloads the type formers with a suitable relational interpretation, which translates to
\begin{align}
  &\forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict}(R).\
  \forall |e| ∈ \mathsf{Exp}.\
  \forall (ρ_1, ρ_2) ∈ (\mathsf{Name} \pfun R). \notag \\
  &(|evalD2 {-"A"-}space e|(\mathit{inst_1})(ρ_1), |evalD2 {-"B"-}space e|(\mathit{inst_2})(ρ_2)) ∈ R \label{eqn:name-abs}
\end{align}
and in the following proof, we will instantiate $R(|d|,|hat d|) \triangleq |αD
^ ((set (d))) ⊑ hat d|$ to show the abstraction relationship.

We will need the following auxiliary lemma for the |apply| and |select| cases:
\begin{lemma}[By-name bind]
\label{thm:by-name-bind}
It is |βT^(d >>= f) ⊑ hat f (hat d)| if
\begin{enumerate}
  \item |βT^(d) ⊑ hat d|, and
  \item for all events |ev| and elements |hat d'|, |(hat step) ev ((hat f) (hat d')) ⊑ (hat f) ((hat step) ev (hat d'))|, and
  \item for all values |v|, |βT^(f v) ⊑ (hat f) (βT^(Ret v))|.
\end{enumerate}
\end{lemma}
\begin{proof}
By Löb induction.

If |d = Step ev d'|, define |hat d' := βT^(d'|.
We) get
\begin{spec}
  βT^(d >>= f) = βT^(Step ev d' >>= f) = (hat step) ev (βT^(d' >>= f))
⊑  {- Induction hypothesis at |βT^(d') = hat d'|, Monotonicity of |hat step| -}
  hat step ev ((hat f) (βT^(d'))
⊑)  {- Assumption (2) -}
  (hat f) ((hat step) ev (βT^(d'))) = (hat f) (βT^(d)
⊑)  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}

Otherwise, |d = Ret v| for some |v :: Value|.
\begin{spec}
  βT^(Ret v >>= f) = βT^(f v)
⊑  {- Assumption (3) -}
  (hat f) (βT^(Ret v)) = (hat f) (βT^(d)
⊑)  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}
\end{proof}

What follows is the sound abstraction proof by parametricity:

\begin{theorem}[Sound By-name Interpretation]
\label{thm:soundness-by-name}
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let $α_{\mathcal{S}}$ be the abstraction function from \Cref{fig:abstract-name}.
If the by-name abstraction laws in \Cref{fig:abstraction-laws} hold,
then |evalD2 (hat D)| is an abstract interpreter that is sound \wrt $α_{\mathcal{S}}$,
\[
  α_{\mathcal{S}}(|evalName1 e|) ⊑ |evalD2 (hat D) e|.
\]
\end{theorem}
\begin{proof}
Let $|inst| : \mathsf{Dict}(|DName|)$, $|hat inst| : \mathsf{Dict}(|hat D|)$ the
canonical dictionaries from the type class instance definitions.
Instantiate the free theorem \labelcref{eqn:name-abs} above as follows:
\[\begin{array}{c}
A \triangleq |DName|, B \triangleq |hat D|, R(|d|, |hat d|) \triangleq |αD ^ ((set (d))) ⊑ hat d|,
\mathit{inst_1} \triangleq |inst|, \mathit{inst_2} \triangleq |hat inst|, |e := e|
\end{array}\]
Note that $(|ρ|,|hat ρ|) ∈ (\mathsf{Name} \pfun R) \Longleftrightarrow |αE ^
((set ρ)) ⊑ hat ρ <==> ρ ∈ γE ^ ((hat ρ))|$ by simple calculation.

The above instantation yields, in Haskell,
\[
  \inferrule
    {(|inst|, |hat inst|) ∈ \mathsf{Dict}(R) \\ |ρ ∈ γE ^ ((hat ρ))|}
    {|αD ^ ((set (evalName e ρ))) ⊑ evalD (hat D) e (hat ρ)|}
\]
and since |ρ| and |hat ρ| can be chosen arbitrarily, this can be reformulated as
\[
  \inferrule
    {(|inst|, |hat inst|) ∈ \mathsf{Dict}(R)}
    {α_{\mathcal{S}}(|evalName1 e|) ⊑ |evalD2 (hat D) e|}
\]
Hence, in order to show the goal, it suffices to prove $(|inst|, |hat inst|) ∈ \mathsf{Dict}(R)$.
By the relational interpretation of products, we get one subgoal per instance method.
Note that $R(|d|, |hat d|) \Longleftrightarrow |βT^(d) ⊑ hat d|$ and it is more
direct to argue in terms of the latter.
\begin{itemize}
  \item \textbf{Case |step|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R}{(|step ev d|, |hat step ev (hat d)|) ∈ R}$. \\
    Then |βT^(Step ev d) = hat step ev (βT^(d)) ⊑ hat step ev (hat d)| by assumption and monotonicity.

  \item \textbf{Case |stuck|}.
    Goal: $(|stuck|, |hat stuck|) ∈ R$. \\
    Then |βT^(stuck) = βT^(Ret Stuck) = hat stuck|.

  \item \textbf{Case |fun|}.
    Goal: $\inferrule{\forall (|d|,|(hat d)|) ∈ R.\ (|f d|, |hat f (hat d)|) ∈ R}{(|fun f|, |hat fun (hat f)|) ∈ R}$. \\
    Then |βT^(fun f) = βT^(Ret (Fun f)) = (hat fun) (αD . powMap f . γD)| and
    it suffices to show that |αD . powMap f . γD ⊑ hat f| by monotonicity of |hat fun|.
    \begin{spec}
      (αD . powMap f . γD) (hat d)
    =  {- Unfold |powMap|, |αD|, simplify -}
      Lub (βT^(f d) | d ∈ γD (hat d))
    ⊑  {- Apply premise to |βT^(d) ⊑ hat d| -}
      hat f (hat d)
    \end{spec}

  \item \textbf{Case |apply|}.
    Goal: $\inferrule{(|d|,|(hat d)|) ∈ R \\ (|a|,|(hat a)|) ∈ R}{(|apply d a|, |hat apply (hat d) (hat a)|) ∈ R}$. \\
    |apply d a| is defined as |d >>= \v -> case v of Fun g -> g a; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-name-bind} at |hat f (hat d) := hat apply (hat d) (hat a)|.
    We get three subgoals for the premises of \Cref{thm:by-name-bind}:
    \begin{itemize}
      \item |βT^(d) ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R$.
      \item |forall ev (hat d'). (hat step) ev ((hat apply) (hat d') (hat a)) ⊑ (hat apply) ((hat step) ev (hat d')) (hat a)|: By assumption \textsc{Step-App}.
      \item |forall v. βT^(case v of Fun g -> g a; _ -> stuck) ⊑ hat apply (βT^(Ret v)) (hat a)|: \\
        By cases over |v|.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Con k ds|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat apply) ((hat con) k (hat ds)) (hat a)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Fun g|}:
            Then
            \begin{spec}
                βT^(g a)
              ⊑  {- |id ⊑ γD . αD|, rearrange -}
                (αD . powMap g . γD) (αD a)
              ⊑  {- Assumption |βT^(a) ⊑ hat a| -}
                (αD . powMap g . γD) (hat a)
              ⊑  {- Assumption \textsc{Beta-App} -}
                (hat apply) ((hat fun) (αD . powMap g . γD)) (hat a)
              =  {- Definition of |βT|, |v| -}
                (hat apply) (βT^(Ret v)) (hat a)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case |con|}.
    Goal: $\inferrule{(|ds|,|(hat ds)|) ∈ |[{-"R"-}space]|}{(|con k ds|, |(hat con) k (hat ds)|) ∈ R}$. \\
    Then |βT^(con k ds) = βT^(Ret (Con k ds)) = (hat con) k (map (αD . set) ds)|.
    The assumption $(|ds|,|(hat ds)|) ∈ |[{-"R"-}space]|$ implies |map (αD . set) ds ⊑ hat ds| and
    the goal follows by monotonicity of |hat con|.

  \item \textbf{Case |select|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R \\ (|alts|,|hat alts|) ∈ |Tag :-> ([{-"R"-}space] -> {-"R"-}space)|}{(|select d alts|, |(hat select) (hat d) (hat alts)|) ∈ R}$. \\
    |select d fs| is defined as |d >>= \v -> case v of Con k ds || k ∈ dom alts  -> (alts ! k) ds; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-name-bind} at |hat f (hat d) := hat select (hat d) (hat alts)|.
    We get three subgoals for the premises of \Cref{thm:by-name-bind}:
    \begin{itemize}
      \item |βT^(d) ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R$.
      \item |forall ev (hat d'). (hat step) ev ((hat select) (hat d') (hat alts)) ⊑ (hat select) ((hat step) ev (hat d')) (hat alts)|: By assumption \textsc{Step-Sel}.
      \item |forall v. βT^(case v of Con k ds || k ∈ dom alts  -> (alts ! k) ds; _ -> stuck) ⊑ (hat select) (βT^(Ret v)) (hat alts)|: \\
        By cases over |v|. The first three all correspond to when the continuation of |select| gets stuck.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT^(stuck) = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Con k ds|, $|k| ∈ |dom alts|$}:
            Then
            \begin{spec}
                βT^((alts ! k) ds)
              ⊑  {- |id ⊑ γD . αD|, rearrange -}
                (αD . powMap (alts ! k) . map γD) (map (αD . set) ds)
              ⊑  {- Assumption $(|alts|,|hat alts|) ∈ |Tag :-> ([{-"R"-}space] -> {-"R"-}space)|$ -}
                (hat alts ! k) (map (αD . set) ds)
              ⊑  {- Assumption \textsc{Beta-Sel} -}
                (hat select) ((hat con) k (map (αD . set) ds)) (hat alts)
              =  {- Definition of |βT|, |v| -}
                (hat select) (βT^(Ret v)) (hat alts)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case |bind|}.
    Goal: $\inferrule{(\forall (|d|,|(hat d)|) ∈ R.\ (|rhs d|, |hat rhs (hat d)|) ∈ R) \\ (\forall (|d|,|(hat d)|) ∈ R.\ (|body d|, |hat body (hat d)|) ∈ R)}
                     {(|bind rhs body|, |(hat bind) (hat rhs) (hat body)|) ∈ R}$. \\
    It is |bind rhs body = body (fix rhs)| and |(hat body) (lfp (hat rhs)) ⊑ (hat bind) (hat rhs) (hat body)| by Assumption \textsc{Bind-ByName}.
    Let us first establish that $(|fix rhs|, |lfp (hat rhs)|) ∈ R$, leaning on
    our theory about safety extension in \Cref{sec:safety-extension}:
    \begin{spec}
      αD ^ ((set (fix rhs)))
    ⊑  {- By \Cref{thm:safety-extension} -}
      lfp (αD . powMap rhs . γD)
    =  {- Unfolding |powMap|, |αD| -}
      lfp (\(hat d) -> Lub (βT^(rhs d) | d ∈ γD (hat d))
    ⊑  {- Apply assumption to $|αD ^ ((set d)) ⊑ αD (γD (hat d)) ⊑ hat d <==> | (|d|,|hat d|) ∈ R$ -}
      lfp (hat rhs)
    \end{spec}
    Applying this fact to the second assumption proves
    $(|body (fix rhs)|, |(hat body) (lfp (hat rhs))|) ∈ R$ and thus the goal.
\end{itemize}
\end{proof}

\subsection{Abstract By-need Soundness, in Detail}
\label{sec:by-need-soundness}

The goal of this section is to prove \Cref{thm:soundness-by-name} correct,
which is applicable for analyses that are sound both \wrt to by-name
as well as by-need, such as usage analysis or perhaps type analysis in
\Cref{sec:type-analysis} (we have however not proven it so).

The setup in \Cref{sec:by-name-soundness} with its Galois connection in
\Cref{fig:abstract-name} is somewhat similar to the Galois connection in
\Cref{fig:abstract-name-need}, however for by-need abstraction the Galois
connection for domain elements |d :: DNeed| is indexed by a heap \wrt to which the
element is abstracted.
We will later see how this indexing yields a Kripke-style logical relation
as the soundness condition, and that, sadly, such a relation cannot easily be
proven by appealing to parametricity.

The reason we need to index correctness relations by a heap is as follows:
Although in \Cref{sec:evaluation-strategies} we considered an element |d|
as an atomic denotation, such a denotation actually only carries meaning when it
travels together with a heap |μ| that ties the adresses that |d| references to
actual meaning.

There are \emph{many} elements (functions!) |d :: DNeed|, many with very
surprising behavior, but we are only interested in elements \emph{definable}
by our interpreter:

\begin{definition}[Definable by-need entities]
  \label{defn:definable}
  We write |needd d|, |needenv ρ| or |needheap μ| to say that the by-need
  element |d|, environment |ρ| or heap |μ| is \emph{definable}, defined as
  \begin{itemize}
    \item |needenv ρ := forall x ∈ dom ρ. exists x a. ρ ! x = step (Look y) (fetch a)|.
    \item |adom ρ := set (a || ρ ! x = step (Look y) (fetch a))|.
    \item |needd d := exists e ρ. needenv ρ /\ d = evalNeed2 e ρ|.
    \item |adom d := adom ρ| where |d = evalNeed2 e ρ|.
    \item |needheap μ := forall a. exists d. μ ! a = memo a d /\ Later (needd d /\ adom d ⊆ dom μ)|.
  \end{itemize}
  We refer to |adom d| (resp. |adom ρ|) as the \emph{address domain} of |d| (resp. |ρ|).
\end{definition}

Henceforth, we assume that all elements |d|, environments |ρ| and heaps |μ| of
interest are definable in this sense.
It is easy to see that definability is preserved by |evalNeed2| whenever the
environment or heap is extended; the important case is the implementation of
|bind|.

%A sound by-name analysis must only satisfy the two additional abstraction laws
%\textsc{Step-Inc} and \textsc{Update} in \Cref{fig:abstraction-laws} to yield
%sound results for by-need as well.
%These laws make intuitive sense, because |Upd| events cannot be observed in a
%by-name trace and hence must be ignored.
%Other than |Upd| steps, by-need evaluation makes fewer steps than by-name
%evaluation, so \textsc{Step-Inc} asserts that dropping steps never invalidates
%the result.

The indexed family of abstraction functions improves whenever the heap with
which we index is ``more evaluated'' --- the binary relation |(~>)| (``progresses
to'') on heaps in \Cref{fig:heap-progression} captures this progression.
It is defined as the smallest preorder (rules \progresstorefl, \progresstotrans)
that also contains rules \progresstoext and \progresstomemo.
The former corresponds to extending the heap in the |Let| case.
The latter corresponds to memoising a heap entry after it was evaluated in the
|Var| case.

\begin{figure}
  \[\begin{array}{c}
    \ruleform{ μ_1 \progressto μ_2 }
    \\ \\[-0.5em]
    \inferrule[\progresstorefl]{|needheap μ|}{|μ ~> μ|}
    \qquad
    \inferrule[\progresstotrans]{|μ1 ~> μ2| \quad |μ2 ~> μ3|}{|μ1 ~> μ3|}
    \qquad
    \inferrule[\progresstoext]
      {|a| \not∈ |dom μ| \quad |adom ρ ⊆ dom μ ∪ set a|}
      {|μ ~> ext μ a (memo a (evalNeed2 e ρ))|}
    \\ \\[-0.5em]
    \inferrule[\progresstomemo]
      {|μ1 ! a = memo a (evalNeed2 e ρ1)| \quad |Later (evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2))|}
      {|μ1 ~> ext μ2 a (memo a (evalNeed2 v ρ2))|}
    \\[-0.5em]
  \end{array}\]
  \caption{Heap progression relation}
  \label{fig:heap-progression}
\end{figure}

Heap progression is the primary mechanism by which we can reason about the
meaning of programs:
If |μ1| progresses to |μ2| (\ie |μ1 ~> μ2|), and |adom d ⊆ dom μ1|, then
|d μ1| has the same by-name semantics as |d μ2|, with the latter potentially
terminating in fewer steps.
We will exploit this observation in the abstract in
\Cref{thm:heap-progress-mono}, and now work towards proof.

To that end, it is important to build witnesses of |μ1 ~> μ2| in the first
place:

\begin{lemma}[Evaluation progresses the heap]
\label{thm:eval-progression}
If |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|, then |μ1 ~> μ2|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    Let |many ev1 := tail (init (many ev))|.
    \begin{spec}
        (ρ1 ! x) μ1
    =   {- |needenv ρ1|, some |y|, |a| -}
        Step (Look y) (fetch a μ1)
    =   {- Unfold |fetch| -}
        Step (Look y) ((μ1 ! a) μ1)
    =   {- |needheap μ|, some |e|, |ρ3| -}
        Step (Look y) (memo a (evalNeed e ρ3 μ1))
    =   {- Unfold |memo| -}
        Step (Look y) (evalNeed e ρ3 μ1 >>= upd)
    =   {- |evalNeed e ρ3 μ1 = many (Step ev1) (evalNeed v ρ2 μ3)| for some |μ3|, unfold |>>=|, |upd| -}
        Step (Look y) (many (Step ev1) (evalNeed v ρ2 μ3 >>= \v μ3 ->
          Step Upd (Ret (v, ext μ3 a (memo a (return v))))))
    \end{spec}
    Now let |sv :: Value (ByNeed T)| be the semantic value such that |evalNeed v ρ2 μ3 = Ret (sv, μ3)|.
    \begin{spec}
    =   {- |evalNeed v ρ2 μ3 = Ret (sv, μ3)| -}
        Step (Look y) (many (Step ev1) (Step Upd (Ret (sv, ext μ3 a (memo a (return sv))))))
    =   {- Refold |evalNeed v ρ2|, |many ev = [Look y] ++ many ev1 ++ [Upd]| -}
        many (Step ev) (evalNeed v ρ2 (ext μ3 a (memo a (evalNeed2 v ρ2))))
    =   {- Determinism of |evalNeed2|, assumption -}
        many (Step ev) (evalNeed v ρ2 μ2)
    \end{spec}
    We have
    \begin{align}
      & |μ1 ! a = memo a (evalNeed2 e ρ3)| \label{eqn:eval-progression-memo} \\
      & |Later (evalNeed e ρ3 μ1 = many (Step ev1) (evalNeed v ρ2 μ3))| \label{eqn:eval-progression-eval} \\
      & |μ2 = ext μ3 a (memo a (evalNeed2 v ρ2))| \label{eqn:eval-progression-heaps}
    \end{align}
    We can apply rule \progresstomemo to \Cref{eqn:eval-progression-memo} and \Cref{eqn:eval-progression-eval}
    to get |μ1 ~> ext μ3 a (memo a (evalNeed2 v ρ2))|, and rewriting along
    \Cref{eqn:eval-progression-heaps} proves the goal.
  \item \textbf{Case} |Lam x body|, |ConApp k xs|:
    Then |μ1 = μ2| and the goal follows by \progresstorefl.
  \item \textbf{Case} |App e1 x|:
    Let us assume that |evalNeed e1 ρ1 μ1 = many (Step ev1) (evalNeed (Lam y e2) ρ3 μ3)| and
    |evalNeed e2 (ext ρ3 y (ρ ! x)) μ3 = many (Step ev2) (evalNeed v ρ2 μ2)|, so that
    |μ1 ~> μ3|, |μ3 ~> μ2| by the induction hypothesis.
    The goal follows by \progresstotrans, because
    |many ev = [App1] ++ many ev1 ++ [App2] ++ many ev2|.
  \item \textbf{Case} |Case e1 alts|:
    Similar to |App e1 x|.
  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        evalNeed (Let x e1 e2) ρ1 μ1
    =   {- Unfold |evalNeed2| -}
        bind  (\d1 -> evalNeed e1 (ext ρ1 x (step (Look x) d1)))
              (\d1 -> step Let1 (evalNeed e2 (ext ρ1 x (step (Look x) d1))))
              μ1
    =   {- Unfold |bind|, |a := nextFree μ| with $|a| \not\in |dom μ|$ -}
        step Let1 (evalNeed e2 (ext ρ1 x (step (Look x) (fetch a)))
                               (ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a)))))))
    \end{spec}
    At this point, we can apply the induction hypothesis to |evalNeed2 e2 (ext ρ1 x
    (step (Look x) (fetch a)))| to conclude that
    |ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a))))) ~> μ2|.

    On the other hand, we have
    |μ1 ~> ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a)))))|
    by rule \progresstoext (note that $|a| \not∈ |dom μ|$), so the goal follows
    by \progresstotrans.
\end{itemize}
\end{proof}

%\Cref{thm:eval-progression} exposes nested structure in \progresstomemo.
%For example, if |μ1 ~> ext μ2 a (memo a (evalNeed2 v ρ2))| is the result of applying
%rule \progresstomemo, then we obtain a proof that the memoised expression
%|evalNeed2 e ρ1 μ1 = many (Step ev) (evalNeed2 v ρ2 μ2)|, and this
%evaluation in turn implies that |μ1 ~> μ2|.

It is often necessary, but non-trivial to cope with equality of elements |d|
modulo readressing.
Fortunately, we only need to consider equality in the abstract, that is,
modulo |βD|, where |βD^(μ)^(d) := αD^(μ)^((set d))| is the representation
function of |αD|.

\begin{lemma}[Abstract readdressing]
\label{thm:abstract-readdressing}
If |a1 ∈ dom μ1|, but $|a2| \not∈ |dom μ1|$,
then |βD^(μ1)^(evalNeed2 e ρ1) = βD^(μ2)^(evalNeed2 e ρ2)|,
where |ρ2| and |μ2| are renamings of |ρ1| and |μ1| defined as follows:
\begin{itemize}
  \item $|ρ2 ! x| = \begin{cases} |step (Look y) (fetch a2)| & \textup{if }|ρ1 ! x = step (Look y) (fetch a1)| \\ |ρ1 ! x| & \textup{otherwise} \end{cases}$
  \item $|a1| \not∈ |dom μ2|$
  \item $|μ2 ! a| = \begin{cases} |memo a2 (evalNeed2 e1 ρ4)| & \textup{if |a = a2|, |μ1 ! a1 = memo a1 (evalNeed2 e1 ρ3)|, |ρ4| renaming of |ρ3|} \\ |memo a (evalNeed2 e1 ρ4)| & \textup{where |μ1 ! a = memo a (evalNeed2 e1 ρ3)|, |ρ4| renaming of |ρ3|} \end{cases}$
\end{itemize}
\end{lemma}
\begin{proof}
Simple proof by Löb induction and cases on |e|.
\end{proof}

Readressing allows us to prove an abstract pendant of the venerable \emph{frame
rule} of separation logic:

\begin{lemma}[Abstract frame rule]
\label{thm:abstract-frame}
If |adom ρ ⊆ dom μ| and $|a| \not∈ |dom μ|$,
then
\[|βD^(μ)^(evalNeed2 e ρ) = βD^((ext μ a (memo a d)))^(evalNeed2 e ρ)|.\]
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
Only the cases that access the heap are interesting.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    We never fetch |a|, because $|a| \not∈ |adom ρ|$.
    Furthermore, the environment |ρ1| of the heap entry |evalNeed2 e1 ρ1| thus
    fetched satisfies |adom ρ1 ⊆ dom μ| so that we may apply the induction
    hypothesis.
  \item \textbf{Case} |Let x e1 e2|:
    Follows by the induction hypothesis after readressing the extended heap
    (\Cref{thm:abstract-readdressing}) so that the induction hypothesis can be applied.
\end{itemize}
\end{proof}

The frame rule in turn is important to show that heap progression preserves the
results of the abstraction function:

\begin{lemma}[Heap progression preserves abstraction]
  \label{thm:heap-progress-mono}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName}
  and \textsc{Step-Inc} from \Cref{fig:abstraction-laws}.
  \[ |μ1 ~> μ2 /\ adom d ⊆ dom μ1 ==> βD^(μ2)^(d) ⊑ βD^(μ1)^(d)|. \]
\end{lemma}
\begin{proof}
By Löb induction.
Element |d| is definable of the form |d = evalNeed2 e ρ| for definable |ρ|.
Proceed by cases on |e|. Only the |Var| and |Let| cases are interesting.
\begin{itemize}
  \item \textbf{Case} |Let x e1 e2|:
    We need to readdress the extended heaps with \Cref{thm:abstract-readdressing} so that
    |ext μ1 a1 (memo a1 d1) ~> ext μ2 a1 (memo a1 d1)| is preserved, in which case the goal follows by applying the
    induction hypothesis.
  \item \textbf{Case} |Var x|:
    Let us assume that |μ1 ~> μ2| and |adom d ⊆ dom μ1|.
    We get |d = step (Look y) (fetch a)| for some |y| and |a|.
    Furthermore, let us abbreviate |memo a (evalNeed2 ei ρi) := μi ! a|.
    The goal is to show
    \[
      |step (Look y) (βD^(μ2)^(memo a (evalNeed2 e2 ρ2))) ⊑ step (Look y) (βD^(μ1)^(memo a (evalNeed2 e1 ρ1)))|.
    \]
    Monotonicity allows us to drop the |step (Look y)| context
    \[
      |Later (βD^(μ2)^(memo a (evalNeed2 e2 ρ2)) ⊑ βD^(μ1)^(memo a (evalNeed2 e1 ρ1)))|.
    \]
    Now we proceed by induction on |μ1 ~> μ2|, which we only use to prove correct the
    reflexive and transitive closure in \progresstorefl and \progresstotrans.
    \begin{itemize}
      \item \textbf{Case} \progresstorefl:
        Then |μ1 = μ2| and hence |βD^(μ1) = βD^(μ2)|.
      \item \textbf{Case} \progresstotrans:
        Apply the induction hypothesis to the sub-derivations and apply transitivity
        of |⊑|.

      \item \textbf{Case} $\inferrule*[vcenter,left=\progresstoext]{|a1| \not∈ |dom μ1| \quad |adom ρ ⊆ dom μ1 ∪ set a1|}{|μ1 ~> ext μ1 a1 (memo a1 (evalNeed2 e ρ))|}$:\\
        We get to refine |μ2 = ext μ1 a1 (memo a1 (evalNeed2 e ρ))|.
        Since |a ∈ dom μ1|,
        we have $|a1| \not= |a|$
        and thus |μ1 ! a = μ2 ! a|, thus |e1=e2|, |ρ1=ρ2|.
        We can exploit monotonicity of |Later| and simplify the goal to
        \begin{spec}
          βD^((ext μ1 a1 (memo a1 (evalNeed2 e ρ))))^(memo a (evalNeed2 e1 ρ1)) ⊑ βD^(μ1)^(memo a (evalNeed2 e1 ρ1))
        \end{spec}
        This follows by applying the abstract frame rule (\Cref{thm:abstract-frame}).

      \item \textbf{Case} $\inferrule*[vcenter,left=\progresstomemo]{|μ1 ! a1 = memo a1 (evalNeed2 e ρ3)| \quad |Later (evalNeed e ρ3 μ1 = many (Step ev) (evalNeed v ρ4 μ3))|}{|μ1 ~> ext μ3 a1 (memo a1 (evalNeed2 v ρ4))|}$:\\
        We get to refine |μ2 = ext μ3 a1 (memo a1 (evalNeed2 v ρ2))|.
        When $|a1| \not= |a|$, we have |μ1 ! a = μ2 ! a| and the goal follows as in the \progresstoext case.
        Otherwise, |a = a1|, |e1 = e|, |ρ3 = ρ1|, |ρ4 = ρ2|, |e2 = v|.

        The goal can be simplified to
        |Later (βD^(μ2)^(memo a (evalNeed2 v ρ2)) ⊑ βD^(μ1)^(memo a (evalNeed2 e1 ρ1)))|.
        We reason under |Later| as follows
        \begin{spec}
          βD^(μ2)^(memo a (evalNeed2 v ρ2))
        = {- |μ2 ! a = memo a (evalNeed2 v ρ2)| -}
          βT^(Step Update (evalNeed v ρ2 μ2))
        = {- |μ2 = ext μ3 a (memo a (evalNeed2 v ρ2))| -}
          βD^(μ3)^(memo a (evalNeed2 v ρ2))
        ⊑   {- |evalNeed e1 ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ3)|, \textsc{Step-Inc} -}
          βD^(μ1)^(memo a (evalNeed2 e1 ρ1))
        \end{spec}
    \end{itemize}
\end{itemize}
\end{proof}

The preceding lemma corresponds to the $\UpdateT$ step of the preservation
\Cref{thm:preserve-absent} where we (and \citet{Sergey:14}) resorted to
hand-waving.
Here, we hand-wave no more!

In order to prove the main soundness \Cref{thm:soundness-by-need},
we need two more auxiliary lemmas about |(>>=)| and environment
access.

\begin{lemma}[By-need bind]
\label{thm:by-need-bind}
It is |βT^((d >>= f) μ1) ⊑ hat f (hat d)| if
\begin{enumerate}
  \item |βT^(d μ1) ⊑ hat d|, and
  \item for all events |ev| and elements |hat d'|, |(hat step) ev ((hat f) (hat d')) ⊑ (hat f) ((hat step) ev (hat d'))|, and
  \item for all values |v| and heaps |μ2| such that |μ1 ~> μ2|, |βT^(f v μ2) ⊑ (hat f) (βT^(Ret (v, μ2)))|.
\end{enumerate}
\end{lemma}
\begin{proof}
By Löb induction.

If |d μ1 = Step ev (d' μ1')|, define |hat d' := βT^(d' μ1')| and note that
|μ1 ~> μ1'| for the definable |d| as in \Cref{thm:eval-progression} (we will
always instantiate the original |d| to |evalNeed2 e ρ|).
We get
\begin{spec}
  βT^((d >>= f) μ1) = βT^(Step ev ((d' >>= f) μ1')) = (hat step) ev (βT^((d' >>= f) μ1'))
⊑  {- Induction hypothesis at |βT^(d' μ1') = hat d'|, Monotonicity of |hat step| -}
  hat step ev ((hat f) (βT^(d' μ1')))
⊑  {- Assumption (2) -}
  (hat f) ((hat step) ev (βT^(d' μ1'))) = (hat f) (βT^(d μ1))
⊑  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}
Note that in order to apply the induction hypothesis at |μ1'| above, we need
refine assumption (3) to apply at any |μ2| such that |μ1' ~> μ2|.
This would not be possible without generalising for any such |μ2| in the first
place.

Otherwise, |d = return v| for some |v :: Value|.
\begin{spec}
  βT^((return v >>= f) μ1) = βT^(f v μ1)
⊑  {- Assumption (3) -}
  (hat f) (βT^(Ret v, μ1)) = (hat f) (βT^(d μ1))
⊑  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}
\end{proof}

\begin{lemma}[By-need environment unrolling]
\label{thm:by-need-env-unroll}
Let |hat D| a domain with instances for |Trace|, |Domain|, |HasBind| and |Lat|,
satisfying $\textsc{Update}$ from \Cref{fig:abstraction-laws},
and let |μ1 := (ext μ a (memo a (evalNeed e1 ρ1))), ρ1 := ext ρ x (step (Look x) (fetch a))|. \\
If |Later (forall e ρ μ. βT^(evalNeed e ρ μ) ⊑ (evalD (hat D) e (βD^(μ) << ρ)))|,
then |βD^(μ1)^(ρ1 ! x) ⊑ step (Look x) (evalD (hat D) e1 (βD^(μ1) << ρ1))|.
\end{lemma}
\begin{proof} $ $
\begin{spec}
  βD^(μ1)^(ρ1 ! x)
=   {- |needenv ρ1|, |needheap μ1|, unfold |βD| and |fetch a| -}
  step (Look x) (βT^(memo a (evalNeed e1 ρ1) μ1))
=   {- Unfold |memo a| -}
  step (Look x) (βT^((evalNeed e1 ρ1 >>= upd) μ1))
⊑   {- Apply \Cref{thm:by-need-bind}; see below -}
  step (Look x) (evalD (hat D) e1 (βD^(μ1) << ρ1))
\end{spec}

In the last step, we apply \Cref{thm:by-need-bind} under |step (Look x)|, which
yields three subgoals (under $\later$):
\begin{itemize}
  \item |βT^(evalNeed e1 ρ1 μ1) ⊑ evalD (hat D) e1 (βD^(μ1) << ρ1)|:
    By assumption.
  \item |forall ev (hat d'). (hat step) ev (id (hat d')) ⊑ id ((hat step) ev (hat d'))|:
    By reflexivity.
  \item |forall v μ2. μ1 ~> μ2 ==> βT^(upd v μ2) ⊑ id (βT^(Ret (v, μ2)))|:
    If |v = Stuck|, then |upd v μ2 = Ret (v, μ2)| and the goal follows by reflexivity.
    Otherwise, |upd v μ2 = Step Update (Ret (v, ext μ2 a (memo a (return v))))|.
    By $\textsc{Update}$, it suffices to show |βT^(Ret (v, ext μ2 a (memo a (return v)))) ⊑ βT^(Ret (v, μ2))|.
    It is |μ2 ~> ext μ2 a (memo a (return v))| (either by \progresstorefl or \progresstomemo)
    and the goal follows by \Cref{thm:heap-progress-mono}.
\end{itemize}
\end{proof}

Finally, we can prove \Cref{thm:soundness-by-need}:

% Keep up to date with {thm:soundness-by-need}
{
\renewcommand{\thetheorem}{\ref{thm:soundness-by-need}}
\begin{theorem}[Sound By-need Interpretation]
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let $α_{\mathcal{S}}$ be the abstraction function from \Cref{fig:abstract-name-need}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |evalD2 (hat D)| is an abstract interpreter that is sound \wrt $α_{\mathcal{S}}$,
that is,
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
\end{theorem}
\addtocounter{theorem}{-1}
}
\begin{proof}
We simplify our proof obligation to the single-trace case:
\begin{spec}
    forall e. αS^(evalNeed1 e) ⊑ evalD2 (hat D) e
  <==>  {- Unfold |αS|, |αT| -}
    forall e (hat ρ). Lub (βT^(evalNeed e ρ μ) | (ρ,μ) ∈ γE^((hat ρ))) ⊑ (evalD (hat D) e (hat ρ))
  <==>  {- |(ρ,μ) ∈ γE^((hat ρ)) <==> αE^((set (ρ,μ))) ⊑ hat ρ|, unfold |αE|, refold |βD| -}
    forall e ρ μ. βT^(evalNeed e ρ μ) ⊑ (evalD (hat D) e (βD^(μ) << ρ))
\end{spec}
where |βT := αT . set| and |βD^(μ) := αD^(μ) . set| are the representation
functions corresponding to |αT| and |αD|.
We proceed by Löb induction and cases over |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The case $|x| \not∈ |dom ρ|$ follows by reflexivity.
    Otherwise, let |ρ ! x = Step (Look y) (fetch a)|.
    \begin{spec}
        βT^((ρ ! x) μ)
    ⊑   {- \Cref{thm:by-need-env-unroll} -}
        step (Look y) (evalD (hat D) e1 (βD^(μ) << ρ1))
    =   {- Refold |βD| -}
        βD^(μ)^(ρ ! x)
    \end{spec}

  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        βT^(evalNeed (Lam x body) ρ μ)
    =   {- Unfold |evalNeed2|, |βT| -}
        fun (\(hat d) -> Lub (step App2 (βT^(evalNeed body (ext ρ x d) μ)) | d ∈ γD^(μ) (hat d)))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> Lub (step App2 (evalD (hat D) body (βD^(μ) << (ext ρ x d))) | d ∈ γD^(μ) (hat d)))
    ⊑   {- Least upper bound / |αD^(μ) . γD^(μ) ⊑ id| -}
        fun (\(hat d) -> step App2 (evalD (hat D) body (ext (βD^(μ) << ρ) x (hat d))))
    =   {- Refold |evalD (hat D)| -}
        evalD (hat D) (Lam x body) (βD^(μ) << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k xs|:
    \begin{spec}
        βT^(evalNeed (ConApp k xs) ρ μ)
    =   {- Unfold |evalNeed2|, |βT| -}
        con k (map ((βD^(μ) << ρ) !) xs)
    =   {- Refold |evalD (hat D)| -}
        evalD (hat D) (Lam x body) (βD^(μ) << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    Very similar to the |apply| case in \Cref{thm:soundness-by-name}.
    There is one exception: We must apply \Cref{thm:heap-progress-mono}
    to argument denotations.

    The |stuck| case is simple.
    Otherwise, we have
    \begin{spec}
      βT^(evalNeed (App e x) ρ μ)
    =   {- Unfold |evalNeed2|, |βT|, |apply| -}
      step App1 ((evalNeed e ρ >>= \v -> case v of Fun f -> f (ρ ! x); _ -> stuck) μ)
    ⊑   {- Apply \Cref{thm:by-need-bind}; see below -}
      step App1 ((hat apply) (evalD (hat D) e (βD^(μ) << ρ)) (βD^(μ)^(ρ ! x)))
    =   {- Refold |evalD (hat D)| -}
      evalD (hat D) e (βD^(μ) << ρ)
    \end{spec}

    In the $⊑$ step, we apply \Cref{thm:by-need-bind} under |step App1|, which
    yields three subgoals (under $\later$):
    \begin{itemize}
      \item |βT^(evalNeed e ρ μ) ⊑ evalD (hat D) e (βD^(μ) << ρ)|:
        By induction hypothesis.
      \item |forall ev (hat d'). (hat step) ev ((hat apply) (hat d') (βD^(μ)^(ρ ! x))) ⊑ (hat apply) ((hat step) ev (hat d')) (βD^(μ)^(ρ ! x))|:
        By assumption \textsc{Step-App}.
      \item |forall v μ2. μ ~> μ2 ==> βT^((case v of Fun g -> g (ρ ! x); _ -> stuck) μ2) ⊑ (hat apply) (βT^(Ret (v, μ2))) (βD^(μ)^(ρ ! x))|:
        By cases over |v|.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Con k ds|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat apply) ((hat con) k (hat ds)) (hat a)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Fun g|}:
            Note that |g| has a parametric definition, of the form |(\d -> step App2 (eval e1 (ext ρ x d)))|.
            This is important to apply \textsc{Beta-App} below.
            \begin{spec}
                βT^(g (ρ!x) μ2)
              ⊑  {- |id ⊑ γD^(μ2) . αD^(μ2)|, rearrange -}
                (αD^(μ2) . powMap g . γD^(μ2)) (βD^(μ2)^(ρ!x))
              ⊑  {- |βD^(μ2)^(ρ!x) ⊑ βD^(μ)^(ρ!x)| by {thm:heap-progress-mono} -}
                (αD^(μ2) . powMap g . γD^(μ2)) (βD^(μ)^(ρ!x))
              ⊑  {- Assumption \textsc{Beta-App} -}
                (hat apply) ((hat fun) (αD^(μ2) . powMap g . γD^(μ2))) (βD^(μ)^(ρ!x))
              =  {- Definition of |βT|, |v| -}
                (hat apply) (βT^(Ret v, μ2)) (βD^(μ)^(ρ!x))
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case} |Case e alts|:
    Very similar to the |select| case in \Cref{thm:soundness-by-name}.

    The cases where the interpreter returns |stuck| follow by parametricity.
    Otherwise, we have
    (for the suitable definition of |hat alts|, which satisfies
    |αD^(μ2) . powMap (alts ! k) . map (γD^(μ2)) ⊑ (hat alts) ! k| by induction)
    \begin{spec}
      βT^(evalNeed (Case e alts) ρ μ)
    =   {- Unfold |evalNeed2|, |βT|, |apply| -}
      step Case1 ((evalNeed e ρ >>= \v -> case v of Con k ds | k ∈ dom alts -> (alts!k) ds; _ -> stuck) μ)
    ⊑   {- Apply \Cref{thm:by-need-bind}; see below -}
      step Case1 ((hat select) (evalD (hat D) e (βD^(μ) << ρ)) (hat alts))
    =   {- Refold |evalD (hat D)| -}
      evalD (hat D) e (βD^(μ) << ρ)
    \end{spec}

    In the $⊑$ step, we apply \Cref{thm:by-need-bind} under |step Case1|, which
    yields three subgoals (under $\later$):
    \begin{itemize}
      \item |βT^(evalNeed e ρ μ) ⊑ evalD (hat D) e (βD^(μ) << ρ)|:
        By induction hypothesis.
      \item |forall ev (hat d'). (hat step) ev ((hat select) (hat d') (hat alts)) ⊑ (hat select) ((hat step) ev (hat d')) (hat alts)|:
        By assumption \textsc{Step-Select}.
      \item |forall v μ2. μ ~> μ2 ==> βT^((case v of Con k ds || k ∈ dom alts -> (alts ! k) ds; _ -> stuck) μ2) ⊑ (hat select) (βT^(Ret (v, μ2))) (hat alts)|:
        By cases over |v|.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Con k ds|, $|k| ∈ |dom alts|$}:
            Note that |alts| has a parametric definition.
            This is important to apply \textsc{Beta-Sel} below.
            \begin{spec}
                βT^((alts ! k) ds μ2)
              ⊑  {- |id ⊑ γD^(μ2) . αD^(μ2)|, rearrange -}
                (αD^(μ2) . powMap (alts ! k) . map (γD^(μ2))) (map (αD^(μ2) . set) ds)
              ⊑  {- Abstraction property of |hat alts| -}
                (hat alts ! k) (map (αD^(μ2) . set) ds)
              ⊑  {- Assumption \textsc{Beta-Sel} -}
                (hat select) ((hat con) k (map (αD^(μ2) . set) ds)) (hat alts)
              =  {- Definition of |βT|, |v| -}
                (hat select) (βT^(Ret v)) (hat alts)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case} |Let x e1 e2|:
    We can make one step to see
    \begin{spec}
      evalNeed (Let x e1 e2) ρ μ = Step Let1 (evalNeed e2 ρ1 μ1),
    \end{spec}
    where |ρ1 := ext ρ x (step (Look x) (fetch a))|,
    |a := nextFree μ|,
    |μ1 := ext μ a (memo a (evalNeed2 e1 ρ1))|.

    Then |(βD^(μ1) << ρ1) ! y ⊑ (βD^(μ) << ρ) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:heap-progress-mono},
    and |(βD^(μ1) << ρ1) ! x = step (Look x) (βD^(μ1)^(evalNeed e1 ρ1))|.
    \begin{spec}
        βT^(evalNeed (Let x e1 e2) ρ μ)
    =   {- Unfold |evalNeed2| -}
        βT^(bind  (\d1 -> evalNeed2 e1 ρ1) (\d1 -> Step Let1 (evalNeed2 e2 ρ1)) μ)
    =   {- Unfold |bind|, $|a| \not\in |dom μ|$, unfold |βT| -}
        step Let1 (βT^(evalNeed e2 ρ1 μ1))
    ⊑   {- Induction hypothesis -}
        step Let1 (eval e2 (βD^(μ1) << ρ1))
    ⊑   {- By \Cref{thm:by-need-env-unroll}, unfolding |ρ1|  -}
        step Let1 (eval e2 (ext (βD^(μ1) << ρ) x (step (Look x) (eval e1 (ext (βD^(μ1) << ρ) x (βD^(μ1)^(ρ1 ! x)))))))
    ⊑   {- Least fixpoint -}
        step Let1 (eval e2 (ext (βD^(μ1) << ρ) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βD^(μ1) << ρ) x (hat d1)))))))
    ⊑   {- |βD^(μ1)^(ρ ! x) ⊑ βD^(μ)^(ρ ! x)| by \Cref{thm:heap-progress-mono} -}
        step Let1 (eval e2 (ext (βD^(μ) << ρ) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βD^(μ) << ρ) x (hat d1)))))))
    =   {- Partially unroll fixpoint -}
        step Let1 (eval e2 (ext (βD^(μ) << ρ) x (step (Look x) (lfp (\(hat d1) -> eval e1 (ext (βD^(μ) << ρ) x (step (Look x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = βD^(μ) << ρ| -}
        bind  (\d1 -> eval e1 (ext (βD^(μ) << ρ) x (step (Look x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (βD^(μ) << ρ) x (step (Look x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βD^(μ) << ρ)| -}
        eval (Let x e1 e2) (βD^(μ) << ρ)
    \end{spec}
\end{itemize}
\end{proof}

\subsection{Parametricity and Relationship to Kripke-style Logical Relations}

We remarked right at the begin of the previous subsection that the Galois
connection in \Cref{fig:abstract-name-need} is really a family of definitions
indexed by a heap |μ|.
It is not possible to regard the ``abstraction of a |d|'' in isolation;
rather, \Cref{thm:heap-progress-mono} expresses that once an ``abstraction of a |d|''
holds for a particular heap |μ1|, this abstraction will hold for any heap |μ2|
that the semantics may progress to.

Unfortunately, this indexing also means that we cannot apply parametricity
to prove the sound abstraction \Cref{thm:soundness-by-need}, as we did for
by-name abstraction.
Such a proof would be bound to fail whenever the heap is extended (in |bind|),
because then the index of the soundness relation must change as well.
Concretely, we would need roughly the following free theorem
\[
  |(bind, bind) ∈ Later (Later (Rel(ext μ a d)) -> Rel(ext μ a d)) -> (Later (Rel(ext μ a d)) -> Rel(ext μ a d)) -> Rel(μ)|
\]
for the soundness relation of \Cref{thm:soundness-by-need}
\[
  R_|μ|(|d|, |hat d|) \triangleq |βD^(μ)^(d) ⊑ hat d|.
\]
However, parametricity only yields
\[
  |(bind, bind) ∈ (Rel(μ) -> Rel(μ)) -> (Rel(μ) -> Rel(μ)) -> Rel(μ)|
\]
We think that a modular proof is still conceivable by defining a custom proof
tactic that would be \emph{inspired} by parametricity, given a means for
annotating how the heap index changes in |bind|.

Although we do not formally acknowledge this, the soundness relation |Rel(μ)|
of \Cref{thm:soundness-by-need} is reminiscent of a \emph{Kripke logical
relation}~\citep{Ahmed:04}.
In this analogy, definable heaps correspond to the \emph{possible worlds} of
\citet{Kripke:63} with heap progression |(~>)| as the \emph{accessibility
relation}.
\Cref{thm:heap-progress-mono} states that the relation $R_|μ|$ is monotonic
\wrt |(~>)|, so we consider it possible to define a Kripke-style logical
relation over System $F$ types.

Kripke-style logical relations are well-understood in the literature, hence it
is conceivable that a modular proof technique just as for parametricity exists.
We have not investigated this avenue so far.
A modular proof would help our proof framework to scale up to a by-need
semantics of Haskell, for example, so this avenue bears great potential.
