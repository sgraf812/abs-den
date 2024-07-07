\subsection{Guarded Fixpoints, Safety Properties and Safety Extension of a Galois Connection}
\label{sec:safety-extension}

\Cref{fig:name-need-gist} describes a semantic trace property as a ``fold'', in
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
$α_{\mathcal{S}}$ in \Cref{fig:name-need-gist} defined by a fold over the
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
  |step e ({-" β_\Traces(\varid{τ'}) "-})| & \text{if |τ = Step e τ'|} \\
  |stuck|                         & \text{if |τ = Ret Stuck|} \\
  |fun (αD . powMap f . γD)| & \text{if |τ = Ret (Fun f)|} \\
  |con k (map (αD . set) ds)| & \text{if |τ = Ret (Con k ds)|} \\
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
Compared to the by-need trace abstraction in \Cref{fig:name-need-gist}, the
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
It is |βT (d >>= f) ⊑ hat f (hat d)| if
\begin{enumerate}
  \item |βT d ⊑ hat d|, and
  \item for all events |ev| and elements |hat d'|, |(hat step) ev ((hat f) (hat d')) ⊑ (hat f) ((hat step) ev (hat d'))|, and
  \item for all values |v|, |βT (f v) ⊑ (hat f) (βT (Ret v))|.
\end{enumerate}
\end{lemma}
\begin{proof}
By Löb induction.

If |d = Step ev d'|, define |hat d' := βT d'|.
We get
\begin{spec}
  βT (d >>= f) = βT (Step ev d' >>= f) = (hat step) ev (βT (d' >>= f))
⊑  {- Induction hypothesis at |βT d' = hat d'|, Monotonicity of |hat step| -}
  hat step ev ((hat f) (βT d'))
⊑  {- Assumption (2) -}
  (hat f) ((hat step) ev (βT d')) = (hat f) (βT d)
⊑  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}

Otherwise, |d = Ret v| for some |v :: Value|.
\begin{spec}
  βT (Ret v >>= f) = βT (f v)
⊑  {- Assumption (3) -}
  (hat f) (βT (Ret v)) = (hat f) (βT d)
⊑  {- Assumption (1) -}
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
Note that $R(|d|, |hat d|) \Longleftrightarrow |βT d ⊑ hat d|$ and it is more
direct to argue in terms of the latter.
\begin{itemize}
  \item \textbf{Case |step|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R}{(|step ev d|, |hat step ev (hat d)|) ∈ R}$. \\
    Then |βT (Step ev d) = hat step ev (βT d) ⊑ hat step ev (hat d)| by assumption and monotonicity.

  \item \textbf{Case |stuck|}.
    Goal: $(|stuck|, |hat stuck|) ∈ R$. \\
    Then |βT stuck = βT (Ret Stuck) = hat stuck|.

  \item \textbf{Case |fun|}.
    Goal: $\inferrule{\forall (|d|,|(hat d)|) ∈ R.\ (|f d|, |hat f (hat d)|) ∈ R}{(|fun f|, |hat fun (hat f)|) ∈ R}$. \\
    Then |βT (fun f) = βT (Ret (Fun f)) = (hat fun) (αD . powMap f . γD)| and
    it suffices to show that |αD . powMap f . γD ⊑ hat f| by monotonicity of |hat fun|.
    \begin{spec}
      (αD . powMap f . γD) (hat d)
    =  {- Unfold |powMap|, |αD|, simplify -}
      Lub (βT (f d) | d ∈ γD (hat d))
    ⊑  {- Apply premise to |βT d ⊑ hat d| -}
      hat f (hat d)
    \end{spec}

  \item \textbf{Case |apply|}.
    Goal: $\inferrule{(|d|,|(hat d)|) ∈ R \\ (|a|,|(hat a)|) ∈ R}{(|apply d a|, |hat apply (hat d) (hat a)|) ∈ R}$. \\
    |apply d a| is defined as |d >>= \v -> case v of Fun g -> g a; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-name-bind} at |hat f (hat d) := hat apply (hat d) (hat a)|.
    We get three subgoals for the premises of \Cref{thm:by-name-bind}:
    \begin{itemize}
      \item |βT d ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R$.
      \item |forall ev (hat d'). (hat step) ev ((hat apply) (hat d') (hat a)) ⊑ (hat apply) ((hat step) ev (hat d')) (hat a)|: By assumption \textsc{Step-App}.
      \item |forall v. βT (case v of Fun g -> g a; _ -> stuck) ⊑ hat apply (βT (Ret v)) (hat a)|: \\
        By cases over |v|.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT stuck = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Con k ds|}:
            Then |βT stuck = hat stuck ⊑ (hat apply) ((hat con) k (map (αD . set) ds)) (hat a)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Fun g|}:
            Then
            \begin{spec}
                βT (g a)
              ⊑  {- |id ⊑ γD . αD|, rearrange -}
                (αD . powMap g . γD) (αD a)
              ⊑  {- Assumption |βT a ⊑ hat a| -}
                (αD . powMap g . γD) (hat a)
              ⊑  {- Assumption \textsc{Beta-App} -}
                (hat apply) ((hat fun) (αD . powMap g . γD)) (hat a)
              =  {- Definition of |βT|, |v| -}
                (hat apply) (βT (Ret v)) (hat a)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case |con|}.
    Goal: $\inferrule{(|ds|,|(hat ds)|) ∈ |[{-"R"-}space]|}{(|con k ds|, |(hat con) k (hat ds)|) ∈ R}$. \\
    Then |βT (con k ds) = βT (Ret (Con k ds)) = (hat con) k (map (αD . set) ds)|.
    The assumption $(|ds|,|(hat ds)|) ∈ |[{-"R"-}space]|$ implies |map (αD . set) ds ⊑ hat ds| and
    the goal follows by monotonicity of |hat con|.

  \item \textbf{Case |select|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R \\ (|alts|,|hat alts|) ∈ |Tag :-> ([{-"R"-}space] -> {-"R"-}space)|}{(|select d alts|, |(hat select) (hat d) (hat alts)|) ∈ R}$. \\
    |select d fs| is defined as |d >>= \v -> case v of Con k ds || k ∈ dom alts  -> (alts ! k) ds; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-name-bind} at |hat f (hat d) := hat select (hat d) (hat alts)|.
    We get three subgoals for the premises of \Cref{thm:by-name-bind}:
    \begin{itemize}
      \item |βT d ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R$.
      \item |forall ev (hat d'). (hat step) ev ((hat select) (hat d') (hat alts)) ⊑ (hat select) ((hat step) ev (hat d')) (hat alts)|: By assumption \textsc{Step-Sel}.
      \item |forall v. βT (case v of Con k ds || k ∈ dom alts  -> (alts ! k) ds; _ -> stuck) ⊑ (hat select) (βT (Ret v)) (hat alts)|: \\
        By cases over |v|. The first three all correspond to when the continuation of |select| gets stuck.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT stuck = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT stuck = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT stuck = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Con k ds|, $|k| ∈ |dom alts|$}:
            Then
            \begin{spec}
                βT ((alts ! k) ds)
              ⊑  {- |id ⊑ γD . αD|, rearrange -}
                (αD . powMap (alts ! k) . map γD) (map (αD . set) ds)
              ⊑  {- Assumption $(|alts|,|hat alts|) ∈ |Tag :-> ([{-"R"-}space] -> {-"R"-}space)|$ -}
                (hat alts ! k) (map (αD . set) ds)
              ⊑  {- Assumption \textsc{Beta-Sel} -}
                (hat select) ((hat con) k (map (αD . set) ds)) (hat alts)
              =  {- Definition of |βT|, |v| -}
                (hat select) (βT (Ret v)) (hat alts)
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
      lfp (\(hat d) -> Lub (βT (rhs d) | d ∈ γD (hat d))
    ⊑  {- Apply assumption to $|αD ^ ((set d)) ⊑ αD (γD (hat d)) ⊑ hat d <==> | (|d|,|hat d|) ∈ R$ -}
      lfp (hat rhs)
    \end{spec}
    Applying this fact to the second assumption proves
    $(|body (fix rhs)|, |(hat body) (lfp (hat rhs))|) ∈ R$ and thus the goal.
\end{itemize}
\end{proof}

\subsection{Abstract By-need Soundness, in Detail}
\label{sec:by-need-soundness}

Now that we have gained some familiarity with utilising parametricity in while
proving \Cref{thm:soundness-by-name} correct, we will tackle the proof
for \Cref{thm:soundness-by-need}, which is applicable for analyses that
are sound both \wrt to by-name as well as by-need, such as usage analysis or
perhaps type analysis in \Cref{sec:type-analysis} (we have however not proven it
so).

A sound by-name analysis must only satisfy the two additional abstraction laws
\textsc{Step-Inc} and \textsc{Update} in \Cref{fig:abstraction-laws} to yield
sound results for by-need as well.
These laws make intuitive sense, because |Upd| events cannot be observed in a
by-name trace and hence must be ignored.
Other than |Upd| steps, by-need evaluation makes fewer steps than by-name
evaluation, so \textsc{Step-Inc} asserts that dropping steps never invalidates
the result.

The Galois connection in \Cref{fig:abstract-name-need} formalises the
corresponding semantic property.
It is more complicated than the Galois connection in \Cref{fig:abstract-name},
because it needs to account for heaps and memoisation.
Although in \Cref{sec:evaluation-strategies} we considered a |d :: DNeed|
as an atomic denotation, such a denotation actually only makes sense when it
travels together with an environment |ρ| that ties free variables to their addresses
in the heap that |d| expects.

Note that the abstraction function |αS| only considers \emph{definable} |ρ|
and |μ|, a notion that we will clarify now.
From now on, we will abbreviate the constraint tuple |(Trace d, Domain d,
HasBind d)| simply by |Dict d|.

\begin{definition}[Definable by-need environment, address domain]
The definable by-need environments are characterised by
|needenv ρ := forall x. {-" \exists\!\!\; "-} many ev {-"\varid{a}\ldotp"-} ρ!x = many (step ev) (fetch a)|
The \emph{address domain} of a definable |ρ| is |adom ρ := set (^^ a || ρ!x = many (step ev) (fetch a) ^^)|.
\end{definition}

Note that |many ev| is always non-empty because at least one |step| must
hide the |Later| in the result of |fetch a|.
We will mostly omit |Later| from the present pen-and-paper formalisation, but it
is important to keep in mind this particular use of the later modality in order
to apply Löb induction in the proofs that follow.

\begin{definition}[Polymorphic definition]
We write |polydef sss| to mean that |sss| can be defined at
polymorphic type |forall x. Dict x => (Name :-> x) -> x|.
\end{definition}

\begin{definition}[Definable by-need elements, address domain]
The definable by-need elements are characterised by
|needd d := exists sss ρ. (polydef sss) /\ (needenv ρ) /\ d = sss ρ|.
The \emph{address domain} of a definable |d| is |adom (sss ρ) := adom ρ|.
\end{definition}

\begin{definition}[Definable by-need heaps]
The definable by-need heaps are characterised by
|needheap μ := forall a. exists d. needd d /\ μ!a = memo a d|.
\end{definition}

Note that a definable |d| cannot be obtained by instantiating a polymorphic
|d' :: (Trace d, Domain d, HasBind d) => d|, because the |fetch a| operations
isolated in definable |ρ| are not part of the type class algebra.
Still, the factoring of definable |d| in terms of a polymorphic |sss| yields
enough leverage to apply parametricity.

%It is easy to see that definability is preserved by any such |sss|, for example |eval e|:
%
%\begin{lemma}
%If |polydef sss| and |needenv ρ|, then |needd (sss ρ)|
%\end{lemma}

\begin{lemma}[Parametric induction principle]
\label{thm:param-ind-1}
If |polydef sss| and |needenv ρ|, some property $P ⊆ |DNeed|$
\[
  \inferrule
    {(\forall |a|.\ \later (|fetch a| ∈ P)) \\ \mathit{inst} ∈ \mathsf{Dict}(P)}
    {|sss ρ| ∈ P}
\]
\end{lemma}
\begin{proof}
By |polydef sss|, we get the free theorem
\[
  (|sss|,|sss|) ∈ \forall \mathcal{X}.\ \mathsf{Dict}(\mathcal{X}) → (|Name| \pfun \mathcal{X}) → \mathcal{X}.
\]
We instantiate it at $R(d_1,d_2) \triangleq d_1 = d_2 \land d_1 ∈ P$, the
instance dictionary $\mathit{inst} ∈ \mathsf{Dict}(|DNeed|)$ and |ρ| to derive the
following assertion:
\[
  \inferrule
    {(\mathit{inst},\mathit{inst}) ∈ \mathsf{Dict}(R) \\ (|ρ|,|ρ|) ∈ (|Name| \pfun R)}
    {(|sss ρ|,|sss ρ|) ∈ R}
\]
Note that $(|d|, |d|) ∈ R$ is equivalent to $|d| ∈ P$, so it suffices to
show the two premises of the rule, which become our subgoals.

The first subgoal $(\mathit{inst},\mathit{inst}) ∈ \mathsf{Dict}(R)$ follows
by $\mathit{inst} ∈ \mathsf{Dict}(P)$.

For the second subgoal $(|ρ|,|ρ|) ∈ (|Name| \pfun R)$, it suffices to show
\begin{equation}
  \forall |many ev|, |a|.\ (|many (step ev) (fetch a)|,|many (step ev) (fetch a)|) ∈ R. \label{eqn:step-induction}
\end{equation}
The property for |step :: Later DNeed -> DNeed| (making
explicit that the |Later| that the implementation of |step| embeds) implied by
$\mathit{inst} ∈ \mathsf{Dict}(P)$ is as follows
\[
  \forall |ev|,|d1|,|d2|.\ \later ((|d1|,|d2|) ∈ R) \implies (|step ev d1|, |step ev d2|) ∈ R.
\]
We instantiate with the assumption
$\forall |a|.\ \later ((|fetch a|, |fetch a|) ∈ R)$
to show the goal \Cref{eqn:step-induction}.
\end{proof}

From now on, we assume that all concrete environments |Name :-> DNeed|
and heaps |HeapNeed| are definable.
It is easy to see that definability is preserved by |evalNeed|; the only
interesting case concerns the implementation of |HasBind|.

Just as for by-name, we will rely on parametricity to achieve a modular proof.
However, the definable |ρ| and |μ| do not enjoy parametric definitions at
|forall d. (Trace d, Domain d, HasBind d) => Name :-> d| and
|forall d. (Trace d, Domain d, HasBind d) => Addr :-> d|!
Neither |fetch a| nor |memo a| are expressible in the type class algebra.
We can still exploit parametricity at the type of |eval e|, as we shall see,
but first we need a better grasp on heaps.

Intuitively, if |μ2| is ``more evaluated than'' |μ1|,
the fewer steps |d ^(μ2)| does relative to |d ^(μ1)|,
and hence |βT ^ (d ^(μ2)) ⊑ βT ^ (d ^(μ1))| as well.
The notion of ``more evaluated than'' is formally defined by the
\emph{heap progression} relation in \Cref{fig:heap-progression},
and we will now work towards a proof for the approximation statement about |βT|
in \Cref{thm:heap-progress-persist}.

To that end, let us define the following abbreviation:
\begin{abbreviation}[Big-step]
  We write $\bigstep{μ_1}{d}{μ_2}{v}$ to mean that there exists |many ev| such that
  |d μ1 = many (Step ev) (Ret (v, μ2))|.
\end{abbreviation}

\begin{figure}
  \[\begin{array}{c}
    \ruleform{ μ_1 \progressto μ_2 }
    \\ \\[-0.5em]
    \inferrule[\progresstorefl]
      {}
      {|μ ~> μ|}
    \qquad
    \inferrule[\progresstotrans]
      {|μ1 ~> μ2| \\ |μ2 ~> μ3|}
      {|μ1 ~> μ3|}
    \qquad
    \inferrule[\progresstoext]
      {|a| \not∈ |dom μ| \\ |adom ρ ⊆ dom μ ∪ set a|}
      {|μ ~> ext μ a (memo a (sss ρ))|}
    \\ \\[-0.5em]
    \inferrule[\progresstomemo]
      {|μ1 ! a = memo a (sss ρ1)| \\ |Later (bigstep μ1 (sss ρ1) μ2 v)|}
      {|μ1 ~> ext μ2 a (memo a (return v))|}
    \\[-0.5em]
  \end{array}\]
  \caption{Heap progression relation. The meta-variable |sss| scopes over
  definitions of the type
  |forall d. (Trace d, Domain d, HasBind d) => (Name :-> d) -> d|, and all
  occurrences of |ρ| and |μ| refer to definable entities.}
  \label{fig:heap-progression}
\end{figure}

Transitivity and reflexivity of $(\progressto)$ are definitional by rules
\progresstorefl and \progresstotrans; antisymmetry is not so simple to show for
a lack of full abstraction.

\begin{corollary}
  $(\progressto)$ is a preorder.
\end{corollary}

% Can't prove the following lemma:
%\begin{lemma}
%If |μ1 ~> μ2| by \progresstomemo,
%then also |ext μ2 a (μ1 ! a) ~> μ2| for the updated |a ∈ dom μ1|.
%\end{lemma}
%\begin{proof}
%By rule inversion, we have |μ1 ! a = memo a (eval e ρ1)|
%and |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 (ext μ2 a (memo a (eval e ρ1)))|
%for some |e|, |ρ1|, |v|, |ρ2|.
%Then
%|eval x (singenv x (step (Look x) (fetch a))) μ1 = step (Look x) (many (step ev) (step Upd (eval v ρ2 μ2)))|,
%hence by \Cref{thm:eval-progression} |μ1 ~> μ2|.
%\end{proof}

The remaining two rules express how a heap can be modified during by-need
evaluation:
Evaluation of a |Let| extends the heap via \progresstoext and evaluation
of a |Var| will memoise the evaluated heap entry, progressing it along
\progresstomemo.

URGH LATER. Say that instead of |eval e| and by induction, we do the type of |eval e| and by parametricity.

In a first iteration, we have expressed all the properties that follow in
terms of the concrete definition |eval e|
In the following proofs, we will appeal to parametricity .

The properties and proofs in the following could be conducted  |eval e| by induction on |e|,
we will try to instead

In the following, the type of |sss| is always the same polymorphic type
|forall d. (Trace d, Domain d, HasBind d) => (Name :-> d) -> d|
which we encode in System $F$ as
$\forall X. \mathsf{Dict}(X) \to (\mathsf{Name} \pfun X) \to X$.

\begin{lemma}[Evaluation progresses the heap]
\label{thm:eval-progression}
If |bigstep μ1 (sss ρ1) μ2 v|, then |μ1 ~> μ2|.
\end{lemma}
\begin{proof}
By Löb induction and the parametric induction principle \Cref{thm:param-ind-1}, applied to the property
\[
  P(d) \triangleq \forall μ_1,μ_2,v\ldotp \bigstep{μ_1}{d}{μ_2}{v} \implies μ_1 \progressto μ_2.
\]
The two subgoals are
\[
  (\forall |a|.\ \later (|fetch a| ∈ P)) \qquad \mathit{inst} ∈ \mathsf{Dict}(P)
\]
\begin{itemize}
  \item \textbf{Case }$\forall |a|.\ \later (|fetch a| ∈ P)$:
    Everything under |Later|:
    \begin{spec}
        fetch a μ1
    =   {- Unfold |fetch| -}
        (μ1 ! a) μ1
    =   {- |μ| definable, some |sss'|, |ρ3| -}
        memo a (sss' ρ3 μ1)
    =   {- Unfold |memo| -}
        sss' ρ3 μ1 >>= upd
    =   {- |bigstep μ1 (sss' ρ3) μ3 v| for some |μ3|, |many ev1|, unfold |>>=|, |upd| -}
        many (Step ev1) (Step Upd (Ret (v, ext μ3 a (memo a (return v)))))
    \end{spec}
    So |Later (bigstep μ1 (fetch a) (ext μ3 a (memo a (return v))) v)|,
    and by determinism |μ2 = (ext μ3 a (memo a (return v)))|.
    In summary, we have
    \begin{align}
      & |μ1 ! a = memo a (sss' ρ3)| \label{eqn:eval-progression-memo} \\
      & |Later (bigstep μ1 (sss' ρ3) μ3 v)| \label{eqn:eval-progression-eval} \\
      & |μ2 = ext μ3 a (memo a (return v))| \label{eqn:eval-progression-heaps}
    \end{align}
    We can apply rule \progresstomemo to \Cref{eqn:eval-progression-memo} and \Cref{eqn:eval-progression-eval}
    to get |μ1 ~> ext μ3 a (memo a (return v))|, and rewriting along
    \Cref{eqn:eval-progression-heaps} proves the goal.
  \item \textbf{Case } |step|,|stuck|,|fun|,|apply|,|con|,|select|:
    These cases do not modify the heap and consequently follow by applying
    assumptions, reflexivity and transitivity.
  \item \textbf{Case } |bind|. Goal: $\inferrule{(\forall |d| ∈ P.\ |rhs d| ∈ P) \\ (\forall |d| ∈ P.\ |body d| ∈ P)}
                                                {|bind rhs body| ∈ P}$: \\
    \begin{spec}
      bind rhs body μ1
    =   {- Unfold |bind|, |a := nextFree μ1| with $|a| \not\in |dom μ1|$ -}
      body (fetch a) (ext μ1 a (memo a (rhs (fetch a))))
    \end{spec}
    We have already shown $\later (|fetch a|∈P)$.
    Hence $|rhs (fetch a)|∈P$ as well as $|body (fetch a)|∈P$
    by assumption.

    Note that |μ1 ~> ext μ1 a (memo a (rhs (fetch a)))| by \progresstoext.
    On the other hand, $|body (fetch a)|∈P$ and thus
    |ext μ1 a (memo a (rhs (fetch a))) ~> μ2|, so the goal follows by
    \progresstotrans.
\end{itemize}
\end{proof}

\Cref{thm:eval-progression} exposes nested structure in \progresstomemo.
For example, if |μ1 ~> ext μ2 a (memo a (evalNeed2 v ρ2))| is the result of applying
rule \progresstomemo, then we obtain a proof that the memoised expression
|evalNeed2 e ρ1 μ1| evaluates to |evalNeed2 v ρ2 μ2|, and this
evaluation in turn implies that |μ1 ~> μ2|.

Heap progression is useful to state a number of semantic properties, for example
the ``update once'' property of memoisation and that a heap binding is
semantically irrelevant when it is never updated:

\begin{lemma}[Update once]
\label{thm:update-once}
If   |μ1 ~> μ2| and |μ1 ! a = memo a (return v)|,
then |μ2 ! a = memo a (return v)|.
\end{lemma}
\begin{proof}
Simple proof by induction on |μ1 ~> μ2|.
The only case updating a heap entry is \progresstomemo, and there we can see
that |μ2 ! a = memo (return v)| because evaluating |v| in |μ1| does not make
a step.
\end{proof}

\begin{lemma}[No update implies semantic irrelevance]
\label{thm:no-update-irrelevance}
If |bigstep μ1 (sss ρ) μ2 v|
and |μ1 ! a = μ2 ! a = memo a (step ev d1)|,
then |forall d2. bigstep (ext μ1 a d2) (sss ρ) (ext μ2 a d2) (return v)|.
\end{lemma}
\begin{proof}
By Löb induction and the parametric induction principle \Cref{thm:param-ind-1}, applied to the property
\begin{spec}
  {-" P(d) "-} := forall μ1 μ2 v d1.  bigstep μ1 d μ2 v /\ μ1 ! a = μ2 ! a = memo a (step ev d1) ==>
                                      forall d2. bigstep (ext μ1 a d2) d (ext μ2 a d2) v
\end{spec}
\begin{itemize}
  \item \textbf{Case }$\forall |a1|.\ \later (|fetch a1| ∈ P)$:
     Everything under |Later|.
     We may assume |bigstep μ1 (fetch a1) μ2 v|, |μ1 ! a = μ2 ! a = memo a (step ev d1)|.

     It is |fetch a1 μ1 = (μ1 ! a1) μ1 = memo a1 d3 μ1| by |needheap μ1| for the suitable |d3|,
     with |bigstep μ1 d3 μ2 v| (later!).
     Since |memo a1| updates |μ2 ! a1 = memo a1 (return v)| and
     $|return v| \not= |step ev d1|$ it must be $|a1| \not= |a|$.

     We may apply the Löb induction hypothesis to |bigstep μ1 d3 μ2 v| to get \\
     |forall d2. bigstep (ext μ1 a d2) d3 (ext μ2 a d2) v|. \\
     Since $|a1| \not= |a|$, we must also have
     |forall d2. bigstep (ext μ1 a d2) (fetch a) (ext μ2 a d2) v|, as required.

  \item \textbf{Case } |step|,|stuck|,|fun|,|apply|,|con|,|select|:
    These cases do not modify the heap and consequently follow by applying
    assumptions.

  \item \textbf{Case } |bind|. Goal: $\inferrule{(\forall |d| ∈ P.\ |rhs d| ∈ P) \\ (\forall |d| ∈ P.\ |body d| ∈ P)}
                                                {|bind rhs body| ∈ P}$: \\
    \begin{spec}
      bind rhs body μ1
    =   {- Unfold |bind|, |a1 := nextFree μ1| with $|a1| \not\in |dom μ1|$ -}
      body (fetch a1) (ext μ1 a1 (memo a1 (rhs (fetch a1))))
    \end{spec}
    We have $\later (|fetch a1| ∈ P)$ by a previous case, so we can get
    $|body (fetch a1)| ∈ P$ by assumption.
    We also have $|a| \not= |a1|$ by a property of |nextFree|, so $|body (fetch a1)| ∈ P$
    yields |forall d2. bigstep (ext (ext μ1 a1 (memo a1 (rhs (fetch a1)))) a d2) (body (fetch a1)) (ext μ2 a d2) v|,
    which is the same as the goal |forall d2. bigstep (ext μ1 a d2) (bind rhs body) (ext μ2 a d2) v|
    after refolding |bind|.
\end{itemize}
\end{proof}

Now we move on to proving auxiliary lemmas about |persistHeap|.

A by-name analysis that is sound \wrt by-need must improve when an expression
reduces to a value, which in particular will happen after the heap update during
memoisation.

The following pair of lemmas corresponds to the $\UpdateT$ step of the
preservation \Cref{thm:preserve-absent} where we (and \citet{Sergey:14})
resorted to hand-waving.
Its proof is suprisingly tricky, but it will pay off; in a moment, we will
hand-wave no more!

\begin{lemma}[Preservation of heap update]
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the abstraction laws
  \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName} and
  \textsc{Step-Inc} from \Cref{fig:abstraction-laws}.
  Let |d| be a definable element and
  \begin{enumerate}[label=(\alph*),ref=\thelemma.(\alph*)]
    \item
      If   |bigstep μ1 (sss ρ1) μ2 v|
      and  |μ1 ! a = memo a (sss ρ1)|,\\
      then |eval v (βE (ext μ2 a (memo a (return v))) << ρ2) ⊑ eval e (βE μ2 << ρ1)|.
      \label{thm:memo-improves}
    \item
      If   |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|
      and  |μ2 ~> μ3|,
      then |eval v (βE μ3 << ρ2) ⊑ eval e (βE μ3 << ρ1)|.
      \label{thm:value-improves}
  \end{enumerate}
\end{lemma}
\begin{proof}
By Löb induction, we assume that both properties hold \emph{later}.
\begin{itemize}
  \item \labelcref{thm:memo-improves}:
    We assume that |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|
    and |μ1 ! a = memo a (evalNeed2 e ρ1)|
    to show |eval v (βE (ext μ2 a (memo a (evalNeed2 v ρ2))) << ρ2) ⊑ eval e (βE μ2 << ρ1)|.

    We can use the IH \labelcref{thm:memo-improves} to prove that
    |βE (ext μ2 a (memo a (evalNeed2 v ρ2))) d ⊑ βE μ2 d|
    for all |d| such that |adom d ⊆ adom μ2|.
    This is simple to see unless |d = Step (Look y) (fetch a)|, in
    which case we have:
    \begin{spec}
        βE (ext μ2 a (memo a (evalNeed2 v ρ2))) (Step (Look y) (fetch a))
    = {- Unfold |βE| -}
        step (Look y) (eval v (βE (ext μ2 a (memo a (evalNeed2 v ρ2))) << ρ2))
    ⊑ {- IH \labelcref{thm:memo-improves} -}
        step (Look y) (eval e (βE μ2 << ρ1))
    = {- Refold |βE| -}
        βE μ2 (step (Look y) (fetch a))
    \end{spec}

    This is enough to show the goal:
    \begin{spec}
        eval v (βE (ext μ2 a (memo a (evalNeed2 v ρ2))) << ρ2)
    ⊑   {- |βE (ext μ2 a (memo a (evalNeed2 v ρ2))) ⊑ βE μ2| -}
        eval v (βE μ2 << ρ2)
    ⊑   {- IH \labelcref{thm:value-improves} applied to |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)| -}
        eval e (βE μ2 << ρ1)
    \end{spec}

  \item \labelcref{thm:value-improves}
    |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2) && μ2 ~> μ3 ==> eval v (βE μ3 << ρ2) ⊑ eval e (βE μ3 << ρ1)|:

    By Löb induction and cases on |e|.
    \begin{itemize}
      \item \textbf{Case} |Var x|:
        Let |a| be the address such that |ρ1 ! x = Step (Look y) (fetch a)|.
        Note that |μ1 ! a = memo a _|, so the result has been memoised in
        |μ2|, and by \Cref{thm:update-once} in |μ3| as well.
        Hence the entry in |μ3| must be of the form |μ3 ! a = memo a (evalNeed2 v ρ2)|.
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step (Look y) (eval v (βE μ3 << ρ2))
        =   {- Refold |βE| for the appropriate |y| -}
            (βE μ3 << ρ1) ! x
        =   {- Refold |eval| -}
            eval x (βE μ3 << ρ1)
        \end{spec}
      \item \textbf{Case} |Lam x body|, |ConApp k xs|: Follows by reflexivity.
      \item \textbf{Case} |App e x|:
        Then |evalNeed e ρ1 μ1 = many (Step ev1) (evalNeed (Lam y body) ρ3 μ4)|\\
        and |evalNeed body (ext ρ3 y (ρ1 ! x)) μ4 = many (Step ev2) (evalNeed v ρ2 μ2)|.
        Note that |μ4 ~> μ2| by \Cref{thm:eval-progression}, hence |μ4 ~> μ3|
        by \progresstotrans.
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- IH \labelcref{thm:value-improves} at |body| and |μ2 ~> μ3| -}
            eval body (βE μ3 << ext ρ3 y (ρ1 ! x))
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step App2 (eval body (βE μ3 << ext ρ3 y (ρ1 ! x)))
        ⊑   {- Assumption \textsc{Beta-App}, refold |Lam| case -}
            apply (eval (Lam y body) (βE μ3 << ρ3)) (βE μ3 (ρ1 ! x))
        ⊑   {- IH \labelcref{thm:value-improves} at |e| and |μ4 ~> μ3| -}
            apply (eval e (βE μ3 << ρ1)) (βE μ3 (ρ1 ! x))
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step App1 (apply (eval e (βE μ3 << ρ1)) (βE μ3 (ρ1 ! x)))
        =   {- Refold |eval (App e x) (βE μ3 << ρ1)| -}
            eval (App e x) (βE μ3 << ρ1)
        \end{spec}
      \item \textbf{Case} |Case e alts|: Similar to |App|.
      \item \textbf{Case} |Let x e1 e2|:
        Then |evalNeed (Let x e1 e2) ρ1 μ1 = Step Let1 (evalNeed e2 ρ4 μ4)|, where
        |a := nextFree μ1|, |ρ4 := ext ρ1 x (Step (Look x) (fetch a))|,
        |μ4 := ext μ1 a (memo a (evalNeed2 e1 ρ4))|.
        Observe that |μ4 ~> μ2 ~> μ3|.

        The first first half of the proof is simple enough:
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- IH \labelcref{thm:value-improves} at |e2| and |μ2~>μ3| -}
            eval e2 (βE μ3 << ρ4)
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step Let1 (eval e2 (βE μ3 << ρ4))
        =   {- Unfold |ρ4| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (βE μ3 (ρ4 ! x))))
        \end{spec}

        We proceed by case analysis on whether |μ4 ! a = μ3 ! a|.

        If that is the case, we get
        \begin{spec}
        =   {- Unfold |βE μ3 (ρ4 ! x)|, |μ3 ! a = μ4 ! a| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE μ3 << ρ1) x (hat d1)))))))
        ⊑   {- Assumption \textsc{Bind-ByName} -}
            bind  (\(hat d1) -> eval e1 (ext ((βE μ3 << ρ1)) x (step (Look x) (hat d1))))
                  (\(hat d1) -> step Let1 (eval e2 (ext ((βE μ3 << ρ1)) x (step (Look x) (hat d1)))))
        =   {- Refold |eval| -}
            eval (Let x e1 e2) (βE μ3 << ρ1)
        \end{spec}

        Otherwise, we have |μ3 ! a //= μ4 ! a|, implying that |μ4 ~> μ3|
        contains an application of \progresstomemo updating |μ3 ! a|.

        By rule inversion, |μ3 ! a| is the result of updating it to the form
        |memo a (evalNeed2 v1 ρ3)|, where |evalNeed e1 ρ4 μ4' = many (Step ev1) (evalNeed v1 ρ3 μ3')|
        such that |μ4 ~> μ4' ~> (ext μ3' a (memo a (evalNeed2 v1 ρ3))) ~> μ3| and
        |μ4 ! a = μ4' ! a = μ3' ! a //= μ3 ! a|.
        (NB: if there are multiple such occurrences of \progresstomemo in
        |μ4 ~> μ3|, this must be the first one, because afterwards it is
        $|μ4 ! a //= μ4' ! a|$.)

        It is not useful to apply the IH \labelcref{thm:memo-improves} to this
        situation directly, because |μ3' ~> μ3| does not hold.
        However, note that \progresstomemo contains proof that evaluation of
        |evalNeed e1 ρ4 μ4'| succeeded, and it must have done so without
        looking at |μ4' ! a| (because that would have led to an infinite loop).
        Furthermore, |e1| cannot be a value; otherwise, |μ4 ! a = μ3 ! a|, a contradiction.
        Since |e1| is not a value and |μ4' ! a = μ3' ! a|, we can apply
        \Cref{thm:no-update-irrelevance} to get the useful reduction
        \begin{align*}
            & |evalNeed e1 ρ4 (ext μ4' a (memo a (evalNeed2 v1 ρ3)))| \\
          = & |many (Step ev1) (evalNeed v1 ρ3 (ext μ3' a (memo a (evalNeed2 v1 ρ3))))|.
        \end{align*}
        This reduction is so useful because we know something about
        |ext μ3' a (memo a (evalNeed2 v1 ρ3))|;
        namely that |ext μ3' a (memo a (evalNeed2 v1 ρ3)) ~> μ3|.
        This allows us to apply the induction hypothesis
        \labelcref{thm:memo-improves} to the reduction, which yields
        \[
          |eval v1 (βE μ3 << ρ3) ⊑ eval e1 (βE μ3 << ρ4)|
        \]
        We this identity below:
        \begin{spec}
        =   {- Unfold |βE μ3 (ρ4 ! x)|, |μ3 ! a = memo a (evalNeed2 v1 ρ3)| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval v1 (ext (βE μ3 << ρ3) x (hat d1)))))))
        ⊑   {- |eval v1 (βE μ3 << ρ3) ⊑ eval e1 (βE μ3 << ρ4)|, unfold |βE μ3 (ρ4 ! x)| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE μ3 << ρ1) x (hat d1)))))))
        ⊑   {- ... as above ... -}
            eval (Let x e1 e2) (βE μ3 << ρ1)
        \end{spec}
    \end{itemize}
\end{itemize}
\end{proof}

With that, we can finally prove that heap progression preserves environment
abstraction:

\begin{lemma}[Heap progression preserves abstraction]
  \label{thm:heap-progress-persist}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the abstraction laws
  \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName} and
  \textsc{Step-Inc} in \Cref{fig:abstraction-laws}.
  Furthermore, let |αE μ :<->: γE μ = persistHeap μ| for all |μ|.

  If |μ1 ~> μ2| and |adom d ⊆ dom μ1|, then |αE μ2 d ⊑ αE μ1 d|.
\end{lemma}
\begin{proof}
By Löb induction.
Let us assume that |μ1 ~> μ2| and |adom d ⊆ dom μ1|.
Since |needd d|, we have |d = Cup (Step (Look y) (fetch a))|.
Similar to \Cref{thm:soundness-by-name}, it suffices to show the goal for a
single |d = Step (Look y) (fetch a)| for some |y|, |a| and the representation
function |βE μ := αE μ << set|.

Furthermore, let us abbreviate |memo a (evalNeed2 ei ρi) := μi ! a|.
The goal is to show
\[
  |step (Look y) (eval e2 (βE μ2 << ρ2)) ⊑ step (Look y) (eval e1 (βE μ1 << ρ1))|,
\]
Monotonicity allows us to drop the |step (Look x)| context
\[
  |Later (eval e2 (βE μ2 << ρ2) ⊑ eval e1 (βE μ1 << ρ1))|.
\]
Now we proceed by induction on |μ1 ~> μ2|, which we only use to prove correct the
reflexive and transitive closure in \progresstorefl and \progresstotrans.
By contrast, the \progresstomemo and \progresstoext cases make use of the Löb
induction hypothesis, which is freely applicable under the ambient |Later|.
\begin{itemize}
  \item \textbf{Case} \progresstorefl:
    Then |μ1 = μ2| and hence |αE μ1 = αE μ2|.
  \item \textbf{Case} \progresstotrans:
    Apply the induction hypothesis to the sub-derivations and apply transitivity
    of |⊑|.
  \item \textbf{Case} $\inferrule*[vcenter,left=\progresstoext]{|a1| \not∈ |dom μ1| \quad |adom ρ ⊆ dom μ1 ∪ set a1|}{|μ ~> ext μ1 a1 (memo a1 (evalNeed2 e ρ))|}$:\\
    We get to refine |μ2 = ext μ1 a1 (memo a1 (evalNeed2 e ρ))|.
    Since |a ∈ dom μ1|,
    we have $|a1| \not= |a|$
    and thus |μ1 ! a = μ2 ! a|, thus |e1=e2|, |ρ1=ρ2|.
    The goal can be simplified to
    |Later (eval e1 (βE μ2 << ρ1) ⊑ eval e1 (βE μ1 << ρ1))|.
    We can apply the induction hypothesis to get
    |Later (βE μ2 ⊑ βE μ1)|, and the goal follows by monotonicity.
  \item \textbf{Case} $\inferrule*[vcenter,left=\progresstomemo]{|μ1 ! a1 = memo a1 (evalNeed2 e ρ3)| \quad |Later (evalNeed e ρ3 μ1 = many (Step ev) (evalNeed v ρ2 μ3))|}{|μ1 ~> ext μ3 a1 (memo a1 (evalNeed2 v ρ2))|}$:\\
    We get to refine |μ2 = ext μ3 a1 (memo a1 (evalNeed2 v ρ2))|.
    When $|a1| \not= |a|$, we have |μ1 ! a = μ2 ! a| and the goal follows as in the \progresstoext case.
    Otherwise, |a = a1|, |e1 = e|, |ρ3 = ρ1|, |e2 = v|.

    We can use Lemma \labelcref{thm:memo-improves} to prove that
    |βE μ2 d ⊑ βE μ3 d| for all |d| such that |adom d ⊆ adom μ2|.
    This is simple to see unless |d = Step (Look y) (fetch a)|, in
    which case we have:
    \begin{spec}
        βE μ2 (Step (Look y) (fetch a))
    = {- Unfold |βE| -}
        step (Look y) (eval v (βE μ2 << ρ2))
    ⊑ {- Lemma \labelcref{thm:memo-improves} -}
        step (Look y) (eval e (βE μ3 << ρ1))
    = {- Refold |βE| -}
        βE μ3 (step (Look y) (fetch a))
    \end{spec}

    We can finally show the goal |βE μ2 d ⊑ βE μ1 d| for all |d| such that
    |adom d ⊆ dom μ1|:
    \begin{spec}
        βE μ2 d
    ⊑   {- |βE μ2 ⊑ βE μ3| -}
        βE μ3 d
    ⊑   {- Löb induction hypothesis at |μ1 ~> μ3| by \Cref{thm:eval-progression} -}
        βE μ1 d
    \end{spec}
    % Actually the Löb induction hypothesis only applies under a Later,
    % but it is easy to show |βE μ3 d ⊑ βE μ1 d| now when it holds Later,
    % by unfolding
\end{itemize}
\end{proof}

\begin{lemma}[By-need evaluation preserves by-name trace abstraction]
  \label{thm:eval-preserves-need}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the abstraction laws \textsc{Step-App},
  \textsc{Step-Sel}, \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName},
  \textsc{Step-Inc} and \textsc{Update}
  in \Cref{fig:abstraction-laws}.
  Furthermore, let |αE μ :<->: γE μ = persistHeap μ| for all |μ|.

  If   |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|,
  then |many (step ev) (eval v (αE μ2 << set << ρ2)) ⊑ eval e (αE μ1 << set << ρ1)|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    \begin{spec}
      evalNeed x ρ1 μ1 = Step (Look y) (memo a (evalNeed e1 ρ3 μ1)) = many (Step ev) (evalNeed v ρ2 μ2)
    \end{spec}
    for some |y|, |a|, |e1|, |ρ3|,
    such that |ρ1 = step (Look y) (fetch a)|, |μ1 ! a = memo a (evalNeed2 e1 ρ3)| and
    |many ev = [Look y] ++ many ev1 ++ [Upd]| for some |ev1| by determinism.

    The step below that uses \Cref{thm:value-improves} does so at |e1| and
    |μ2 ~> μ2| to get |eval v (βE μ2 << ρ2) ⊑ eval e1 (βE μ2 << ρ3)|,
    in order to prove that
    |(βE μ2 << ρ2) ⊑ (βE (ext μ2 a (memo a (evalNeed2 e1 ρ3))) << ρ2)|.
    \begin{spec}
        many (step ev) (eval v (βE μ2 << ρ2))
    =   {- |many ev = [Look y] ++ many ev1 ++ [Upd]| -}
        step (Look y) (many (step ev1) (step Upd (eval v (βE μ2 << ρ2))))
    =   {- Assumption \textsc{Update} -}
        step (Look y) (many (step ev1) (eval v (βE μ2 << ρ2)))
    ⊑   {- \Cref{thm:value-improves} at |e1| implies |(βE μ2 << ρ2) ⊑ (βE (ext μ2 a (memo a (evalNeed2 e1 ρ3))) << ρ2)|  -}
        step (Look y) (many (step ev1) (eval v (βE (ext μ2 a (memo a (evalNeed2 e1 ρ3))) << ρ2)))
    ⊑   {- \Cref{thm:eval-preserves-need} -}
        step (Look y) (eval e1 (βE μ1 << ρ3))
    =   {- Refold |βE|, |ρ3 ! x| -}
        βE (ρ1 ! x)
    =   {- Refold |eval x (βE μ1 << ρ1)| -}
        eval x (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    We can make one step to see
    \begin{spec}
      evalNeed (Let x e1 e2) ρ1 μ1 = Step Let1 (evalNeed e2 ρ3 μ3) = Step Let1 (many (Step ev1) (evalNeed v ρ2 μ2)),
    \end{spec}
    where |ρ3 := ext ρ1 x (step (Look x) (fetch a))|,
    |a := nextFree μ1|,
    |μ3 := ext μ1 a (memo a (evalNeed2 e1 ρ3))|.

    Then |(βE μ3 << ρ3) ! y ⊑ (βE μ1 << ρ1) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:heap-progress-persist},
    and |(βE μ3 << ρ3) ! x = step (Look x) (eval e1 (βE μ3 << ρ3))|.

    We prove the goal, thus
    \begin{spec}
        many (step ev) (eval v (βE μ2 << ρ2))
    =   {- |many ev = Let1 : many ev1| -}
        step Let1 (many (step ev1) (eval v (βE μ2 << ρ2)))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Let1 (eval e2 (βE μ3 << ρ3))
    =   {- Rearrange |βE μ3| by above reasoning -}
        step Let1 (eval e2 (ext (βE μ1 << ρ1) x (βE μ3 (ρ3 ! x))) μ3)
    ⊑   {- Expose fixpoint, approximating |βE μ3 << ρ3| by |ext (βE μ1 << ρ1) x (βE μ3 (ρ3 ! x))| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE μ1 << ρ1) x (hat d1)))))))
    =   {- Partially unroll |lfp| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ1) x (step (Look x) (lfp (\(hat d1) -> eval e1 (ext (βE μ1 << ρ1) x (step (Look x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName} -}
        bind  (\(hat d1) -> eval e1 (ext ((βE μ1 << ρ1)) x (step (Look x) (hat d1))))
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE μ1 << ρ1)) x (step (Look x) (hat d1)))))
    =   {- Refold |eval (Let x e1 e2) (βE μ1 << ρ1)| -}
        eval (Let x e1 e2) (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Lam|, |ConApp|: By reflexivity.

  \item \textbf{Case} |App e x|:
    Very similar to \Cref{thm:eval-preserves}, since the heap is never updated or
    extended.
    There is one exception: We must apply \Cref{thm:heap-progress-persist}
    to argument denotations.

    We have |evalNeed e ρ1 μ1 = many (Step ev1) (evalNeed (Lam y body) ρ3 μ3)|
    and |evalNeed body (ext ρ3 y (ρ1 ! x)) μ3 = many (Step ev2) (evalNeed v ρ2 μ2)|.
    We have |μ1 ~> μ3| by \Cref{thm:eval-progression}.
    \begin{spec}
        step App1 (many (Step ev1) (step App2 (many (Step ev2) (eval v (βE μ2 << ρ2)))))
    =   {- Induction hypothesis at |many ev2| -}
        step App1 (many (step ev1) (step App2 (eval body (βE μ3 << (ext ρ3 y (ρ1 ! x))))))
    ⊑   {- Assumption \textsc{Beta-App}, refold |Lam| case -}
        step App1 (many (step ev1) (apply (eval (Lam y body) (βE μ3 << ρ3)) ((βE μ3 << ρ1) ! x)))
    ⊑   {- Assumption \textsc{Step-App} -}
        step App1 (apply (many (step ev1) (eval (Lam y body) (βE μ3 << ρ3))) ((βE μ3 << ρ1) ! x))
    ⊑   {- Induction hypothesis at |many ev1| -}
        step App1 (apply (eval e (βE μ1 << ρ1)) ((βE μ3 << ρ1) ! x))
    ⊑   {- \Cref{thm:heap-progress-persist} -}
        step App1 (apply (eval e (βE μ1 << ρ1)) ((βE μ1 << ρ1) ! x))
    =   {- Refold |eval| -}
        eval (App e x) (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The same as in \Cref{thm:eval-preserves}.

    We have |evalNeed e ρ1 μ1 = many (Step ev1) (evalNeed (ConApp k ys) ρ3 μ3)|,
    |evalNeed er (exts ρ1 xs (map (ρ3 !) ys)) μ3 = many (Step ev2) (evalNeed v ρ2 μ2)|,
    where |alts ! k = (xs,er)| is the matching RHS.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2) µ2)
    ⊑   {- |many ev = [Case1] ++ many ev1 ++ [Case2] ++ ev2|, IH at |ev2| -}
        step Case1 (many (step ev1) (step Case2 (eval er (βE μ3 << (exts ρ1 xs (map (hat ρ3 !) ys))))))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev1) (select (eval (ConApp k ys) (βE μ3 << ρ3)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (many (step ev1) (eval (ConApp k ys) (βE μ3 << ρ3))) (cont << alts))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Case1 (select (eval e (βE μ1 << ρ1)) (cont << alts))
    =   {- Refold |eval (Case e alts) (βE μ1 << ρ1)| -}
        eval (Case e alts) (βE μ1 << ρ1)
    \end{spec}
\end{itemize}
\end{proof}

Using |persistHeap|, we can give a Galois connection expressing correctness of a
by-name analysis \wrt by-need semantics:

% TODO There is potential to extract useful Galois Connections from this large
% one, but it is far more succinct and comprehensible to give it directly.

\begin{lemma}[Parametric induction principle, binary]
\label{thm:param-ind-2}
If |polydef sss| and |needenv ρ|, some relation $R ⊆ |DNeed| \times |hat D|$
\[
  \inferrule
    {(\forall |a|.\ \later (|fetch a|,|fetch a|) ∈ R) \\ \mathit{inst} ∈ \mathsf{Dict}(P)}
    {|sss ρ| ∈ P}
\]
\end{lemma}
\begin{proof}
By |polydef sss|, we get the free theorem
\[
  (|sss|,|sss|) ∈ \forall \mathcal{X}.\ \mathsf{Dict}(\mathcal{X}) → (|Name| \pfun \mathcal{X}) → \mathcal{X}.
\]
We instantiate it at $R(d_1,d_2) \triangleq d_1 = d_2 \land d_1 ∈ P$, the
instance dictionary $\mathit{inst} ∈ \mathsf{Dict}(|DNeed|)$ and |ρ| to derive the
following assertion:
\[
  \inferrule
    {(\mathit{inst},\mathit{inst}) ∈ \mathsf{Dict}(R) \\ (|ρ|,|ρ|) ∈ (|Name| \pfun R)}
    {(|sss ρ|,|sss ρ|) ∈ R}
\]
Note that $(|d|, |d|) ∈ R$ is equivalent to $|d| ∈ P$, so it suffices to
show the two premises of the rule, which become our subgoals.

The first subgoal $(\mathit{inst},\mathit{inst}) ∈ \mathsf{Dict}(R)$ follows
by $\mathit{inst} ∈ \mathsf{Dict}(P)$.

For the second subgoal $(|ρ|,|ρ|) ∈ (|Name| \pfun R)$, it suffices to show
\begin{equation}
  \forall |many ev|, |a|.\ (|many (step ev) (fetch a)|,|many (step ev) (fetch a)|) ∈ R. \label{eqn:step-induction}
\end{equation}
The property for |step :: Later DNeed -> DNeed| (making
explicit that the |Later| that the implementation of |step| embeds) implied by
$\mathit{inst} ∈ \mathsf{Dict}(P)$ is as follows
\[
  \forall |ev|,|d1|,|d2|.\ \later ((|d1|,|d2|) ∈ R) \implies (|step ev d1|, |step ev d2|) ∈ R.
\]
We instantiate with the assumption
$\forall |a|.\ \later ((|fetch a|, |fetch a|) ∈ R)$
to show the goal \Cref{eqn:step-induction}.
\end{proof}

\begin{lemma}[Definable stuff]
\label{thm:definable}
If |needd d1|, |needheap μ1|, |adom d1 ⊆ dom μ1| and |d1 μ1 = Step ev (d2 μ2)|
then |needd d2|, |μ1 ~> μ2| and |adom d2 ⊆ dom μ2|.

Maybe also about values.
\end{lemma}

\begin{lemma}[Indexed parametricity]
Let $R_|μ| ⊆ |DNeed| \times |hat D|$ be some relation indexed by a definable heap.
If the following lemmas hold for all |μ1| such that |μ ~> μ1|,
then |(evalNeed2 e ρ, evalD (hat D) e (hat ρ)) ∈ Rel(μ)|.
\begin{itemize}
  \item |μ1 ~> μ2 ==> Rel(μ1) ⊆ Rel(μ2)|
  \item |(ρ,hat ρ) ∈ Name :-> Rel(μ)|
  \item |(step,hat step) ∈ Event -> Later Rel(μ1) -> Rel(μ1)|
  \item |(stuck,hat stuck) ∈ Rel(μ1)|
  \item |(fun,hat fun) ∈ (Rel (μ1) -> Rel(μ1)) -> Rel(μ1)|
  \item |(apply,hat apply) ∈ Rel(μ1) -> Rel(μ1) -> Rel(μ1)|
  \item |(con,hat con) ∈ Tag -> [Rel(μ1)] -> Rel(μ1)|
  \item |(select,hat select) ∈ Rel(μ1) -> (Tag :-> ([Rel(μ1)] -> Rel(μ1))) ->  Rel(μ1)|
  \item $|a| \not∈ |dom μ1 ==> forall d. (bind,hat bind) ∈ Later (Later (Rel(ext μ1 a (memo a d))) -> Rel(ext μ1 a (memo a d))) -> (Later (Rel(ext μ1 a (memo a d))) -> Rel(ext μ1 a (memo a d))) -> Rel(μ1)|$
\end{itemize}
\end{lemma}

\begin{lemma}[By-need bind]
\label{thm:by-need-bind}
It is |βT ((d >>= f) μ1) ⊑ hat f (hat d)| if
\begin{enumerate}
  \item |βT (d μ1) ⊑ hat d|, and
  \item for all events |ev| and elements |hat d'|, |(hat step) ev ((hat f) (hat d')) ⊑ (hat f) ((hat step) ev (hat d'))|, and
  \item for all values |v| and heaps |μ2| such that |μ1 ~> μ2|, |βT (f v μ2) ⊑ (hat f) (βT (Ret (v, μ2)))|.
\end{enumerate}
\end{lemma}
\begin{proof}
By Löb induction.

If |d μ1 = Step ev (d' μ1')|, define |hat d' := βT (d' μ1')| and note that
|μ1 ~> μ1'| by \Cref{thm:definable}.
We get
\begin{spec}
  βT ((d >>= f) μ1) = βT (Step ev ((d' >>= f) μ1')) = (hat step) ev (βT ((d' >>= f) μ1'))
⊑  {- Induction hypothesis at |βT (d' μ1') = hat d'|, Monotonicity of |hat step| -}
  hat step ev ((hat f) (βT d' μ1'))
⊑  {- Assumption (2) -}
  (hat f) ((hat step) ev (βT d' μ1')) = (hat f) (βT d μ1)
⊑  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}
Note that in order to apply the induction hypothesis at |μ1'| above, we need
refine assumption (3) to apply at any |μ2| such that |μ1' ~> μ2|.
This would not be possible without generalising for any such |μ2| in the first
place.

Otherwise, |d = return v| for some |v :: Value|.
\begin{spec}
  βT ((return v >>= f) μ1) = βT (f v μ1)
⊑  {- Assumption (3) -}
  (hat f) (βT (Ret v, μ1)) = (hat f) (βT d μ1)
⊑  {- Assumption (1) -}
  (hat f) (hat d)
\end{spec}
\end{proof}

\begin{theorem}[Parametric By-need Interpretation]
\label{thm:soundness-by-need}
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain|,
|HasBind| and |Lat|, and let |αT| and |αE| be the abstraction functions from
\Cref{fig:abstract-name-need}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold, then
\[
  |polydef sss /\ needenv ρ /\ needheap μ ==> αT ^ (set (sssD DNeed ρ μ)) ⊑ sssD (hat D) (αE ^ (set ((ρ,μ))))|
\]
\end{theorem}
\begin{proof}
We simplify the proof obligation for the single-trace case, referring to representation functions instead:
\[
  |polydef sss /\ needenv ρ /\ needheap μ ==> βT (sssD DNeed ρ μ) ⊑ sssD (hat D) (βD^(μ) << ρ)|
\]
where |βD^(μ)^(d) := βT (d μ)| is the representation function of |αD| and
|f << m| maps |f| over every entry in |m| as defined in \Cref{fig:map}.
\[
  R_|μ|(|d|, |hat d|) \triangleq |needd d /\ adom d ⊆ dom μ /\ βT (d μ) ⊑ hat d|
\]
The goal is to prove $(|sssD DNeed ρ|,|sssD (hat D) (βD^(μ) << ρ)|) ∈ R_|μ|$.
%Note that $|μ1 ~> μ2 ==>| R_{|μ1|} ⊆ R_{|μ2|}$,
%and $|μ1 ~> μ2 /\ adom d ⊆ dom μ1 /\| R_{|μ2|}(|d|,|hat d|) \implies R_{|μ1|}(|d|,|hat d|)$
%by \Cref{thm:heap-progress-persist}.
\[
  \inferrule
    {(\mathit{inst},\mathit{\widehat{inst}}) ∈ \mathsf{Dict}(R_|μ|) \\ (|ρ|,|(βD^(μ) << ρ)|) ∈ (|Name| \pfun R_|μ|)}
    {(|sssD DNeed ρ|,|sssD (hat D) (βD^(μ) << ρ)|) ∈ R_|μ|}
\]
Compared to the proof for by-name, the only differences are related to heap progression and the implementation of |bind|.
(Somewhat unsurprising, given that only the implementation of |bind| differs.)

\begin{itemize}
  \item \textbf{Case }$(|ρ|,|(βD^(μ) << ρ)|) ∈ (|Name| \pfun R_|μ|)$:
    The goal is to show |forall x. x ∈ dom ρ ==> βT ((ρ!x) μ) ⊑ βD^(μ)^(ρ!x)|, and that follows by reflexivity.

  \item \textbf{Case |step|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R_|μ|}{(|step ev d|, |hat step ev (hat d)|) ∈ R_|μ|}$. \\
    Then |βT (Step ev (d μ) = hat step ev (βT (d μ)) ⊑ hat step ev (hat d)| by assumption and monotonicity.

  \item \textbf{Case |stuck|}.
    Goal: $(|stuck|, |hat stuck|) ∈ R_|μ|$. \\
    Then |βT (stuck μ) = βT (Ret (Stuck, μ)) = hat stuck|.

  \item \textbf{Case |fun|}.
    Goal: $\inferrule{\forall (|d|,|(hat d)|) ∈ R_|μ|.\ (|f d|, |hat f (hat d)|) ∈ R_|μ|}{(|fun f|, |hat fun (hat f)|) ∈ R_|μ|}$. \\
    Then |βT (fun f μ) = βT (Ret (Fun f, μ)) = (hat fun) (αD^(μ) . powMap f . γD^(μ))| and
    it suffices to show that
    |(αD^(μ) . powMap f . γD^(μ)) ⊑ hat f| by monotonicity of |hat fun|.
    \begin{spec}
      (αD^(μ) . powMap f . γD^(μ)) (hat d)
    =  {- Unfold |powMap|, |αD^(μ)|, simplify -}
      Lub (βT (f d μ) | d ∈ γD^(μ) (hat d))
    ⊑  {- Apply premise to |d ∈ γD^(μ) (hat d) <==> βT (d μ) ⊑ hat d| -}
      hat f (hat d)
    \end{spec}

  \item \textbf{Case |apply|}.
    Goal: $\inferrule{(|d|,|(hat d)|) ∈ R_|μ| \\ (|a|,|(hat a)|) ∈ R_|μ|}{(|apply d a|, |hat apply (hat d) (hat a)|) ∈ R_|μ|}$. \\
    |apply d a| is defined as |d >>= \v -> case v of Fun g -> g a; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-need-bind} at |hat f (hat d) := hat apply (hat d) (hat a)|.
    We get three subgoals for the premises of \Cref{thm:by-need-bind}:
    \begin{itemize}
      \item |βT (d μ) ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R_|μ|$.
      \item |forall ev (hat d'). (hat step) ev ((hat apply) (hat d') (hat a)) ⊑ (hat apply) ((hat step) ev (hat d')) (hat a)|: By assumption \textsc{Step-App}.
      \item |forall v μ2. μ ~> μ2 ==> βT ((case v of Fun g -> g a; _ -> stuck) μ2) ⊑ hat apply (βT (Ret v, μ2)) (hat a)|: \\
        By cases over |v|.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}: \\
            Then |βT (stuck μ2) = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Con k ds|}: \\
            Then |βT (stuck μ2) = hat stuck ⊑ (hat apply) ((hat con) k (hat ds)) (hat a)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Fun g|}:
            Then
            \begin{spec}
                βT (g a μ2)
              ⊑  {- |id ⊑ γD^(μ2) . αD^(μ2)|, rearrange -}
                (αD^(μ2) . powMap g . γD^(μ2)) (βT (a μ2))
              ⊑  {- |μ ~> μ2 ==> βT (a μ2) ⊑ βT (a μ)| (\Cref{thm:heap-progress-persist}) -}
                (αD^(μ2) . powMap g . γD^(μ2)) (βT (a μ))
              ⊑  {- Assumption |βT (a μ) ⊑ hat a| -}
                (αD^(μ2) . powMap g . γD^(μ2)) (hat a)
              ⊑  {- Assumption \textsc{Beta-App} -}
                (hat apply) ((hat fun) (αD^(μ2) . powMap g . γD^(μ2))) (hat a)
              =  {- Definition of |βT|, |v| -}
                (hat apply) (βT (Ret v, μ2)) (hat a)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case |con|}.
    Goal: $\inferrule{(|ds|,|(hat ds)|) ∈ |[{-"R_{\varid{μ}}"-}space]|}{(|con k ds|, |(hat con) k (hat ds)|) ∈ R_|μ|}$. \\
    Then |βT (con k ds μ) = βT (Ret (Con k ds, μ)) = (hat con) k (map (αD^(μ) . set) ds)|.
    The assumption $(|ds|,|(hat ds)|) ∈ |[{-"R_{\varid{μ}}"-}space]|$ implies |map (αD^(μ) . set) ds ⊑ hat ds| and
    the goal follows by monotonicity of |hat con|.

  \item \textbf{Case |select|}.
    Goal: $\inferrule{(|d|,|hat d|) ∈ R_|μ| \\ (|alts|,|hat alts|) ∈ |Tag :-> ([{-"R_{\varid{μ}}"-}space] -> {-"R_{\varid{μ}}"-}space)|}{(|select d alts|, |(hat select) (hat d) (hat alts)|) ∈ R_|μ|}$. \\
    |select d alts| is defined as |d >>= \v -> case v of Con k ds || k ∈ dom alts  -> (alts ! k) ds; _ -> stuck|.
    In order to show the goal, we need to apply \Cref{thm:by-need-bind} at |hat f (hat d) := hat select (hat d) (hat alts)|.
    We get three subgoals for the premises of \Cref{thm:by-need-bind}:
    \begin{itemize}
      \item |βT (d μ) ⊑ hat d|: By assumption $(|d|,|(hat d)|) ∈ R_|μ|$.
      \item |forall ev (hat d'). (hat step) ev ((hat select) (hat d') (hat alts)) ⊑ (hat select) ((hat step) ev (hat d')) (hat alts)|: By assumption \textsc{Step-Sel}.
      \item |forall v μ2. μ ~> μ2 ==> βT (select d alts μ2) ⊑ (hat select) (βT (Ret v, μ2)) (hat alts)|: \\
        By cases over |v|. The first three all correspond to when the continuation of |select| gets stuck.
        \begin{itemize}
          \item \textbf{Case |v = Stuck|}:
            Then |βT (stuck μ2) = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Unwind-Stuck}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT (stuck μ2) = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT (stuck μ2) = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Intro-Stuck}, for the suitable |hat ds|.
          \item \textbf{Case |v = Con k ds|, $|k| ∈ |dom alts|$}:
            Then
            \begin{spec}
                βT ((alts ! k) ds μ2)
              ⊑  {- |id ⊑ γD^(μ2) . αD^(μ2)|, rearrange -}
                (αD^(μ2) . powMap (alts ! k) . map γD^(μ2)) (map (αD^(μ2) . set) ds)
              ⊑  {- Assumption $(|alts|,|hat alts|) ∈ |Tag :-> ([{-"R_{\varid{μ}}"-}space] -> {-"R_{\varid{μ}}"-}space)|$ -}
                (hat alts ! k) (map (αD^(μ2) . set) ds)
              ⊑  {- Assumption \textsc{Beta-Sel} -}
                (hat select) ((hat con) k (map (αD^(μ2) . set) ds)) (hat alts)
              =  {- Definition of |βT|, |v| -}
                (hat select) (βT (Ret (v, μ2))) (hat alts)
            \end{spec}
        \end{itemize}
    \end{itemize}

  \item \textbf{Case |bind|}.
    Goal: $\inferrule{(\forall (|d|,|(hat d)|) ∈ R_|μ|.\ (|rhs d|, |hat rhs (hat d)|) ∈ R_|μ|) \\ (\forall (|d|,|(hat d)|) ∈ R_|μ|.\ (|body d|, |hat body (hat d)|) ∈ R_|μ|)}
                     {(|bind rhs body|, |(hat bind) (hat rhs) (hat body)|) ∈ R_|μ|}$. \\
    It is |bind rhs body μ = body (fetch a) (ext μ a (memo a (rhs (fetch a))))| and |(hat body) (lfp (hat rhs)) ⊑ (hat bind) (hat rhs) (hat body)| by Assumption \textsc{Bind-ByName},
    so it suffices to prove
    \begin{spec}
      βT (body (fetch a) (ext μ a (memo a (rhs (fetch a))))) ⊑ (hat body) (lfp (hat rhs))
    \end{spec}
    Note that |μ ~> (ext μ a (memo a (rhs (fetch a))))|, so the
    goal follows from the assumption $|(body,hat body)| ∈ R_|μ| → R_|μ|$, provided
    we can show that $|(fetch a,lfp (hat rhs))| ∈ R_|μ|$.


    Let us first establish that $(|fix rhs|, |lfp (hat rhs)|) ∈ R_|μ|$, leaning on
    our theory about safety extension in \Cref{sec:safety-extension}:
    \begin{spec}
      αD ^ ((set (fix rhs)))
    ⊑  {- By \Cref{thm:safety-extension} -}
      lfp (αD . powMap rhs . γD)
    =  {- Unfolding |powMap|, |αD| -}
      lfp (\(hat d) -> Lub (βT (rhs d) | d ∈ γD (hat d))
    ⊑  {- Apply assumption to $|αD ^ ((set d)) ⊑ αD (γD (hat d)) ⊑ hat d <==> | (|d|,|hat d|) ∈ R_|μ|$ -}
      lfp (hat rhs)
    \end{spec}
    Applying this fact to the second assumption proves
    $(|body (fix rhs)|, |(hat body) (lfp (hat rhs))|) ∈ R_|μ|$ and thus the goal.
\end{itemize}
\end{proof}

\begin{theorem}[Sound By-need Interpretation]
\label{thm:soundness-by-need}
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain|,
|HasBind| and |Lat|, and let |αT :<->: γT = nameNeed|, as well as |αE μ
:<->: γE μ = persistHeap μ| from \Cref{fig:name-need}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |eval| instantiates at |hat D| to an abstract interpreter that is sound
\wrt |γE -> αT|, that is,
\[
  |αT (set (evalNeed e ρ μ)) ⊑ (evalD (hat D) e (αE μ << set << ρ))|
\]
\end{theorem}
\begin{proof}
As in \Cref{thm:soundness-by-name}, we simplify our proof obligation to the single-trace case:
\[
  |forall ρ. βT (evalNeed e ρ μ) ⊑ (evalD (hat D) e (βE μ << ρ))|,
\]
where |βT := αT . set| and |βE μ := αE μ . set| are the representation
functions corresponding to |αT| and |αE|.
We proceed by Löb induction.

Whenever |evalNeed e ρ μ = many (Step ev) (evalNeed v ρ2 μ2)| yields a balanced trace
and makes at least one step, we can reuse the proof for
\Cref{thm:eval-preserves-need} as follows:
\begin{spec}
    βT (evalNeed e ρ μ)
=   {- |evalNeed e ρ μ = many (Step ev) (evalNeed v ρ2 μ2)|, unfold |βT| -}
    many (step ev) (βT (evalNeed v ρ2 μ2))
⊑   {- Induction hypothesis (needs non-empty |many ev|) -}
    many (step ev) (eval v (βE μ2 << ρ2))
⊑   {- \Cref{thm:eval-preserves-need} -}
    eval e (βE μ << ρ)
\end{spec}

Thus, without loss of generality, we may assume that if |e| is not a value,
then either the trace diverges or is stuck.
We proceed by cases over |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |βT|.
    \begin{spec}
        βT ((ρ ! x) μ)
    =   {- |needenv ρ|, Unfold |βT| -}
        step (Look y) (βT (fetch a μ))
    =   {- |needheap μ| -}
        step (Look y) (βT (memo a (evalNeed e1 ρ1 μ)))
    \end{spec}
    By assumption, |memo a (evalNeed e1 ρ1 μ)| diverges or gets stuck and the result
    is equivalent to |evalNeed e1 ρ1 μ|.
    \begin{spec}
    =   {- Diverging or stuck -}
        step (Look y) (βT (evalNeed e1 ρ2 μ))
    ⊑   {- Induction hypothesis -}
        step (Look y) (eval e1 (βE μ << ρ1))
    =   {- Refold |βE| -}
        βE μ (ρ ! x)
    \end{spec}

  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        βT (evalNeed (Lam x body) ρ μ)
    =   {- Unfold |evalNeed|, |βT| -}
        fun (\(hat d) -> Lub (step App2 (βT (evalNeed body (ext ρ x d) μ)) | βE μ d ⊑ hat d))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> Lub (step App2 (eval body (βE μ << (ext ρ x d))) | βE μ d ⊑ hat d))
    ⊑   {- Least upper bound / |αE . γE ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext ((βE μ << ρ)) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (βE μ << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k xs|:
    \begin{spec}
        βT (evalNeed (ConApp k xs) ρ μ)
    =   {- Unfold |evalNeed|, |βT| -}
        con k (map ((βE μ << ρ) !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (βE μ << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|, |Case e alts|:
    The same steps as in \Cref{thm:soundness-by-name}.
% When I checked last, it looked like this:
%    Our proof obligation can be simplified as follows
%    \begin{spec}
%        βT (evalNeed (App e x) ρ μ)
%    =   {- Unfold |evalNeed|, |βT| -}
%        step App1 (βT (apply (evalNeed e ρ μ) (ρ ! x)))
%    =   {- Unfold |apply| -}
%        step App1 (βT (evalNeed e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    ⊑   {- By cases, see below -}
%        step App1 (apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x))
%    =   {- Refold |eval| -}
%        eval (App e x) (βE μ << ρ)
%    \end{spec}
%
%    When |evalNeed e ρ μ| diverges, we have
%    \begin{spec}
%    =   {- |evalNeed e ρ μ| diverges, unfold |βT| -}
%        step ev1 (step ev2 (...))
%    ⊑   {- Assumption \textsc{Step-App} -}
%        apply (step ev1 (step ev2 (...))) ((βE μ << ρ) ! x)
%    =   {- Refold |βT|, |evalNeed| -}
%        apply (βT (evalNeed e ρ μ)) ((βE μ << ρ) ! x)
%    ⊑   {- Induction hypothesis -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}
%    Otherwise, |evalNeed e ρ μ| must produce a value |v| in heap |μ2|.
%    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
%    (resp. |d := con k (map (βE μ) ds)|) and have
%    \begin{spec}
%        βT (evalNeed e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
%    =   {- |evalNeed e ρ μ = many (step ev) (return v)|, unfold |βT| -}
%        many (step ev) (βT (return v μ2 >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    =   {- |v| not |Fun|, unfold |βT| -}
%        many (step ev) stuck
%    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map βT ds)| -}
%        many (step ev) (apply (d μ2) a)
%    ⊑   {- Assumption \textsc{Step-App} -}
%        apply (many (step ev) (d μ2)) ((βE μ << ρ) ! x)
%    =   {- Refold |βT|, |evalNeed| -}
%        apply (βT (evalNeed e ρ μ)) ((βE μ << ρ) ! x)
%    ⊑   {- Induction hypothesis -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}
%    In the final case, we have |v = Fun f|, which must be the result of some
%    call |evalNeed (Lam y body) ρ1 μ2|; hence
%    |f := \d μ2 -> step App2 (evalNeed body (ext ρ1 y d) μ2)|.
%    \begin{spec}
%        βT (evalNeed e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
%    =   {- |evalNeed e ρ μ = many (step ev) (return v μ2)|, unfold |βT| -}
%        many (step ev) (βT (return v μ2 >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    =   {- |v=Fun f|, with |f| as above; unfold |βT| -}
%        many (step ev) (step App2 (βT (evalNeed body (ext ρ1 y (ρ ! x)) μ2)))
%    ⊑   {- Induction hypothesis -}
%        many (step ev) (step App2 (eval body (βE μ2 << (ext ρ1 y (ρ ! x)))))
%    ⊑   {- Same as in proof for \Cref{thm:eval-preserves-need} -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    We can make one step to see
    \begin{spec}
      evalNeed (Let x e1 e2) ρ μ = Step Let1 (evalNeed e2 ρ1 μ1),
    \end{spec}
    where |ρ1 := ext ρ x (step (Look x) (fetch a))|,
    |a := nextFree μ|,
    |μ1 := ext μ a (memo a (evalNeed2 e1 ρ1))|.

    Then |(βE μ1 << ρ1) ! y ⊑ (βE μ << ρ) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:heap-progress-persist},
    and |(βE μ1 << ρ1) ! x = step (Look x) (eval e1 (βE μ1 << ρ1))|.
    \begin{spec}
        βT (evalNeed (Let x e1 e2) ρ μ)
    =   {- Unfold |evalNeed| -}
        βT (bind  (\d1 -> evalNeed2 e1 ρ1) (\d1 -> Step Let1 (evalNeed2 e2 ρ1)) μ)
    =   {- Unfold |bind|, $|a| \not\in |dom μ|$, unfold |βT| -}
        step Let1 (βT (evalNeed e2 ρ1 μ1))
    ⊑   {- Induction hypothesis, unfolding |ρ1| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ) x (βE μ1 (ρ1 ! x))))
    ⊑   {- Expose fixpoint, approximating |βE μ1 (ρ1 ! x)| by |ext (βE μ << ρ) x (βE μ1 (ρ1 ! x))| -}
        step Let1 (eval e2 (ext (βE μ << ρ) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE μ << ρ) x (hat d1)))))))
    =   {- Partially unroll fixpoint -}
        step Let1 (eval e2 (ext (βE μ << ρ) x (step (Look x) (lfp (\(hat d1) -> eval e1 (ext (βE μ << ρ) x (step (Look x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = βE μ << ρ| -}
        bind  (\d1 -> eval e1 (ext (βE μ << ρ) x (step (Look x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (βE μ << ρ) x (step (Look x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βE μ << ρ)| -}
        eval (Let x e1 e2) (βE μ << ρ)
    \end{spec}
\end{itemize}
\end{proof}

We can apply this by-need abstraction theorem to usage analysis on open
expressions, just as before:

\begin{lemma}[|evalUsg| abstracts |evalNeed|, open]
\label{thm:usage-abstracts-need}
Usage analysis |evalUsg| is sound \wrt |evalNeed|, that is,
\[
  |αT (set (evalNeed e ρ μ)) ⊑ evalUsg e (αE << set << ρ) where αT :<->: _ = nameNeed; αE μ :<->: _ = persistHeap μ|
\]
\end{lemma}
\begin{proof}
By \Cref{thm:soundness-by-need}, it suffices to show the abstraction laws
in \Cref{fig:abstraction-laws} as done in the proof for \Cref{thm:usage-abstracts-need-closed}.
\end{proof}

%if False
% Here is an attempt to recover a frame rule for |evalNeed|, but we didn't need it
% so far. Perhaps the notion of equivalence modulo readdressing permutations
% opens up possilibities for making ~> a partial order as well.
% We don't seem to need it, though.
For the next lemma, we need to identify heaps modulo $α$, \ie \emph{readdressing},
in the following sense: $|μ1| =_α |μ2|$ iff there exists a permutation |σ ::
Addr -> Addr| such that |heap σ μ1 = μ2|, where
\begin{center}
\begin{spec}
  heap σ μ  = [ σ a ↦ memo (σ a) (eval e (env σ ρ)) | memo a (eval e ρ) <- μ ]
  env σ ρ   = [ x ↦ step (Look y) (fetch (σ a)) | step (Look y) (fetch a) <- ρ ]
\end{spec}
\end{center}
\noindent
We will make use of the overloaded notation |σ μ := heap σ μ|, |σ ρ := env σ ρ|
for convenience.

\sg{I think we can show antisymmetry and confluence modulo readdressing,
compensating for the deterministic allocator that is |nextFree|. I don't plan
to prove that, though.}

\begin{lemma}[Congruence modulo readdressing]
\label{thm:eval-perm}
Let |σ1 :: dom μ1 -> dom μ1| be a permutation.
If   |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|,
then there exists a permutation |σ2 :: dom μ2 -> dom μ2|
such that |forall a ∈ dom μ1. σ1 a = σ2 a|
and |eval e (σ1 ρ1) (σ1 μ1) = many (Step (σ1 ev)) (eval v (σ2 ρ2) (σ2 μ2))|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    It is |σ1 ρ1 ! x = step (Look y) (fetch (σ1 a))|
    and   |σ1 μ1 ! σ1 a = memo (σ1 a) (eval e1 (σ1 ρ3))|,
    so |eval x (σ1 ρ1) (σ1 μ1) = Step (Look y) (memo (σ1 a) (eval e1 (σ1 ρ3)) (σ1 μ1))|.
    We apply the induction hypothesis to |eval e1 ρ3|.
    The subsequent update transition updates |σ1 a| with |memo (σ1 a) (eval v (σ2 ρ2))|,
    which is exactly what |σ2 μ2 ! σ1 a = σ1 μ2 ! σ1 a| looks like.
  \item \textbf{Case} |Lam x e|, |ConApp k xs|: Easy to see for |σ1 = σ2|.
  \item \textbf{Case} |App e x|:
    In the interesting case, the lambda body in the value of |e| is entered with
    |ext (σ3 ρ3) y (σ1 ρ1 ! x) = ext (σ3 ρ3) y (σ3 ρ1 ! x)|,
    where |σ3| is obtained from applying the induction hypothesis to |e|.
    Since |σ3| is an extension of |σ1|, we can invoke the induction hypothesis
    once more to show the goal.
  \item \textbf{Case} |Case e alts|: Similar to |App|.
  \item \textbf{Case} |Let x e1 e2|:
    Set |ext σ1 (nextFree μ1) (nextFree (σ1 μ1))| and apply the induction hypothesis.
    The returned |σ2| agrees with |σ1| on |dom μ1 ∪ set (nextFree μ1)|, so it
    also agrees on |dom μ1|.
\end{itemize}
\end{proof}

From now on we identify heaps and ambient environments modulo readdressing.
Furthermore, let |μ `oplus` μ'| denote the disjoint extension of |μ| with
the bindings in |μ'| (each of which may scope over |μ| and thus |μ'| is not a
realisable heap).

\begin{lemma}[Frame rule]
% Currently dead, but nevertheless interesting
If   |adom ρ1 ⊆ dom μ1|,
then |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
if and only if |eval e ρ1 (μ1 `oplus` μ') = many (Step ev) (eval v ρ2 (μ2 `oplus` μ'))|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
     It is |eval x ρ1 μ1 = Step (Look y) (memo a (eval e1 ρ3 μ1))| for the
     suitable |a|,|y|.
     We can apply the induction hypothesis to |e1|, since |adom ρ3 ⊆ dom μ1|
     by |needheap μ1|.
     Tracing the update step is routine.
  \item \textbf{Case} |Lam x e|, |ConApp k xs|: Easy to see for |μ1 = μ2|.
  \item \textbf{Case} |App e x|:
    In the interesting case, the lambda body in the value of |e| is entered with
    |ext ρ3 y (ρ1 ! x)| in a heap |μ3 `oplus` μ'|,
    |adom (ext ρ3 y (ρ1 ! x)) ⊆ dom μ3|, which is the situation we invoke the
    induction hypothesis at once more to show the goal.
  \item \textbf{Case} |Case e alts|: Similar to |App|.
  \item \textbf{Case} |Let x e1 e2|:
    In case $|nextFree μ1| \not= |nextFree (μ1 `oplus` μ')|$, we permute |μ2|
    after the fact, as justified by \Cref{thm:eval-perm}.

    We apply the induction hypothesis to
    |eval e2 (ext ρ1 x _) (ext μ1 (nextFree a) _ `oplus` μ')| to show the goal.
\end{itemize}
\end{proof}
%endif
