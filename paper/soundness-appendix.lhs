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
where the \emph{extension} $|αinf| : (\pow{\Traces^{\infty}},⊆) \rightleftarrows (|hat D|, ⊑) : |γinf|$ of
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
The goal is to show $|τ| ∈ |γinf|(|hat d|)$, as follows:
\begin{spec}
      τ ∈ {-" P "-}
==>   {- $P$ safety property -}
      (forall τ2. τ2 <. τ ==> τ2 ∈ {-" P ∩ \Traces^{*} "-})
==>   {- Assumption $P ∩ \Traces^{*} ⊆ |γ|(|hat d|)$ -}
      (forall τ2. τ2 <. τ ==> τ2 ∈ γ (hat d))
<==>  {- Definition of Union -}
      Cup (τ2 | τ2 <. τ) ⊆ γ (hat d)
<==>  {- Galois -}
      α (Cup (τ2 | τ2 <. τ)) ⊑ hat d
<==>  {- Definition of |βinf| -}
      βinf τ ⊑ hat d
<==>  {- Galois -}
      τ ∈ γinf (hat d)
\end{spec}
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

Compared to the by-need trace abstraction in \Cref{fig:abstract-name-need}, the
by-name trace abstraction function in \Cref{fig:abstract-name} is rather
straightforward because no heap is involved.

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

What follows is the sound abstraction proof by parametricity.
Note that its statement fixes the interpreter to |eval|, however the proof would
still work if generalised to \emph{any} definition with the same type as |eval|!

\begin{theorem}[Abstract By-name Interpretation]
\label{thm:abstract-by-name}
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

The above instantiation yields, in Haskell,
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
            Then |βT^(stuck) = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Stuck-App}.
          \item \textbf{Case |v = Con k ds|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat apply) ((hat con) k (hat ds)) (hat a)| by assumption \textsc{Stuck-App}, for the suitable |hat ds|.
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
            Then |βT^(stuck) = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Stuck-Sel}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT^(stuck) = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Stuck-Sel}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT^(stuck) = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Stuck-Sel}, for the suitable |hat ds|.
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
    It is |bind rhs body = body (fix rhs)| and |(hat body) (lfp (hat rhs)) ⊑ (hat bind) (hat rhs) (hat body)| by Assumption \textsc{ByName-Bind}.
    Let us first establish that $(|fix rhs|, |lfp (hat rhs)|) ∈ R$, leaning on
    our theory about guarded fixpoint abstraction in \Cref{sec:safety-extension}:
    \begin{spec}
      αD ^ (set (fix rhs))
    ⊑  {- By \Cref{thm:guarded-fixpoint-abstraction} -}
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

The goal of this section is to prove \Cref{thm:abstract-by-need} correct,
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
travels together with a heap |μ| that ties the addresses that |d| references to
actual meaning.

There are \emph{many} elements (functions!) |d :: DNeed|, many with very
surprising behavior, but we are only interested in elements \emph{definable}
by our interpreter:

\begin{definition}[Definable by-need entities]
  \label{defn:definable}
  We write |needd d|, |needenv ρ| or |needheap μ| to say that the by-need
  element |d|, environment |ρ| or heap |μ| is \emph{definable}, defined as
  \begin{itemize}
    \item |needenv ρ := forall x ∈ dom ρ. exists y a. ρ ! x = step (Look y) (fetch a)|.
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
modulo readdressing.
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

Readdressing allows us to prove an abstract pendant of the venerable \emph{frame
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
    Follows by the induction hypothesis after readdressing the extended heap
    (\Cref{thm:abstract-readdressing}) so that the induction hypothesis can be applied.
\end{itemize}
\end{proof}

The frame rule in turn is important to show that heap progression preserves the
results of the abstraction function:

\begin{lemma}[Heap progression preserves abstraction]
  \label{thm:heap-progress-mono}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{ByName-Bind}
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
        This follows by applying the abstract frame rule (\Cref{thm:abstract-frame}),
        because |adom ρ1 ⊆ dom μ1|.

      \item \textbf{Case} $\inferrule*[vcenter,left=\progresstomemo]{|μ1 ! a1 = memo a1 (evalNeed2 e ρ3)| \quad |Later (evalNeed e ρ3 μ1 = many (Step ev) (evalNeed v ρ4 μ3))|}{|μ1 ~> ext μ3 a1 (memo a1 (evalNeed2 v ρ4))|}$:\\
        We get to refine |μ2 = ext μ3 a1 (memo a1 (evalNeed2 v ρ4))|.
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
        ⊑   {- Assumption \textsc{Step-Inc} -}
          many (step ev) (βD^(μ3)(memo a (evalNeed2 v ρ2)))
        =   {- Unfold |memo|, |βD| -}
          many (step ev) (βT^(evalNeed v ρ2 μ3 >>= upd))
        =   {- Refold |βT|, |>>=| -}
          βT^(many (Step ev) (evalNeed v ρ2 μ3) >>= upd)
        =   {- |evalNeed e1 ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ3)| -}
          βT^(evalNeed e1 ρ1 μ1 >>= upd)
        =   {- Refold |memo|, |βD| -}
          βD^(μ1)^(memo a (evalNeed2 e1 ρ1))
        \end{spec}
    \end{itemize}
\end{itemize}
\end{proof}

The preceding lemma corresponds to the $\UpdateT$ step of the preservation
\Cref{thm:preserve-absent} where we (and \citet{Sergey:14}) resorted to
hand-waving.
Here, we hand-wave no more!

In order to prove the main soundness \Cref{thm:abstract-by-need},
we need two more auxiliary lemmas about |(>>=)| and environment
access.

\begin{lemma}[By-need bind]
\label{thm:by-need-bind}
It is |βT^((d >>= f) μ1) ⊑ hat f (hat d)| if
\begin{enumerate}
  \item |βT^(d μ1) ⊑ hat d|, and
  \item for all events |ev| and elements |hat d'|, |(hat step) ev ((hat f) (hat d')) ⊑ (hat f) ((hat step) ev (hat d'))|, and
  \item for all values |v| and heaps |μ2| such that |μ1 ~> μ2|, \hfuzz=2em|βT^(f v μ2) ⊑ (hat f) (βT^(Ret (v, μ2)))|.
\end{enumerate}
\end{lemma}
\begin{proof}
By assumption (1), it suffices to show |βT^((d >>= f) μ1) ⊑ hat f (βT^(d μ1))|.
Let us first consider the case where the trace |τ := d μ1| is infinite; then
|τ = (d >>= f) μ1| and hence |βT^((d >>= f) μ1) = βT^(τ)|.
By Löb induction.
\begin{spec}
  βT^((d >>= f) μ1) = βT^(τ) = βT^(Step ev τ') = (hat step) ev (βT^(τ'))
⊑  {- Induction hypothesis at |βT^(τ')|, Monotonicity of |hat step| -}
  hat step ev ((hat f) (βT^(τ')))
⊑  {- Assumption (2) -}
  (hat f) ((hat step) ev (βT^(τ'))) = (hat f) (βT^(τ))
\end{spec}

Otherwise, |d μ1| is finite and |d = evalNeed2 e ρ1| for some |e|,|ρ1| since
|d| is definable.
Then |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)| for some number
of events |many ev|, |v|, |ρ2| and |μ2|.
By \Cref{thm:eval-progression}, we have |μ1 ~> μ2|.
We proceed by induction on |many ev|.

The induction step is the same as in the infinite case above;
we shift the |Step| transition out of the argument to |βT|, apply the induction
hypothesis and apply assumption (2).

The interesting case is the base case, when |many ev| is empty
and |evalNeed e ρ1 μ1 = evalNeed v ρ2 μ2|.
Then we get, defining |sv| as |return sv := evalNeed2 v ρ2|,
\begin{spec}
  βT^((return sv >>= f) μ2) = βT^(f sv μ2)
⊑  {- Assumption (3) at |μ1 ~> μ2| -}
  (hat f) (βT^(Ret sv, μ2)) = (hat f) (βT^(evalNeed v ρ2 μ2))
\end{spec}
Note that in order to apply assumption (3) at |μ2| above, we need that
|μ1 ~> μ2|.
This would not be possible without generalising for any such |μ2| in the first
place.
\end{proof}

\begin{lemma}[By-need environment unrolling]
\label{thm:by-need-env-unroll}
Let |hat D| a domain with instances for |Trace|, |Domain|, |HasBind| and |Lat|,
satisfying $\textsc{Update}$ from \Cref{fig:abstraction-laws},
and let |μ1 := (ext μ a (memo a (evalNeed e1 ρ1))), ρ1 := ext ρ x (step (Look x) (fetch a))|. \\
If |Later (forall e ρ μ. βT^(evalNeed e ρ μ) ⊑ (evalD (hat D) e (βD^(μ) << ρ)))|,
then |βD^(μ1)^(ρ1 ! x) ⊑ step (Look x) (evalD (hat D) e1 (βD^(μ1) << ρ1))|.
\end{lemma}
\begin{proof}
Note that the antecedent is exactly the Löb induction hypothesis of \Cref{thm:abstract-by-need}.
\begin{spec}
  βD^(μ)^(ρ ! x)
=   {- Unfold |ρ ! x|, |μ ! a|, |βD| and |fetch a| -}
  step (Look x) (βT^(memo a (evalNeed2 e1 ρ1) μ))
=   {- Unfold |memo a| -}
  step (Look x) (βT^((evalNeed2 e1 ρ1 >>= upd) μ))
⊑   {- Apply \Cref{thm:by-need-bind}; see below -}
  step (Look x) (evalD (hat D) e1 (βD^(μ) << ρ1))
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

Finally, we can prove \Cref{thm:abstract-by-need}:
