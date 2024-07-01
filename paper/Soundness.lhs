%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Soundness where

import Prelude hiding ((+), (*))
import Data.Set (Set)
import qualified Data.Set as Set
import Order
import Interpreter

instance Eq (D (ByName T)) where
  (==) = undefined
instance Ord (D (ByName T)) where
  compare = undefined
powMap :: (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ undefined $ map f $ Set.toList s
set = P . Set.singleton
\end{code}
%endif

\section{Generic Sound By-Name and By-Need Interpretation}
\label{sec:soundness}

\begin{toappendix}
So far, we have seen how to \emph{use} the abstraction
\Cref{thm:soundness-by-need-closed}, but not proved it.
Proving this theorem correct is the goal of this section,
and we approach the problem from the bottom up.

We will discuss why it is safe to approximate guarded fixpoints with
least fixpoints and why the definition of the Galois connection in
\Cref{fig:name-need-gist} as a fold over the trace is well-defined
in \Cref{sec:safety-extension}.
Then we will go on to prove abstract by-name soundness in
\Cref{sec:by-name-soundness}, and finally by-need soundness in
\Cref{sec:by-need-soundness}.

%include soundness-appendix.lhs

\subsection{Usage Analysis Proofs}

Here we give the proofs for the main body, often deferring to
\Cref{sec:by-need-soundness}.
\end{toappendix}

\begin{figure}
\[\ruleform{\begin{array}{c}
  α_{\mathcal{S}} : (|(Name :-> DNeed) -> DNeed|) \rightleftarrows (|(Name :-> hat D) -> hat D|) : γ_{\mathcal{S}}
  \\
  α_{\Environments} : \pow{(|Name :-> DNeed|) \times |HeapNeed|} \rightleftarrows (|Name :-> hat D|) : γ_{\Environments}
  \\
  α_{\Domain{}} : |HeapNeed| \to \pow{|DNeed|} \rightleftarrows |hat D| : γ_{\Domain{}}
  \\
  α_\Traces : \pow{|T (ValueNeed, HeapNeed)|} \rightleftarrows |hat D| : γ_\Traces
  \qquad
  β_\Traces : |T (ValueNeed, HeapNeed)| \to |hat D|
  \qquad
\end{array}}\]
\belowdisplayskip=0pt
\arraycolsep=2pt
\[\begin{array}{lcl}
α_{\mathcal{S}}(S)(\widehat{ρ}) & = & α_\Traces(\{\  S(ρ)(μ) \mid (ρ,μ) ∈ γ_{\Environments}(\widehat{ρ}) \ \}) \\
α_{\Environments}(R)(x) & = & \Lub \{\  α_{\Domain{}}(μ)(\{ρ(x)\}) \mid (ρ,μ) ∈ R \ \} \\
α_\Traces(T) & = & \Lub \{\  β_\Traces(τ) \mid τ ∈ T \ \} \\
\\[-0.75em]
β_\Traces(|τ|) & = & \begin{cases}
  |step e ({-" β_\Traces(\varid{τ'}) "-})| & \text{if |τ = Step e τ'|} \\
  |stuck|                         & \text{if |τ = Ret (Stuck, μ)|} \\
  |fun (\(hat d) -> {-" α_\Traces(\{\  \varid{f}~\varid{d}~\varid{μ} \mid \varid{d} ∈ γ_{\Domain{}}(\varid{μ})(\widehat{\varid{d}})\ \}) "-})| & \text{if |τ = Ret (Fun f, μ)|} \\
  |con k (map (\d -> {-" α_{\Domain{}}(\varid{μ})(\{\varid{d}\}) "-}) ds)| & \text{if |τ = Ret (Con k ds, μ)|} \\
  \end{cases} \\
\\[-0.75em]
α_{\Domain{}}(μ)(D) & = & \text{... see \Cref{fig:name-need} in \Cref{sec:soundness-detail} ...} \\
\end{array}\]
\caption{Galois connection $α_{\mathcal{S}}$ for by-need abstraction derived from |Trace|, |Domain| and |Lat| instances on |hat D|}
\label{fig:name-need-gist}
\end{figure}

In this section we prove and apply a generic abstract interpretation theorem
of the form
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
This statement can be read as follows:
for a closed expression |e|, the \emph{static analysis} result |evalD (hat D) e emp|
on the right-hand side \emph{overapproximates} ($⊒$) a property of the by-need
\emph{semantics} |evalNeed e emp emp| on the left-hand side.
The abstraction function $α_{\mathcal{S}}$, given in
\Cref{fig:name-need-gist}, generalises this notion to open expressions and
defines the semantic property of interest in terms of the abstract semantic
domain |hat D| of |evalD (hat D) e ρ|, which is short for |eval e ρ :: hat D|.
That is: the type class instances on |hat D| determine $α_{\mathcal{S}}$, and
hence the semantic property that is soundly abstracted by |evalD (hat D) e ρ|.

We will instantiate the theorem at |UD| in order to prove that usage analysis
|evalUsg e ρ = evalD UD e ρ| infers absence, just as absence analysis in
\Cref{sec:problem}.
This proof will be much simpler than the proof for \Cref{thm:absence-correct}.
%The main body will only discuss abstraction of closed terms, but the underlying
%\Cref{thm:soundness-by-need} in the Appendix considers open terms as well.

\begin{figure}
  \[\begin{array}{c}
    \inferrule[\textsc{Mono}]{|d1 ⊑ d2| \\ |f1 ⊑ f2|}{%
      |apply f1 d1 ⊑ apply f2 d2|%
      \textit{ and so on, for all methods of |Trace|, |Domain|, |HasBind|}} \\
    \\[-0.5em]
    \inferrule[\textsc{Step-App}]{}{%
      |step ev (apply d a) ⊑ apply (step ev d) a|} \qquad
    \inferrule[\textsc{Step-Sel}]{}{%
      |step ev (select d alts) ⊑ select (step ev d) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Unwind-Stuck}]{}{%
      \textstyle|stuck ⊑ Lub (apply stuck a, select stuck alts)|} \hspace{1.5em}
    \inferrule[\textsc{Intro-Stuck}]{}{%
      \begin{array}{@@{}l@@{}c@@{}l@@{}}|stuck|&{}⊑{} &\textstyle|Lub (apply (con k ds) a, select (fun x f) alts)| \arcr & ⊔ & \textstyle|Lub (select (con k ds) alts || k {-"\not"-}∈ dom alts)|\end{array}} \\
    \\[-0.5em]
    \inferrule[\textsc{Beta-App}]{%
      |f d = step App2 (evalD (hat D) e (ext ρ x d))|}{%
      |f a ⊑ apply (fun x f) a|} \qquad
    \inferrule[\textsc{Beta-Sel}]{%
      |(alts ! k) ds = step Case2 (evalD (hat D) er (exts ρ xs ds))|}{%
      |(alts ! k) ds ⊑ select (con k ds) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Bind-ByName}]{|rhs d1 = evalD (hat D) e1 (ext ρ x (step (Look x) d1))|\\ |body d1 = step Let1 (evalD (hat D) e2 (ext ρ x d1))|}{|body (lfp rhs) ⊑ bind rhs body|}
  \end{array}\]
  \fcolorbox{lightgray}{white}{$\begin{array}{c}
    \inferrule[\textsc{Step-Inc}]{}{|d ⊑ step ev d|}
    \qquad
    \inferrule[\textsc{Update}]{}{|step Upd d = d|} \\
  \end{array}$}
  \caption{By-name and \fcolorbox{lightgray}{white}{by-need} abstraction laws for type class instances of abstract domain |hat D|}
  \label{fig:abstraction-laws}
\end{figure}

\subsection{Sound By-Name and By-Need Interpretation}

This subsection is dedicated to the following derived inference rule for sound
by-need interpretation (\Cref{thm:soundness-by-need-closed}), referring to the
\emph{abstraction laws} in \Cref{fig:abstraction-laws} by name:
\[\begin{array}{c}
  \inferrule{%
    \textsc{Mono} \\ \textsc{Step-App} \\ \textsc{Step-Sel} \\ \textsc{Unwind-Stuck} \\
    \textsc{Intro-Stuck} \\ \textsc{Beta-App} \\ \textsc{Beta-Sel} \\ \textsc{Bind-ByName} \\
    \textsc{Step-Inc} \\ \textsc{Update}
  }{%
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|
  }
\end{array}\]
\noindent
In other words: prove the abstraction laws for an abstract domain |hat D| of
your choosing and we give you a proof of sound abstract by-need
interpretation for the static analysis |evalD (hat D)|!

Note that \emph{we} get to determine the abstraction function $α_{\mathcal{S}}$ based
on the |Trace|, |Domain| and |Lat| instance on \emph{your} |hat D|.
\Cref{fig:name-need-gist} replicates the gist of how $α_{\mathcal{S}}$ is thus derived.

For a closed expression |e|, $α_{\mathcal{S}}(|evalNeed1 e|)(|emp|)$ simplifies
to $β_\Traces(|evalNeed e emp emp|)$, which folds the by-need
trace into an abstract domain element in |hat D|.
Since |hat D| has a |Lat| instance, such a $β_\Traces$ is called a \emph{representation
function}~\citep[Section 4.3]{Nielson:99}, giving rise to the Galois
connection $α_\Traces \rightleftarrows γ_\Traces$.
Function $β_\Traces$ eliminates every |Step ev| in the trace with a call to
|step ev|, and eliminates every concrete |Value| at the end of the trace with a
call to the corresponding |Domain| method.

To that end, the final heap |μ| is \emph{persisted} into a Galois connection
$α_{\Domain{}}(|μ|) \rightleftarrows γ_{\Domain{}}(|μ|)$.
The precise definition of this Galois connection is best left to the Appendix.
Very roughly, $α_{\Domain{}}(|μ|)$ abstracts entries of concrete environments |ρ ! x|
of the form |Step (Look y) (fetch a)| into entries of abstract environments
|hat ρ ! x|, resolving all |fetch a| operations using entries |μ ! a| in the
persisted heap.

When the trace ends in a |Con| value, every field denotation |d| is abstracted
via $α_{\Domain{}}(|μ|)(|d|)$.
When the trace ends in a |Fun| value, an abstract argument denotation |hat d| is
concretised to call the concrete function |f|, and the resulting trace is
recursively abstracted via $α_\Traces$ afterwards.

Thanks to fixing $α_{\mathcal{S}}$, we can prove the following abstraction theorem,
corresponding to the inference rule at the begin of this subsection:

\begin{theoremrep}[Sound By-need Interpretation]
\label{thm:soundness-by-need-closed}
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let $α_{\mathcal{S}}$ be the abstraction function from \Cref{fig:name-need-gist}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |evalD2 (hat D)| is an abstract interpreter that is sound \wrt $α_{\mathcal{S}}$,
that is,
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
\end{theoremrep}
\begin{proof}
\sg{This proposition is no longer weaker than \Cref{thm:soundness-by-need} and I should merge}
When we inline $α_{\mathcal{S}}$, the goal is simply \Cref{thm:soundness-by-need} for
the special case where environment and heap are empty.
\end{proof}

Let us unpack law $\textsc{Beta-App}$ to see how the abstraction laws in
\Cref{fig:abstraction-laws} are to be understood.
For a preliminary reading, it is best to ignore the syntactic premises above
inference lines.
To prove $\textsc{Beta-App}$, one has to show that |forall f a x. f a ⊑ apply
(fun x f) a| in the abstract domain |hat D|.
This states that summarising |f| through |fun|, then |apply|ing the summary to
|a| must approximate a direct call to |f|;
it amounts to proving correct the summary mechanism.
%\footnote{To illustrate this point: If we were to pick dynamic |Value|s as the
%summary as in the ``collecting semantics'' |D (ByNeed UT)|, we would not need to
%show anything! Then |apply (return (Fun f)) a = f a|.}
In \Cref{sec:problem}, we have proved a substitution \Cref{thm:absence-subst},
which is a syntactic form of this statement.
We will need a similar lemma for usage analysis below, and it is useful to
illustrate the next point, so we prove it here:

\begin{toappendix}
\label{sec:soundness-detail}
\begin{abbreviation}[Field access]
  |(MkUT φ' v')^.φ := φ'|, |(MkUT φ' v')^.v = v'|.
\end{abbreviation}

For concise notation, we define the following abstract substitution operation:

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst-usage}
  We call |abssubst φ x φ' := (ext φ x U0) + (φ !? x) * φ'| the
  \emph{abstract substitution} operation on |Uses|
  and overload this notation for |UT|, so that
  |abssubst (MkUT φ v) x φ' := MkUT (abssubst φ x φ') v|.
\end{definition}

\begin{lemma}
  \label{thm:abs-syn-subst-usage}
  |eval (Lam x e `App` y) ρ = abssubst (eval e (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) x ((ρ ! y) ^. φ)|.
\end{lemma}

The proof below needs to appeal to a couple of congruence lemmas about abstract
substitution, the proofs of which would be tedious and hard to follow, hence
they are omitted.
These are very similar to lemmas we have proven for absence analysis (\cf
\Cref{thm:lambda-commutes-absence}).
\begin{lemma}
\label{thm:push-lambda-usage}
|evalUsg (Lam y (Lam x e `App` z)) ρ = evalUsg (Lam x (Lam y e) `App` z) ρ|.
\end{lemma}
\begin{lemma}
\label{thm:push-app-usage}
|evalUsg (Lam x e `App` y `App` z) ρ = evalUsg (Lam x (e `App` z) `App` y) ρ|.
\end{lemma}
\begin{lemma}
\label{thm:push-select-usage}
\belowdisplayskip0pt\[\begin{array}{ll}
  \\[-2.4em]
  & |evalUsg (Case (Lam x e `App` y) (alts (Lam x er `App` y))) (ext ρ x (ρ ! y))| \\
= & |evalUsg (Lam x (Case e (alts er)) `App` y) ρ|.
\end{array}\]
\end{lemma}
\begin{lemma}
\label{thm:push-let-usage}
|evalUsg (Let z (Lam x e1 `App` y) (Lam x e2 `App` y)) ρ = evalUsg (Lam x (Let z e1 e2) `App` y) ρ|.
\end{lemma}

Now we can finally prove the substitution lemma:
\end{toappendix}

\begin{lemmarep}[Substitution]
\label{thm:usage-subst}
|evalUsg e (ext ρ x (ρ ! y)) ⊑ evalUsg (Lam x e `App` y) ρ|.
\end{lemmarep}
\begin{proof}
We need to assume that |x| is absent in the range of |ρ|.
This is a ``freshness assumption'' relating to the identity of |x| that in
practice is always respected by |evalUsg|.

Now we proceed by induction on |e| and only consider non-|stuck| cases.
\begin{itemize}
  \item \textbf{Case }|Var z|:
    When |x //= z|, we have
    \begin{spec}
        evalUsg (Var z) (ext ρ x (ρ ! y))
    =   {- |x //= z| -}
        ρ ! z
    =   {- Refold |evalUsg| -}
        evalUsg (Var z) (ext ρ x (prx x))
    =   {- |((ρ ! z)^.φ) ! x = U0| -}
        abssubst (evalUsg (Var z) (ext ρ x (prx x))) x ((ρ ! y)^.φ)
    =   {- Definition of |evalUsg| -}
        evalUsg (Lam x (Var z) `App` y) ρ
    \end{spec}
    Otherwise, we have |x = z|.
    \begin{spec}
        evalUsg (Var z) (ext ρ x (ρ ! y))
    =   {- |x = y|, unfold -}
        ρ ! y
    ⊑   {- |v ⊑ (Rep Uω)| -}
        MkUT ((ρ ! y)^.φ) (Rep Uω)
    =   {- Definition of abstract substitution -}
        abssubst (prx x) x ((ρ ! y)^.φ)
    =   {- Refold |evalUsg| -}
        abssubst (evalUsg (Var z) (ext ρ x (prx x))) x ((ρ ! y)^.φ)
    =   {- Definition of |evalUsg| -}
        evalUsg (Lam x (Var z) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |Lam z e|:
    \begin{spec}
        evalUsg (Lam z e) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg| -}
        fun z (\d -> step App2 $ evalUsg e (ext (ext ρ x (ρ ! y)) z d))
    =   {- Rearrange, $|x| \not= |z|$ -}
        fun z (\d -> step App2 $ evalUsg e (ext (ext ρ z d) x (ρ ! y)))
    ⊑   {- Induction hypothesis, $|x| \not= |z|$ -}
        fun z (\d -> step App2 $ evalUsg (Lam x e `App` y) (ext ρ z d))
    =   {- Refold |evalUsg| -}
        evalUsg (Lam z (Lam x e `App` y)) ρ
    =   {- $|x| \not= |z|$, \Cref{thm:push-lambda-usage} -}
        evalUsg (Lam x (Lam z e) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |App e z|:
    Consider first the case |x = z|.
    This case is exemplary of the tedious calculation required to bring
    the substitution outside.
    We abbreviate |prx x := MkUT (singenv x U1) (Rep Uω)|.
    \begin{spec}
        evalUsg (App e z) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg|, |x = z| -}
        apply (evalUsg e (ext ρ x (ρ ! y))) (ρ ! y)
    ⊑   {- Induction hypothesis -}
        apply (evalUsg (Lam x e `App` y) ρ) (ρ ! y)
    =   {- Unfold |apply|, |evalUsg| -}
        let MkUT φ v = abssubst (evalUsg e (ext ρ x (prx x))) x ((ρ ! y)^.φ) in
        case peel v of (u,v2) -> MkUT (φ + u * ((ρ!y)^.φ)) v2
    =   {- Unfold |abssubst| -}
        let MkUT φ v = evalUsg e (ext ρ x (prx x)) in
        case peel v of (u,v2) -> MkUT (ext φ x U0 + (φ !? x) * ((ρ!y)^.φ) + u * ((ρ!y)^.φ)) v2
    =   {- Refold |abssubst| -}
        let MkUT φ v = evalUsg e (ext ρ x (prx x)) in
        case peel v of (u,v2) -> abssubst (MkUT (φ + u * ((prx x)^.φ)) v2) x ((ρ!y)^.φ)
    =   {- Move out |abssubst|, refold |apply| -}
        abssubst (apply (evalUsg e (ext ρ x (prx x))) (prx x)) x ((ρ ! y)^.φ)
    =   {- Refold |evalUsg| -}
        evalUsg (Lam x (App e z) `App` y) ρ
    \end{spec}
    When |x //= z|:
    \begin{spec}
        evalUsg (App e z) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg|, |x //= z| -}
        apply (evalUsg e (ext ρ x (ρ ! y))) (ρ ! z)
    ⊑   {- Induction hypothesis -}
        apply (evalUsg (Lam x e `App` y) ρ) (ρ ! z)
    =   {- Refold |evalUsg| -}
        evalUsg (Lam x e `App` y `App` z) ρ
    =   {- \Cref{thm:push-app-usage} -}
        evalUsg (Lam x (e `App` z) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |ConApp k xs|:
    Let us concentrate on the case of a unary constructor application |xs =
    [z]|; the multi arity case is not much different.
    \begin{spec}
        evalUsg (ConApp k [z]) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg| -}
        foldl apply (MkUT emp (Rep Uω)) [(ext ρ x (ρ ! y)) ! z]
    ⊑   {- Similar to |Var| case -}
        foldl apply (MkUT emp (Rep Uω)) [abssubst ((ext ρ x (prx x)) ! z) x ((ρ ! y)^.φ)]
    =   {- |x| dead in |MkUT emp (Rep Uω)|, push out substitution -}
        abssubst (foldl apply (MkUT emp (Rep Uω)) [(ext ρ x (prx x)) ! z]) x ((ρ ! y)^.φ)
    =   {- Refold |evalUsg| -}
        evalUsg (Lam x (ConApp k [z]) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    We concentrate on the single alternative |er|, single field binder |z| case.
    \begin{spec}
        evalUsg (Case e (singenv k ([z], er))) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg|, |step Case2 = id| -}
        select (evalUsg e (ext ρ x (ρ ! y))) (singenv k (\[d] -> evalUsg er (ext (ext ρ x (ρ ! y)) z d)))
    =   {- Unfold |select| -}
        evalUsg e (ext ρ x (ρ ! y)) >> evalUsg er (ext (ext ρ x (ρ ! y)) z (MkUT emp (Rep Uω)))
    ⊑   {- Induction hypothesis -}
        evalUsg (Lam x e `App` y) ρ >> evalUsg (Lam x er `App` y) (ext ρ z (MkUT emp (Rep Uω)))
    =   {- Refold |select|, |evalUsg| -}
        evalUsg (Case (Lam x e `App` y) alts) (ext ρ x (ρ ! y))
    =   {- Refold |select|, |evalUsg| -}
        evalUsg (Case (Lam x e `App` y) (singenv k ([z], Lam x er `App` y))) (ext ρ x (ρ ! y))
    =   {- \Cref{thm:push-select-usage} -}
        evalUsg (Lam x (Case e (singenv k ([z], er))) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |Let|:
    \begin{spec}
        evalUsg (Let z e1 e2) (ext ρ x (ρ ! y))
    =   {- Unfold |evalUsg| -}
        bind  (\d1 -> evalUsg e1 (ext (ext ρ x (ρ ! y)) z (step (Look z) d1)))
              (\d1 -> step Let1 (evalUsg e2 (ext (ext ρ x (ρ ! y)) z (step (Look z) d1))))
    =   {- Induction hypothesis; note that |x| is absent in |ρ| and thus the fixpoint -}
        bind  (\d1 -> evalUsg (Lam x e1 `App` y) (ext z (step (Look z) d1)))
              (\d1 -> step Let1 (evalUsg (Lam x e2 `App` y) (ext z (step (Look z) d1))))
    =   {- Refold |evalUsg| -}
        evalUsg (Let z (Lam x e1 `App` y) (Lam x e1 `App` y)) ρ
    =   {- \Cref{thm:push-let-usage} -}
        evalUsg (Lam x (Let z e1 e2) `App` y) ρ
    \end{spec}
\end{itemize}
\end{proof}

In order to apply this lemma in step $⊑$ below, it is important that the
premise provides the \emph{strongest characterisation} of |f| in terms of the
syntactic definition |f d := step App2 (evalD UD e (ext ρ x d))|.
Then we get, for |a := ρ ! y :: UD|,
\begin{equation}
  \label{eqn:usage-beta-app}
  \hspace{-1ex}
  |f a = step App2 (evalD UD e (ext ρ x a)) = evalD UD e (ext ρ x a) ⊑ evalD UD (Lam x e `App` y) ρ = apply (fun x f) a|
\end{equation}
Without the syntactic premise of \textsc{Beta-App} to rule out undefinable
entities in |UD -> UD|, the rule cannot be proved for usage analysis; we give a counterexample
in the Appendix (\Cref{ex:syntactic-beta-app}).%
\footnote{Finding domains where all entities $d$ are definable is the classic full
abstraction problem~\citep{Plotkin:77}.}
We discuss concerns of proof modularity in \Cref{sec:mod-sound}.

Rule \textsc{Beta-Sel} states a similar substitution property for data
constructor redexes, which is why it needs to duplicate much of the |cont|
function in \Cref{fig:eval} into its premise.
Rule \textsc{Bind-ByName} expresses that the abstract |bind| implementation must
be sound for by-name evaluation, that is, it must approximate passing the least
fixpoint |lfp| of the |rhs| functional to |body|.
%\footnote{We expect that for sound by-value abstraction it suffices to replace
%\textsc{Bind-ByName} with a law \textsc{Bind-ByValue} mirroring the |bind|
%instance of |ByValue|, but have not attempted a formal proof.}
The remaining rules are congruence rules involving |step| and |stuck| as well as
a monotonicity requirement for all involved operations.
These rules follow the mantra ``evaluation improves approximation''; for example,
rule \textsc{Intro-Stuck} expresses that applying a constructor or scrutinising
a function evaluates to (and thus approximates) a stuck term, and
\textsc{Unwind-Stuck} expresses that stuckness unwinds through |apply| and
|select| stack frames.
In the Appendix, we show a result similar to \Cref{thm:soundness-by-need-closed}
for by-name evaluation which does not require the by-need specific rules
\textsc{Step-Inc} and \textsc{Update}.

Note that none of the laws mention the concrete semantics or the abstraction
function $α_{\mathcal{S}}$.
This is how fixing the concrete semantics and $α_{\mathcal{S}}$ pays off; the usual
abstraction laws such as
$α(|apply d a|) ⊑ |hat apply ({-" α "-} (d)) ({-" α "-} (a))|$ further
decompose for $α = α_{\mathcal{S}}$ into \textsc{Beta-App}.
We think this is a nice advantage to our approach, because the author of
the analysis does not need to reason about the concrete semantics in order to
soundly approximate a semantic trace property expressed via |Trace| instance!

\subsection{A Much Simpler Proof That Usage Analysis Infers Absence}

Equipped with the generic soundness \Cref{thm:soundness-by-need-closed},
we will prove in this subsection that usage analysis from \Cref{sec:abstraction}
infers absence in the same sense as absence analysis from \Cref{sec:problem}.
The reason we do so is to evaluate the proof complexity of our approach against
the preservation-style proof framework in \Cref{sec:problem}.

Specifically, \Cref{thm:soundness-by-need-closed} makes it very simple to relate
by-need semantics with usage analysis, taking the place of the absence
analysis-specific preservation \Cref{thm:preserve-absent}:

\begin{lemmarep}[|evalUsg1| abstracts |evalNeed1|]
\label{thm:usage-abstracts-need-closed}
Let |e| be an expression and $α_{\mathcal{S}}$ the abstraction function from
\Cref{fig:name-need-gist}.
Then $α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalUsg1 e|$.
\end{lemmarep}
\begin{proof}
By \Cref{thm:soundness-by-need-closed}, it suffices to show the abstraction laws
in \Cref{fig:abstraction-laws}.
\begin{itemize}
  \item \textsc{Mono}:
    Always immediate, since |⊔| and |+| are the only functions matching on |U|,
    and these are monotonic.
  \item \textsc{Unwind-Stuck}, \textsc{Intro-Stuck}:
    Trivial, since |stuck = bottom|.
  \item \textsc{Step-App}, \textsc{Step-Sel}, \textsc{Step-Inc}, \textsc{Update}:
    Follows by unfolding |step|, |apply|, |select| and associativity of |+|.
  \item \textsc{Beta-App}:
    Follows from \Cref{thm:usage-subst}; see \Cref{eqn:usage-beta-app}.
  \item \textsc{Beta-Sel}:
    Follows by unfolding |select| and |con| and applying a lemma very similar to
    \Cref{thm:usage-subst} multiple times.
  \item \textsc{Bind-ByName}:
    |kleeneFix| approximates the least fixpoint |lfp| since the iteratee |rhs|
    is monotone.
    We have said elsewhere that we omit a widening operator for |rhs| that
    guarantees that |kleeneFix| terminates.
\end{itemize}
\end{proof}

The next step is to leave behind the definition of absence in terms of the LK
machine in favor of one using |evalNeed2|.
That is a welcome simplification because it leaves us with a single semantic
artefact --- the denotational interpreter --- instead of an operational
semantics and a separate static analysis as in \Cref{sec:problem}.
Thanks to adequacy (\Cref{thm:need-adequate-strong}), this new notion is not a
redefinition but provably equivalent to \Cref{defn:absence}:
\begin{lemmarep}[Denotational absence]
  \label{thm:absence-denotational}
  Variable |x| is used in |e| if and only if there exists a by-need evaluation context
  |ectxt| and expression |e'| such that the trace
  |evalNeed (fillC ectxt (Let x e' e)) emp emp| contains a |Look x| event.
  Otherwise, |x| is absent in |e|.
\end{lemmarep}
\begin{proof}
Since |x| is used in |e|, there exists a trace
\[
  (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep^* ... \smallstep[\LookupT(\px)] ...
\]

We proceed as follows:
\begin{DispWithArrows}[fleqn,mathindent=0em]
                          & (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep^* ... \smallstep[\LookupT(\px)] ...
                          \label{arrow:usg-context}
                          \Arrow{$\pE \triangleq \mathit{trans}(\hole,ρ,μ,κ)$} \\
  {}\Longleftrightarrow{} & \init(\pE[\Let{\px}{\pe'}{\pe}]) \smallstep^* ... \smallstep[\LookupT(\px)] ...
                          \Arrow{Apply $α_{\STraces}$ (\Cref{fig:eval-correctness})} \\
  {}\Longleftrightarrow{} & α_{\STraces}(\init(\pE[\Let{\px}{\pe'}{\pe}]) \smallstep^*, []) = | ... Step (Look x) ...|
                          \Arrow{\Cref{thm:need-adequate-strong}} \\
  {}\Longleftrightarrow{} & |evalNeed (fillC ectxt (Let x e' e)) emp emp| = |... Step (Look x) ...|
\end{DispWithArrows}
Note that the trace we start with is not necessarily an maximal trace,
so step \labelcref{arrow:usg-context} finds a prefix that makes the trace maximal.
We do so by reconstructing the syntactic \emph{evaluation context} $\pE$
with $\mathit{trans}$ (\cf \Cref{thm:translation}) such that
\[
  \init(\pE[\Let{\px}{\pe'}{\pe}]) \smallstep^* (\Let{\px}{\pe'}{\pe},ρ,μ,κ)
\]
Then the trace above is contained in the maximal trace starting in
$\init(\pE[\Let{\px}{\pe'}{\pe}])$ and it contains at least one $\LookupT(\px)$
transition.

The next two steps apply adequacy of |evalNeed| to the trace, making the shift
from LK trace to denotational interpreter.
\end{proof}

We define the by-need evaluation contexts for our language in the Appendix.
Thus insulated from the LK machine, we may restate and prove
\Cref{thm:absence-correct} for usage analysis.

\begin{theoremrep}[|evalUsg| infers absence]
  \label{thm:usage-absence}
  Let |ρe := singenvmany y (MkUT (singenv y U1) (Rep Uω))| be the initial
  environment with an entry for every free variable |y| of an expression |e|.
  If |evalUsg e ρe = MkUT φ v| and |φ !? x = U0|,
  then |x| is absent in |e|.
\end{theoremrep}
\begin{proofsketch}
If |x| is used in |e|, there is a trace |evalNeed (fillC ectxt (Let x e' e)) emp emp| containing a |Look x| event.
The abstraction function $α_{\mathcal{S}}$ induced by |UD| aggregates lookups in the
trace into a |φ' :: Uses|, \eg
  $β_\Traces(\LookupT(i) \smallstep \LookupT(x) \smallstep \LookupT(i) \smallstep \langle ... \rangle)
    = |MkUT [ i {-" ↦ "-} Uω, x {-" ↦ "-} U1 ] (...)|$.
Clearly, it is |φ' !? x ⊒ U1|, because there is at least one |Look x|.
\Cref{thm:usage-abstracts-need-closed} and a context invariance
\Cref{thm:usage-bound-vars-context} prove that the computed |φ|
approximates |φ'|, so |φ !? x ⊒ φ' !? x ⊒ U1 //= U0|.
\end{proofsketch}
\begin{proof}
We show the contraposition, that is,
if |x| is used in |e|, then |φ !? x //= U0|.

By \Cref{thm:absence-denotational}, there exists |ectxt|, |e'| such that
\[
  |evalNeed (fillC ectxt (Let x e' e)) emp emp = ... ^^ Step (Look x) ^^ ...| .
\]

This is the big picture of how we prove |φ !? x //= U0| from this fact:
\begin{DispWithArrows}[fleqn,mathindent=0em]
                      & |evalNeed (fillC ectxt (Let x e' e)) emp emp| = |... Step (Look x) ...|
                      \label{arrow:usg-instr}
                      \Arrow{Usage instrumentation} \\
  {}\Longrightarrow{} & |(α (set (evalNeed (fillC ectxt (Let x e' e)) emp emp)))^.φ| ⊒ [|x| ↦ |U1|]
                      \label{arrow:usg-abs}
                      \Arrow{\Cref{thm:usage-abstracts-need-closed}} \\
  {}\Longrightarrow{} & |(evalUsg (fillC ectxt (Let x e' e)) emp)^.φ| ⊒ [|x| ↦ |U1|]
                      \label{arrow:usg-anal-context}
                      \Arrow{\Cref{thm:usage-bound-vars-context}} \\
  {}\Longrightarrow{} & |Uω * (evalUsg e ρe)^.φ| = |Uω * φ| ⊒ [|x| ↦ |U1|]
                      \Arrow{|Uω * U0 = U0 ⊏ U1|} \\
  {}\Longrightarrow{} & |φ !? x //= U0|
\end{DispWithArrows}

Step \labelcref{arrow:usg-instr} instruments the trace by applying the usage
abstraction function |α :<->: _ := nameNeed|.
This function will replace every |Step| constructor
with the |step| implementation of |UT|;
The |Look x| event on the right-hand side implies that its image under |α| is
at least $[|x| ↦ |U1|]$.

Step \labelcref{arrow:usg-abs} applies the central soundness
\Cref{thm:usage-abstracts-need-closed} that is the main topic of this section,
abstracting the dynamic trace property in terms of the static semantics.

Finally, step \labelcref{arrow:usg-anal-context} applies
\Cref{thm:usage-bound-vars-context}, which proves that absence information
doesn't change when an expression is put in an arbitrary evaluation context.
The final step is just algebra.
\end{proof}

\subsection{Evaluation}

Let us compare to the preservation-style proof framework in \Cref{sec:problem}.
\begin{itemize}
  \item
    Where there were multiple separate \emph{semantic artefacts} such as a separate
    small-step semantics and an extension of the absence analysis function to
    machine configurations $σ$ in order to state preservation
    (\Cref{thm:preserve-absent}), our proof only has a single semantic artefact
    that needs to be defined and understood: the denotational interpreter,
    albeit with different instantiations.
  \item
%    The substitution lemma is common to both approaches and indispensable in
%    proving the summary mechanism correct.
    What is more important is that a simple proof for
    \Cref{thm:usage-abstracts-need-closed} in half a page (we encourage the
    reader to take a look) replaces a tedious, error-prone and incomplete
    \emph{proof for the preservation lemma}.
    Of course, we lean on \Cref{thm:soundness-by-need-closed} to prove what
    amounts to a preservation lemma; the difference is that our proof properly
    accounts for heap update and can be shared with other analyses that are
    sound \wrt by-name and by-need.
    Thus, we achieve our goal of proving semantic distractions ``once and for all''.
\end{itemize}

\begin{toappendix}
In the proof for \Cref{thm:usage-absence} we exploit that usage analysis is
somewhat invariant under wrapping of \emph{by-need evaluation contexts}, roughly
|Uω * evalUsg e ρe = evalUsg (fillC ectxt e) emp|. To prove that, we first
need to define what the by-need evaluation contexts of our language are.

\citet[Lemma 4.1]{MoranSands:99} describe a principled way to derive the
call-by-need evaluation contexts $\pE$ from machine contexts $(\hole,μ,κ)$ of
the Sestoft Mark I machine; a variant of \Cref{fig:lk-semantics} that uses
syntactic substitution of variables instead of delayed substitution and
addresses, so $μ ∈ \Var \pfun \Exp$ and no closures are needed.

We follow their approach, but inline applicative contexts,%
\footnote{The result is that of \citet[Figure 3]{Ariola:95} in A-normal form and
extended with data types.}
thus defining the by-need evaluation contexts with hole $\hole$ for our language as
\[\begin{array}{lcl}
  \pE ∈ \EContexts & ::= & \hole \mid \pE~\px \mid \Case{\pE}{\Sel} \mid \Let{\px}{\pe}{\pE} \mid \Let{\px}{\pE}{\pE[\px]} \\
\end{array}\]
The correspondence to Mark I machine contexts $(\hole,μ,κ)$ is encoded by the
following translation function $\mathit{trans}$ that translates from mark I
machine contexts  $(\hole,μ,κ)$ to evaluation contexts $\pE$.
\[\begin{array}{lcl}
  \mathit{trans} & : & \EContexts \times \Heaps \times \Continuations \to \EContexts \\
  \mathit{trans}(\pE,[\many{\px ↦ \pe}],κ) & = & \Letmany{\px}{\pe}{\mathit{trans}(\pE,[],κ)} \\
  \mathit{trans}(\pE,[],\ApplyF(\px) \pushF κ) & = & \mathit{trans}(\pE~\px,[],κ) \\
  \mathit{trans}(\pE,[],\SelF(\Sel) \pushF κ) & = & \mathit{trans}(\Case{\pE}{\Sel},[],κ) \\
  \mathit{trans}(\pE,[],\UpdateF(\px) \pushF κ) & = & \Let{\px}{\pE}{\mathit{trans}(\hole, [], κ)[\px]} \\
  \mathit{trans}(\pE,[],\StopF) & = & \pE \\
\end{array}\]
Certainly the most interesting case is that of $\UpdateF$ frames, encoding
by-need memoisation.
This translation function has the following property:
\begin{lemma}[Translation, without proof]
  \label{thm:translation}
  $\init(\mathit{trans}(\hole,μ,κ)[\pe]) \smallstep^* (\pe,μ,κ)$,
  and all transitions in this trace are search transitions ($\AppIT$, $\CaseIT$,
  $\LetIT$, $\LookupT$).
\end{lemma}
In other words: every machine configuration $σ$ corresponds to an evaluation
context $\pE$ and a focus expression $\pe$ such that there exists a trace
$\init(\pE[\pe]) \smallstep^* σ$ consisting purely of search transitions,
which is equivalent to all states in the trace except possibly the last being
evaluation states.

We encode evaluation contexts in Haskell as follows, overloading hole filling notation |fillC|:
\begin{spec}
data ECtxt  =  Hole | Apply ECtxt Name | Select ECtxt Alts
            |  ExtendHeap Name Expr ECtxt | UpdateHeap Name ECtxt Expr
fillC :: ECtxt -> Expr -> Expr
fillC Hole e                      = e
fillC (Apply ectxt x) e           = App (fillC ectxt e) x
fillC (Select ectxt alts) e       = Case (fillC ectxt e) alts
fillC (ExtendHeap x e1 ectxt) e2  = Let x e1 (fillC ectxt e2)
fillC (UpdateHeap x ectxt e1) e2  = Let x (fillC ectxt e1) e2
\end{spec}

\begin{lemma}[Used variables are free]
  \label{thm:used-free}
  If |x| does not occur in |e| and in |ρ| (that is, |forall y. (ρ ! y)^.φ !?
  x = U0|), then |(evalUsg e ρ)^.φ !? x = U0|.
\end{lemma}
\begin{proof}
  By induction on |e|.
\end{proof}

\begin{lemma}[Context closure]
\label{thm:usage-bound-vars-context}
Let |e| be an expression and |ectxt| be a by-need evaluation context in which
|x| does not occur.
Then |(evalUsg (fillC ectxt e) ρE)^.φ ?! x ⊑ Uω * ((evalUsg e ρe)^.φ !? x)|,
where |ρE| and |ρe| are the initial environments that map free variables |z|
to their proxy |MkUT (singenv z U1) (Rep Uω)|.
\end{lemma}
\begin{proof}
We will sometimes need that if |y| does not occur free in |e1|, we have
By induction on the size of |ectxt| and cases on |ectxt|:
\begin{itemize}
  \item \textbf{Case }|Hole|:
    \begin{spec}
        (evalUsg (fillC Hole e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg e ρE)^.φ !? x
    ⊑   {- |ρe = ρE| -}
        Uω * (evalUsg e ρE)^.φ !? x

    \end{spec}
    By reflexivity.
  \item \textbf{Case }|Apply ectxt y|:
    Since |y| occurs in |ectxt|, it must be different to |x|.
    \begin{spec}
        (evalUsg (fillC (Apply ectxt y) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (App (fillC ectxt e) y) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (apply (evalUsg (fillC ectxt e) ρE) (ρE !? y))^.φ !? x
    =   {- Definition of |apply| -}
        let MkUT φ v = evalUsg (fillC ectxt e) ρE in
        case peel v of (u,v2) -> ((MkUT (φ + u*((ρE!?y)^.φ)) v2)^.φ !? x)
    =   {- Unfold |(MkUT φ v)^.φ = φ|, |x| absent in |ρE !? y| -}
        let MkUT φ v = evalUsg (fillC ectxt e) ρE in
        case peel v of (u,v2) -> φ !? x
    =   {- Refold |(MkUT φ v)^.φ = φ| -}
        (evalUsg (fillC ectxt e) ρE)^.φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|Select ectxt alts|:
    Since |x| does not occur in |alts|, it is absent in |alts| as well
    by \Cref{thm:used-free}.
    (Recall that |select| analyses |alts| with |MkUT emp (Rep Uω)| as
    field proxies.)
    \begin{spec}
        (evalUsg (fillC (Select ectxt alts) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Case (fillC ectxt e) alts) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (select (evalUsg (fillC ectxt e) ρE) (cont << alts))^.φ !? x
    =   {- Definition of |select| -}
        (evalUsg (fillC ectxt e) ρE >> lub (... alts ...))^.φ !? x
    =   {- |x| absent in |lub (... alts ...)| -}
        (evalUsg (fillC ectxt e) ρE)^.φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|ExtendHeap y e1 ectxt|:
    Since |x| does not occur in |e1|, and the initial environment
    is absent in |x| as well, we have |(evalUsg e1 ρE)^.φ !? x = U0| by
    \Cref{thm:used-free}.
    \begin{spec}
        (evalUsg (fillC (ExtendHeap y e1 ectxt) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Let y e1 (fillC ectxt e)) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (evalUsg (fillC ectxt e) (ext ρE y (step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))))))^.φ !? x
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst} -}
        (abssubst (evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω)))) y (
          step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))))) ^.φ !? x
    =   {- Unfold |abssubst|, |(MkUT φ v)^.φ = φ| -}
        let MkUT φ  _ = evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))) in
        (ext φ y U0 + (φ !? y)*φ2) !? x
    =   {- |x| absent in |φ2|, see above -}
        let MkUT φ  _ = evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|UpdateHeap y ectxt e1|:
    Since |x| does not occur in |e1|, and the initial environment
    is absent in |x| as well, we have
    |(evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω))))^.φ !? x = U0| by
    \Cref{thm:used-free}.
    \begin{spec}
        (evalUsg (fillC (UpdateHeap y ectxt e1) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Let y (fillC ectxt e) e1) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (evalUsg e1 (ext ρE y (step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))))^.φ !? x
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst} -}
        (abssubst (evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω)))) y (
          step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))) ^.φ !? x
    =   {- Unfold |abssubst|, |(MkUT φ v)^.φ = φ| -}
        let MkUT φ  _ = evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))) in
        (ext φ y U0 + (φ !? y)*φ2) !? x
    =   {- |φ !? y ⊑ Uω|, |x| absent in |φ|, see above -}
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))) in
        Uω * φ2 !? x
    =   {- Refold |(MkUT φ v)^.φ| -}
        Uω * (step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))^.φ !? x
    =   {- |x //= y| -}
        Uω * (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y d)))^.φ !? x
    =   {- Argument below -}
        Uω * (evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))))^.φ !? x
    ⊑   {- Induction hypothesis, |Uω * Uω = Uω| -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
    The rationale for removing the |kleeneFix| is that under the assumption that
    |x| is absent in |d| (such as is the case for |d := MkUT (singenv y U1)
    (Rep Uω)|), then it is also absent in |fillC ectxt e (ext ρE y d)| per
    \Cref{thm:used-free}.
    Otherwise, we go to |Uω| anyway.

    |UpdateHeap| is why it is necessary to multiply with |Uω| above;
    in the context $\Let{x}{\hole}{x~x}$, a variable $y$ put in the hole
    would really be evaluated twice under call-by-name (where
    $\Let{x}{\hole}{x~x}$ is \emph{not} an evaluation context).

    This unfortunately means that the used-once results do not generalise
    to arbitrary by-need evaluation contexts and it would be unsound
    to elide update frames for $y$ based on the inferred use of $y$ in
    $\Let{y}{...}{\pe}$; for $\pe \triangleq y$ we would infer that $y$
    is used at most once, but that is wrong in context $\Let{x}{\hole}{x~x}$.
\end{itemize}
\end{proof}
\end{toappendix}
