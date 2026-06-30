%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Soundness where

import Prelude hiding ((+), (*))
import Data.Set (Set)
import qualified Data.Set as Set
import Interpreter

instance Eq DName where
  (==) = undefined
instance Ord DName where
  compare = undefined
data Pow a = P (Set a) deriving (Eq, Ord)
powMap :: (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ undefined $ map f $ Set.toList s
set = P . Set.singleton
\end{code}
%endif

\section{Generic Abstract By-Name and By-Need Interpretation}
\label{sec:soundness}

\begin{toappendix}
\label{sec:soundness-detail}

So far, we have seen how to \emph{use} the abstraction
\Cref{thm:abstract-by-need}, but not proved it.
Proving this theorem correct is the goal of this section,
and we approach the problem from the bottom up.

We will discuss why it is safe to approximate guarded fixpoints with
least fixpoints and why the definition of the Galois connection in
\Cref{fig:abstract-name-need} as a fold over the trace is well-defined
in \Cref{sec:safety-extension}.
Then we will go on to prove sound abstract by-name interpretation in
\Cref{sec:by-name-soundness}, and finally sound abstract by-need interpretation
in \Cref{sec:by-need-soundness}.

%include soundness-appendix.lhs
\end{toappendix}

\begin{figure}
\[\ruleform{\begin{array}{c}
  α_{\mathcal{S}} : (|(Name :-> DNeed) -> DNeed|) \to (|(Name :-> hat D) -> hat D|)
  \\
  α_{\Environments} : \pow{|Heap| \times (|Name :-> DNeed|)} \rightleftarrows (|Name :-> hat D|) : γ_{\Environments}
  \\
  α_{\Domain{}} : |Heap| \to (\pow{|DNeed|} \rightleftarrows |hat D|) : γ_{\Domain{}}
  \\
  α_\Traces : \pow{|T (ValueNeed, Heap)|} \rightleftarrows |hat D| : γ_\Traces
  \qquad
  β_\Traces : |T (ValueNeed, Heap)| \to |hat D|
  \qquad
\end{array}}\]
\belowdisplayskip=0pt
\arraycolsep=2pt
\[\begin{array}{lcl}
α_{\mathcal{S}}(S)(\widehat{ρ}) & = & α_\Traces(\{\  S(ρ)(μ) \mid (μ,ρ) ∈ γ_{\Environments}(\widehat{ρ}) \ \}) \\
α_{\Environments}(E)(x) & = & α_\Traces(\{\  ρ(x)(μ) \mid (μ,ρ) ∈ E \ \}) \\
α_{\Domain{}}(μ)(D) & = & α_\Traces(\{\  d(μ) \mid d ∈ D \ \}) \\
α_\Traces(T) & = & \Lub \{\ β_\Traces(τ) \mid τ ∈ T \ \} \\
\\[-0.75em]
β_\Traces(|τ|) & = & \begin{cases}
  |step e (βT ^ (τ'))| & \text{if |τ = Step e τ'|} \\
  |stuck|                         & \text{if |τ = Ret (Stuck, μ)|} \\
  |fun (αD^(μ) . powMap f . γD^(μ))| & \text{if |τ = Ret (Fun f, μ)|} \\
  |con k (map (αD^(μ) . set) ds)| & \text{if |τ = Ret (Con k ds, μ)|} \\
  \end{cases} \\
\end{array}\]
\caption{Galois connection $α_{\mathcal{S}}$ for by-need abstraction derived from |Trace|, |Domain| and |Lat| instances on |hat D|}
\label{fig:abstract-name-need}
\end{figure}

Recall that usage analysis is supposed to infer the semantic property of
absence (\Cref{defn:absence}) in order to inform dead code elimination.
In this section, we prove that usage analysis indeed infers absence.
For that, it is necessary to relate the analysis result to a property of the
program semantics.
The resulting approximation relation is well understood via abstract
interpretation~\citep{Cousot:77} and we capture it in a generalised statement of
the form
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
This statement can be read as follows:
For an expression |e|, the \emph{static analysis} |evalD2 (hat D) e|
on the right-hand side \emph{overapproximates} ($⊒$) a property of the by-need
\emph{semantics} |evalNeed1 e| on the left-hand side.
The abstraction function $α_{\mathcal{S}}$, given in
\Cref{fig:abstract-name-need}, defines the semantic property of interest in
terms of the abstract domain |hat D| of |evalD (hat D) e ρ|, which is
short for |eval e ρ :: hat D|.
That is: the type class instances on |hat D| determine $α_{\mathcal{S}}$, and
hence the semantic property that is soundly abstracted by |evalD (hat D) e ρ|.%
\footnote{Again, note that |evalD (hat D) e ρ| is a decidable algorithm, in
contrast to $α_{\mathcal{S}}(|evalNeed1 e|)$.
To give just one example, computing the latter diverges whenever the evaluation
of |e| diverges.}

We will instantiate the theorem at |UD| in order to prove that usage analysis
|evalUsg e ρ = evalD UD e ρ| infers absence.
The complicated preservation reasoning is reusably contained in the abstract
interpretation theorem, so the analysis-specific part of the proof stays small.

\begin{figure}
  \belowdisplayskip=0pt
  \[\begin{array}{cc}
    \multicolumn{2}{c}{\inferrule[\textsc{Mono}]
      {}
      {\text{|step|, |stuck|, |fun|, |apply|, |con|, |select|, |bind| monotone}}} \\
    \\[-0.5em]
    \inferrule[\textsc{Step-App}]{}{%
      |step ev (apply d a) ⊑ apply (step ev d) a|}
    &
    \inferrule[\textsc{Step-Sel}]{}{%
      |step ev (select d alts) ⊑ select (step ev d) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Stuck-App}]
      {|d ∈ set (stuck, con k ds)|}
      {|stuck ⊑ apply d a|}
    &
    \inferrule[\textsc{Stuck-Sel}]
      {|d ∈ set (stuck, fun x f) ∪ set (con k ds || k {-"\not"-}∈ dom alts)|}
      {|stuck ⊑ select d alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Beta-App}]
      {|f| \text{ polymorphic} \\ |x|\text{ fresh}}
      {|f a ⊑ apply (fun x f) a|}
    &
    \inferrule[\textsc{Beta-Sel}]
      {|alts| \text{ polymorphic} \\ |k ∈ dom alts|}
      {|(alts ! k) ds ⊑ select (con k ds) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{ByName-Bind}]
      {|rhs, body|\text{ polymorphic}}
      {|body (lfp rhs) ⊑ bind rhs body|}
    &
    \fcolorbox{lightgray}{white}{$\begin{array}{c}
      \inferrule[\textsc{Step-Inc}]{}{|d ⊑ step ev d|}
      \qquad
      \inferrule[\textsc{Update}]{}{|step Upd d = d|}
    \end{array}$}
  \end{array}\]
  \caption{By-name and \fcolorbox{lightgray}{white}{by-need} abstraction laws for type class instances of abstract domain |hat D|}
  \label{fig:abstraction-laws}
\end{figure}

\subsection{A Reusable Abstract By-Need Interpretation Theorem}

In this subsection, we explain and prove \Cref{thm:abstract-by-need} for
abstract by-need interpretation, which we will apply to prove usage analysis
sound in \Cref{sec:usage-sound}.
The theorem corresponds to the following derived inference rule, referring to
the \emph{abstraction laws} in \Cref{fig:abstraction-laws} by name:
\[\begin{array}{c}
  \inferrule{%
    \textsc{Mono} \\ \textsc{Step-App} \\ \textsc{Step-Sel} \\ \textsc{Stuck-App} \\
    \textsc{Stuck-Sel} \\ \textsc{Beta-App} \\ \textsc{Beta-Sel} \\ \textsc{ByName-Bind} \\
    \textsc{Step-Inc} \\ \textsc{Update}
  }{%
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|
  }
\end{array}\]
\noindent
In other words: prove the abstraction laws for an abstract domain |hat D| of
your choosing (such as |UD|) and we give you a proof of sound abstract by-need
interpretation for the static analysis |evalD2 (hat D)|!

Note that \emph{we} get to determine the abstraction function $α_{\mathcal{S}}$ based
on the |Trace|, |Domain| and |Lat| instance on \emph{your} |hat D|.
\Cref{fig:abstract-name-need} defines how $α_{\mathcal{S}}$ is thus derived.

Let us calculate |αS| for the closed example expression
$\pe \triangleq \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i}$:
\begin{align}
    & |αS^(evalNeed1 (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})))^(emp)| \notag \\
={} & |βT^(evalNeed (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})) emp emp)| \label{eqn:abs-ex1} \\
={} & |βT|(\perform{evalNeed (read "let i = (λy.λx.x) i in i") emp emp :: T (ValueNeed, Heap)}) \label{eqn:abs-ex2} \\
={} & \textstyle|step Let1 (step (Look "i") (... (fun (\(hat d) -> Lub (βT^({-" \AppET \smallstep \varid{d}([0\!\!↦\!\!\wild]) "-}space) || d ∈ γD^({-"[0\!\!↦\!\!\wild]"-}space)^((hat d)))))))| \notag \\
⊑{} & \textstyle|step Let1 (step (Look "i") (... (fun (\(hat d) -> step App2 (hat d)))))| \label{eqn:abs-ex3} \\
={} & |MkUT (singenv "i" U1) (UCons U1 (Rep Uω)) :: UD| \label{eqn:abs-ex4} \\
={} & |evalUsg (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})) emp| \notag
\end{align}
\noindent
In (\ref{eqn:abs-ex1}), $α_{\mathcal{S}}(|evalNeed1 e|)(|emp|)$ simplifies to |βT^(evalNeed e emp
emp)|.
Function |βT| then folds the by-need trace (\ref{eqn:abs-ex2}) into an abstract
domain element in |hat D|.
It does so by eliminating every |Step ev| in the trace with a call to
|step ev|, and every concrete |Value| at the end of the trace with a
call to the corresponding |Domain| method, following the structure of
types as in \citet{Backhouse:04}.
Since |hat D| has a |Lat| instance, |βT| is a \emph{representation
function}~\citep[Section 4.3]{Nielson:99}, giving rise to Galois connections
$α_\Traces \rightleftarrows γ_\Traces$ and
$α_\Domain(μ) \rightleftarrows γ_\Domain(μ)$.
This implies that $α_\Domain(μ) \circ γ_\Domain(μ) ⊑ \mathit{id}$,
justifying the approximation step $(⊑)$ in (\ref{eqn:abs-ex3}).
For the concrete example, we instantiate |hat D| to |UD| in step
(\ref{eqn:abs-ex4}) to assert that the resulting usage type indeed
coincides with the result of |evalUsg1|, as predicted by the abstract
interpretation theorem.

The abstraction function |αD| for by-need elements |d| is a bit unusual because
it is \emph{indexed} by a heap to give meaning to addresses referenced by |d|.
Our framework is carefully set up in a way that |αD^(μ)| is preserved when |μ|
is modified by memoisation ``in the future'', reminiscent of
\citeauthor{Kripke:63}'s possible worlds.
For similar reasons, the abstraction function for environments pairs up
definable by-need environments |ρ|, the entries of which are of the form (|step
Look y) (fetch a)|, with heaps |μ|.

Thanks to fixing $α_{\mathcal{S}}$, we can prove the following abstraction theorem,
corresponding to the inference rule at the begin of this subsection:

\begin{theoremrep}[Abstract By-need Interpretation]
\label{thm:abstract-by-need}
Let |e| be an expression, |hat D| a domain with instances for |Trace|, |Domain| and
|Lat|, and let $α_{\mathcal{S}}$ be the abstraction function from \Cref{fig:abstract-name-need}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |evalD2 (hat D)| is an abstract interpreter that is sound \wrt $α_{\mathcal{S}}$,
that is,
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
\end{theoremrep}
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
    Otherwise,
    \[
      |βT^(evalNeed (Var x) ρ μ) = βT^((ρ ! x) μ) = evalD (hat D) (Var x) (βD^(μ) << ρ)|.
    \]

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
    Very similar to the |apply| case in \Cref{thm:abstract-by-name}.
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
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat apply) (hat stuck) (hat a)| by assumption \textsc{Stuck-App}.
          \item \textbf{Case |v = Con k ds|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat apply) ((hat con) k (hat ds)) (hat a)| by assumption \textsc{Stuck-App}, for the suitable |hat ds|.
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
    Very similar to the |select| case in \Cref{thm:abstract-by-name}.

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
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) (hat stuck) (hat alts)| by assumption \textsc{Stuck-Sel}.
          \item \textbf{Case |v = Fun f|}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) ((hat fun) (hat f)) (hat alts)| by assumption \textsc{Stuck-Sel}, for the suitable |hat f|.
          \item \textbf{Case |v = Con k ds|, $|k| \not∈ |dom alts|$}:
            Then |βT^(stuck μ2) = hat stuck ⊑ (hat select) ((hat con) k (hat ds)) (hat alts)| by assumption \textsc{Stuck-Sel}, for the suitable |hat ds|.
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
        βT^(step Let1 (bind  (\d1 -> evalNeed2 e1 ρ1) (\d1 -> evalNeed2 e2 ρ1)) μ)
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
    ⊑   {- \textsc{Mono} and assumption \textsc{ByName-Bind}, with |hat ρ = βD^(μ) << ρ| -}
        step Let1 (bind  (\d1 -> eval e1 (ext (βD^(μ) << ρ) x (step (Look x) d1)))
                         (\d1 -> eval e2 (ext (βD^(μ) << ρ) x (step (Look x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βD^(μ) << ρ)| -}
        eval (Let x e1 e2) (βD^(μ) << ρ)
    \end{spec}
\end{itemize}
\end{proof}

Let us unpack law $\textsc{Beta-App}$ to see how the abstraction laws in
\Cref{fig:abstraction-laws} are to be understood.
To prove $\textsc{Beta-App}$, one has to show that
|forall f a x. f a ⊑ apply (fun x f) a| in the abstract domain |hat D|.
This states that summarising |f| through |fun|, then |apply|ing the summary to
|a| must approximate a direct call to |f|;
it amounts to proving correct the summary mechanism.
The ``$|f|\text{ polymorphic}$'' premise asserts that |f| is definable at
polymorphic type |forall d. (Trace d, Domain d) => d -> d|, which is
important to prove \textsc{Beta-App} (in \Cref{sec:mod-subst}).

Law \textsc{Beta-Sel} states a similar property for data constructor redexes.
Law \textsc{ByName-Bind} expresses that the abstract |bind| implementation must
be sound for by-name evaluation, that is, it must approximate passing the least
fixpoint |lfp| of the |rhs| functional to |body|.
The remaining laws are congruence rules involving |step| and |stuck| as well as
a monotonicity requirement for all involved operations.
These laws follow the mantra ``evaluation improves approximation''; for
example, law \textsc{Stuck-App} expresses that applying a stuck term
or constructor evaluates to (and thus approximates) a stuck term, and
\textsc{Stuck-Sel} expresses the same for |select| stack frames.
In the Appendix, we show a result similar to \Cref{thm:abstract-by-need}
for by-name evaluation which does not require the by-need specific laws
\textsc{Step-Inc} and \textsc{Update}.

Note that none of the laws mention the concrete semantics or the abstraction
function $α_{\mathcal{S}}$.
This is how fixing the concrete semantics and $α_{\mathcal{S}}$ pays off; the usual
abstraction laws such as
|αD^(μ)^(apply d a) ⊑ hat apply (αD^(μ)^(d)) (αD^(μ)^(a))| further
decompose into \textsc{Beta-App}.
We think this is a nice advantage to our approach, because the author of
the analysis does not need to reason about by-need heaps in order to soundly
approximate a semantic trace property expressed via |Trace| instance!

\begin{toappendix}
\subsection{Parametricity and Relationship to Kripke-style Logical Relations}

We remarked right at the begin of the previous subsection that the Galois
connection in \Cref{fig:abstract-name-need} is really a family of definitions
indexed by a heap |μ|.
It is not possible to regard the ``abstraction of a |d|'' in isolation;
rather, \Cref{thm:heap-progress-mono} expresses that once an ``abstraction of a |d|''
holds for a particular heap |μ1|, this abstraction will hold for any heap |μ2|
that the semantics may progress to.

Unfortunately, this indexing also means that we cannot apply parametricity
to prove the sound abstraction \Cref{thm:abstract-by-need}, as we did for
by-name abstraction.
Such a proof would be bound to fail whenever the heap is extended (in |bind|),
because then the index of the soundness relation must change as well.
Concretely, we would need roughly the following free theorem
\[
  |(bind, bind) ∈ Later (Later (Rel(ext μ a d)) -> Rel(ext μ a d)) -> (Later (Rel(ext μ a d)) -> Rel(ext μ a d)) -> Rel(μ)|
\]
for the soundness relation of \Cref{thm:abstract-by-need}
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
of \Cref{thm:abstract-by-need} is reminiscent of a \emph{Kripke logical
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
\end{toappendix}

\subsection{A Modular Proof for \textsc{Beta-App}}
\label{sec:mod-subst}

\begin{toappendix}
\subsection{Usage Analysis Proofs}

Here we give the usage analysis proofs for the main body, often deferring to
\Cref{sec:by-need-soundness}.
\end{toappendix}

In order to instantiate \Cref{thm:abstract-by-need} for usage analysis in
\Cref{sec:usage-sound}, we need to prove in particular that |UD| satisfies the
abstraction law \textsc{Beta-App} in \Cref{fig:abstraction-laws}.
\textsc{Beta-App} is where the correctness of the summary mechanism lives, so it
is worth dwelling on how to prove it.

A direct proof would unfold the complete definition of the interpreter and reason
about each case, so its complexity scales with the size of the interpreter and it
must be redone whenever |eval| changes.
Such non-modular proofs become unmanageable on pen and paper for large
denotational interpreters such as for WebAssembly~\citep{Brandl:23}.

For \textsc{Beta-App}, dubbed \emph{semantic substitution}, we can do much better:
\begin{toappendix}
\begin{abbreviation}[Field access]
  |(MkUT φ' v')^.φ := φ'|, |(MkUT φ' v')^.v = v'|.
\end{abbreviation}
\end{toappendix}

\begin{lemmarep}[\textsc{Beta-App}, Semantic substitution]
\label{thm:usage-subst-sem}
Let |f :: forall d. (Trace d, Domain d) => d -> d|, |x :: Name| fresh and |a :: UD|.
Then |f a ⊑ apply (fun x f) a| in |UD|.
\end{lemmarep}
\begin{proof}
We instantiate the free theorem for |f|
\[
  \forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict}(R).\
  \forall (d_1,d_2) ∈ R.\
  (f_A(\mathit{inst_1})(d_1), f_B(\mathit{inst_2})(d_2)) ∈ R
\]
as follows
\[\begin{array}{c}
  A \triangleq B \triangleq |UD|, \qquad \mathit{inst_1} \triangleq \mathit{inst_2} \triangleq \mathit{inst}, \qquad d_1 \triangleq a, \qquad d_2 \triangleq \mathit{pre}(x) \\
  R_{x,a}(d_1,d_2) \triangleq \forall g.\ d_1 = g(a) \land d_2 = g(\mathit{pre}(x)) \implies g(a) ⊑ \mathit{apply}(\mathit{fun}(x,g),a)  \\
\end{array}\]
and get (translated back into Haskell)
\[
  \inferrule
    { (|a|,|pre x|) ∈ R_{|x|,|a|} \\ (\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict}(R_{|x|,|a|}) }
    { (|f a|, |f (pre x)|) ∈ R_{|x|,|a|} }
\]
where |pre x := MkUT (singenv x U1) (Rep Uω)| defines the proxy for |x|,
exactly as in the implementation of |fun x|, and $\mathit{inst}$ is the canonical
instance dictionary for |UD|.

We will first apply this inference rule and then show that the goal follows from
$(|f a|, |f (pre x)|) ∈ R_{|x|,|a|}$.

To apply the inference rule, we must prove its premises.
Before we do so, it is very helpful to eliminate the quantification over
arbitrary |g| in the relation $R_{x,a}(d_1,d_2)$.
To that end, we first need to factor |fun x g = abs x (g (pre x))|, where |abs|
is defined as follows:
\begin{spec}
  abs x (MkUT φ v) = MkUT (ext φ x U0) (UCons (φ !? x) v)
\end{spec}
And we simplify $R_{|x|,|a|}(d_1,d_2)$, thus
\begin{spec}
  forall g. d1 = g a /\ d2 = g (pre x) ==> g a ⊑ apply (fun x g) a
<==> {- |fun x g = abs x (g (pre x))| -}
  forall g. d1 = g a /\ d2 = g (pre x) ==> g a ⊑ apply (abs x (g (pre x))) a
<==> {- Use |d1 = g a| and |d2 = g (pre x)| -}
  forall g. d1 = g a /\ d2 = g (pre x) ==> d1 ⊑ apply (abs x d2) a
<==> {- There exists a |g| satisfying |d1 = g a| and |d2 = g (pre x)| -}
  d1 ⊑ apply (abs x d2) a
<==> {- Inline |apply|, |abs|, simplify -}
  d1 ⊑ let MkUT φ v = d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
\end{spec}

Note that this implies |d1^.φ !? x = U0|, because |ext φ x U0 !? x = U0|
and |a^.φ !? x = U0| by the scoping discipline.

It turns out that $R_{|x|,|a|}$ is reflexive on all |d| for which |d^.φ ?! x =
U0|; indeed, then the inequality becomes an equality.
(This corresponds to summarising a function that does not use its
argument.)
That is a fact that we need in the |stuck|, |fun|, |con| and |select| cases
below, so we prove it here:
\begin{spec}
  forall d. d ⊑ MkUT (ext (d^.φ) x U0 + (d^.φ !? x) * a^.φ) (d^.v)
<==> {- Use |(d^.φ ?! x) = U0| -}
  forall d. d ⊑ MkUT (d^.φ) (d^.v) = d
\end{spec}
The last proposition is reflexivity on $⊑$.

Now we prove the premises of the abstraction theorem:
\begin{itemize}
  \item $(|a|,|pre x|) ∈ R_{|x|,|a|}$:
    The proposition unfolds to
    \begin{spec}
      a ⊑ let MkUT φ v = pre x in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
    <==> {- Unfold |pre|, simplify -}
      a ⊑ MkUT (a^.φ) (Rep Uω)
    \end{spec}
    The latter follows from |a^.v ⊑ Rep Uω| because |Rep Uω| is the Top element.

  \item $(\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict}(R_{|x|,|a|})$:
    By the relational interpretation of products, we get one subgoal per instance method.
    \begin{itemize}
      \item \textbf{Case |step|}.
        Goal: $\inferrule{(|d1|,|d2|) ∈ R_{|x|,|a|}}{(|step ev d1|, |step ev d2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premise $(|d1|,|d2|) ∈ R_{|x|,|a|}$, show the goal.
        All cases other than |ev = Look y| are trivial, because then |step ev d = d| and the goal follows by the premise.
        So let |ev = Look y|. The goal is to show
        \begin{spec}
          step (Look y) d1 ⊑ let MkUT φ v = step (Look y) d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}
        We begin by unpacking the assumption $(|d1|,|d2|) ∈ R_{|x|,|a|}$ to show it:
        \begin{spec}
          d1 ⊑ let MkUT φ v = d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        ==>   {- |step (Look y)| is monotonic -}
          step (Look y) d1 ⊑ step (Look y) (MkUT (ext (d2^.φ) x U0 + (d2^.φ !? x) * a^.φ) (d2^.v))
        <==> {- Refold |step (Look y)| -}
          step (Look y) d1 ⊑ MkUT (ext (d2^.φ) x U0 + singenv y U1 + (d2^.φ !? x) * a^.φ) (d2^.v)
        <==>  {- |step (Look y)| preserves value and $|x| \not= |y|$ because |y| is let-bound -}
          step (Look y) d1 ⊑ let MkUT φ v = step (Look y) d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

      \item \textbf{Case |stuck|}.
        Goal: $(|stuck|, |stuck|) ∈ R_{|x|,|a|}$ \\
        Follows from reflexivity, because |stuck = bottom|, and |bottom^.φ !? x = U0|.

      \item \textbf{Case |fun|}.
        Goal: $\inferrule{\forall (|d1|,|d2|) ∈ R_{|x|,|a|} \implies (|f1 d1|, |f2 d2|) ∈ R_{|x|,|a|}}{(|fun y f1|, |fun y f2|) ∈ R_{|x|,|a|}}$. \\
        Additionally, we may assume $|x| \not= |y|$ by lexical scoping.

        Now assume the premise. The goal is to show
        \begin{spec}
          fun y f1 ⊑ let MkUT φ v = fun y f2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        Recall that |fun y f = abs y (f (pre y))| and that |abs y| is monotonic.

        Note that we have $(|pre y|, |pre y|) ∈ R_{|x|,|a|}$ because of $|x| \not= |y|$ and reflexivity.
        That in turn yields $(|f1 (pre y), f2 (pre y)|) ∈ R_{|x|,|a|}$ by assumption.
        This is useful to kick-start the following proof, showing the goal:
        \begin{spec}
          f1 (pre y) ⊑ let MkUT φ v = f2 (pre y) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        ==>   {- Monotonicity of |abs y| -}
          abs y (f1 (pre y)) ⊑ abs y (let MkUT φ v = f2 (pre y) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
        <==>  {- $|x| \not= |y|$ and |a^.φ !? y = U0| due to scoping, |φ !? x| unaffected by floating |abs| -}
          abs y (f1 (pre y)) ⊑ let MkUT φ v = abs y (f2 (pre y)) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        <==>  {- Rewrite |abs y (f (pre y)) = fun y f| -}
          fun y f1 ⊑ let MkUT φ v = fun y f2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

      \item \textbf{Case |apply|}.
        Goal: $\inferrule{(|l1|,|l2|) ∈ R_{|x|,|a|} \\ (|r1|,|r2|) ∈ R_{|x|,|a|}}{(|apply l1 r1|, |apply l2 r2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premises. The goal is to show
        \begin{spec}
          apply l1 r1 ⊑ let MkUT φ v = apply l2 r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        \begin{spec}
          apply l1 r1
        ⊑  {- |l1 ⊑ apply (abs x l2)|, |r2 ⊑ apply (abs x r2)|, monotonicity -}
          apply  (let MkUT φ v = l2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
                 (let MkUT φ v = r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
        ⊑  {- Componentwise, see below -}
          let MkUT φ v = apply l2 r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        For the last step, we show the inequality for |φ| and |v| independently.
        For values, it is easy to see by calculation that the value is
        |v := snd (peel l2^.v)| in both cases.
        The proof for the |Uses| component is quite algebraic;
        we will abbreviate |u := fst (peel l2^.v)|:
        \begin{spec}
          (apply  (let MkUT φ v = l2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
                  (let MkUT φ v = r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v))^.φ
        =  {- Unfold |apply| -}
          ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * (ext (r2^.φ) x U0 + (r2^.φ !? x) * a^.φ)
        =  {- Distribute |u * (φ1 + φ2) = u*φ1 + u*φ2| -}
          ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * ext (r2^.φ) x U0 + u * (r2^.φ !? x) * a^.φ
        =  {- Commute -}
          ext (l2^.φ) x U0 + u * ext (r2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * (r2^.φ !? x) * a^.φ
        =  {- |ext φ1 x U0 + ext φ2 x U0 = ext (φ1 + φ2) x U0|, |u*φ1 + u*φ2 = u * (φ1+φ2)| -}
          ext (l2^.φ + u * r2^.φ) x U0 + ((l2^.φ + u * r2^.φ) !? x) * a^.φ
        =  {- Refold |apply| -}
          let MkUT φ _ = apply l2 r2 in ext φ x U0 + (φ !? x) * a^.φ
        \end{spec}

      \item \textbf{Case |con|}.
        Goal: $\inferrule{\many{(|d1|,|d2|) ∈ R_{|x|,|a|}}}{(|con k (many d1)|, |con k (many d2)|) ∈ R_{|x|,|a|}}$. \\
        We have shown that |apply| is compatible with $R_{|x|,|a|}$, and |foldl|
        is so as well by parametricity.
        The field denotations |many d1| and |many d2| satisfy $R_{|x|,|a|}$ by
        assumption; hence to show the goal it is sufficient to show that
        $(|MkUT emp (Rep Uω)|, |MkUT emp (Rep Uω)|) ∈ R_{|x|,|a|}$.
        And that follows by reflexivity since |emp ?! x = U0|.

      \item \textbf{Case |select|}.
        Goal: $\inferrule{(|d1|,|d2|) ∈ R_{|x|,|a|} \\ (|fs1|,|fs2|) ∈ |Tag :-> ([Rxa] -> Rxa)|}{(|select d1 fs1|, |select d2 fs2|) ∈ R_{|x|,|a|}}$. \\
        Similar to the |con| case, large parts of the implementation are
        compatible with |Rxa| already.
        With $(|MkUT emp (Rep Uω)|, |MkUT emp (Rep Uω)|) ∈ R_{|x|,|a|}$ proved
        in the |con| case, it remains to be shown that |lub :: [UD] -> UD| and
        |(>>) :: UD -> UD -> UD| preserve |Rxa|.
        The proof for |(>>)| is very similar to but simpler than the |apply|
        case, where a subexpression similar to |MkUT (φ1 + φ2) b| occurs.
        The proof for |lub| follows from the proof for the least upper bound
        operator |⊔|.

        So let |(l1,l2), (r1,r2) ∈ Rxa| and show that |(l1 ⊔ r1, l2 ⊔ r2) ∈ Rxa|.
        The assumptions imply that |l1^.v ⊑ l2^.v| and |r1^.v ⊑ r2^.v|, so
        |(l1 ⊔ r1)^.v ⊑ (l2 ⊔ r2)^.v| follows by properties of least upper bound operators.

        Let us now consider the |Uses| component.
        The goal is to show
        \begin{spec}
          (l1 ⊔ r1)^.φ ⊑ (let MkUT φ v = l2 ⊔ r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)^.φ
        \end{spec}

        For the proof, we need the algebraic identity |forall a b c d. a + c ⊔
        b + d ⊑ a ⊔ b + c ⊔ d| in |U|.
        This can be proved by exhaustive enumeration of all 81 cases; the
        inequality is proper when |a = d = U1| and |b = c = U0| (or vice versa).
        Thus we conclude the proof:
        \begin{spec}
          (l1 ⊔ r1)^.φ = l1^.φ ⊔ r1^.φ
        =  {- By assumption, |l1 ⊑ apply (abs x l2)| and |r1 ⊑ apply (abs x r2)|; monotonicity -}
          (ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ) ⊔ (ext (r2^.φ) x U0 + (r2^.φ !? x) * a^.φ)
        ⊑  {- Follows from |forall a b c d. a + c ⊔ b + d ⊑ a ⊔ b + c ⊔ d| in |U| -}
          (ext (l2^.φ) x U0 ⊔ ext (r2^.φ) x U0) + ((l2^.φ !? x)*a^.φ ⊔ (r2^.φ !? x)*a^.φ)
        =  {- |ext φ1 x U0 ⊔ ext φ2 x U0 = ext (φ1 ⊔ φ2) x U0| -}
          ext ((l2 ⊔ r2)^.φ) x U0 + ((l2 ⊔ r2)^.φ !? x) * a^.φ
        =  {- Refold |MkUT φ v| -}
          (let MkUT φ v = l2 ⊔ r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)^.φ
        \end{spec}

      \item \textbf{Case |bind|}.
        Goal: $\inferrule{\forall (|d1|,|d2|) ∈ R_{|x|,|a|} \implies (|f1 d1|, |f2 d2|), (|g1 d1|, |g2 d2|) ∈ R_{|x|,|a|}}{(|bind f1 g1|, |bind f2 g2|) ∈ R_{|x|,|a|}}$. \\
        By the assumptions, the definition |bind f g = g (kleeneFix f)|
        preserves |Rxa| if |kleeneFix| does.
        Since |kleeneFix :: Lat a => (a -> a) -> a| is parametric, it suffices
        to show that the instance of |Lat| preserves |Rxa|.
        We have already shown that |⊔| preserves |Rxa|, and we have also shown
        that |stuck = bottom| preserves |Rxa|.
        Hence we have shown the goal.

        In \Cref{sec:usage-analysis}, we introduced a widening operator
        |widen :: UD -> UD| to the definition of |bind|, that is, we defined
        |bind rhs body = body (kleeneFix (widen . rhs))|.
        For such an operator, we would additionally need to show that |widen|
        preserves |Rxa|.
        Since the proposed cutoff operator in \Cref{sec:usage-analysis} only
        affects the |UValue| component, the only proof obligation is to show
        monotonicity:
        |forall d1 d2. d1^.v ⊑ d2^.v ==> (widen d1)^.v ⊑ (widen d2)^.v|.
        This is a requirement that our widening operator must satisfy anyway.
    \end{itemize}
\end{itemize}

This concludes the proof that $(|f a|, |f (pre x)|) ∈ R_{|x|,|a|}$.
What remains to be shown is that this implies the overall goal
|f a ⊑ apply (fun x f) a|:
\begin{spec}
  (f a, f (pre x)) ∈ Rxa
<==>  {- Definition of |Rxa| -}
  f a ⊑ let MkUT φ v = f (pre x) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
<==>  {- refold |apply|, |fun| -}
  f a ⊑ apply (fun x f) a
\end{spec}
\end{proof}

As can be seen, its statement does not refer to the interpreter definition
|eval| \emph{at all}.
Instead, the complexity of its proof scales with the number of \emph{abstract
operations} supported in the semantic domain of the interpreter for a much more
\emph{modular} proof.
This modular proof appeals to parametricity~\citep{Reynolds:83} of |f|'s
polymorphic type |forall d. (Trace d, Domain d) => d -> d|.
Of course, any function defined by the generic interpreter satisfies this
requirement.
The proof, deferred to the Appendix, instantiates |f|'s free theorem at a relation
that calls |f| with the proxy |MkUT (singenv x U1) (Rep Uω)| that
the implementation of |fun x| supplies; the obligation then reduces to one lemma
per type class method that is easily discharged.

The polymorphism premise is essential: without it, \textsc{Beta-App} fails for
usage analysis.
\begin{example}
\label{ex:syntactic-beta-app}
Let |z //= x //= y|.
The monotone but non-polymorphic |f| defined as follows
\begin{center}
\begin{spec}
  f :: UD -> UD
  f (MkUT φ _) = if φ !? y ⊑ U0 then MkUT emp (Rep Uω) else MkUT (singenv z U1) (Rep Uω)
\end{spec}
\end{center}
violates |f a ⊑ apply (fun x f) a|.
To see that, let |a := MkUT (singenv y U1) (Rep Uω) :: UD| and consider
\[
  |f a = MkUT (singenv z U1) (Rep Uω) {-" \not⊑ "-} (MkUT emp (Rep Uω)) = apply (fun x f) a|.
\]
\end{example}
Next, we will use \Cref{thm:usage-subst-sem} to instantiate
\Cref{thm:abstract-by-need} for usage analysis.

\subsection{Usage Analysis Infers Absence}
\label{sec:usage-sound}

Equipped with the generic abstract interpretation \Cref{thm:abstract-by-need},
we will prove in this subsection that usage analysis from \Cref{sec:abstraction}
infers absence (\Cref{defn:absence}).

\Cref{thm:abstract-by-need} makes it very simple to relate
by-need semantics with usage analysis, taking the place of an
analysis-specific preservation lemma:

\begin{corollaryrep}[|evalUsg1| abstracts |evalNeed1|]
\label{thm:usage-abstracts-need}
Let |e| be an expression and $α_{\mathcal{S}}$ the abstraction function from
\Cref{fig:abstract-name-need}.
Then $α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalUsg1 e|$.
\end{corollaryrep}
\begin{proof}
By \Cref{thm:abstract-by-need}, it suffices to show the abstraction laws
in \Cref{fig:abstraction-laws}.
\begin{itemize}
  \item \textsc{Mono}:
    Always immediate, since |⊔| and |+| are the only functions matching on |U|,
    and these are monotonic.
  \item \textsc{Stuck-App}, \textsc{Stuck-Sel}:
    Trivial, since |stuck = bottom|.
  \item \textsc{Step-App}, \textsc{Step-Sel}, \textsc{Step-Inc}, \textsc{Update}:
    Follows by unfolding |step|, |apply|, |select| and associativity of |+|.
  \item \textsc{Beta-App}:
    Follows from \Cref{thm:usage-subst-sem}.
  \item \textsc{Beta-Sel}:
    Follows by unfolding |select| and |con| and applying a lemma very similar to
    \Cref{thm:usage-subst-sem} multiple times.
  \item \textsc{ByName-Bind}:
    |kleeneFix| approximates the least fixpoint |lfp| since the iteratee |rhs|
    is monotone.
    We have said elsewhere that we omit a widening operator for |rhs| that
    guarantees that |kleeneFix| terminates.
\end{itemize}
\end{proof}

The next step is to leave behind the definition of absence in terms of the LK
machine in favor of one using |evalNeed2|.
That is a welcome simplification because it leaves us with a single semantic
artefact, the denotational interpreter, instead of an operational
semantics and a separate static analysis.
Thanks to bisimilarity (\Cref{thm:need-adequacy-bisimulation}), this new notion is not a
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
                          \Arrow{\Cref{thm:need-adequacy-bisimulation}} \\
  {}\Longleftrightarrow{} & |evalNeed (fillC ectxt (Let x e' e)) emp emp| = |... Step (Look x) ...|
\end{DispWithArrows}
Note that the trace we start with is not necessarily a maximal trace,
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
\Cref{thm:usage-abstracts-need} and a context invariance
\Cref{thm:usage-bound-vars-context} in the Appendix prove that the computed
|φ| approximates |φ'|, so |φ !? x ⊒ φ' !? x ⊒ U1 //= U0|.
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
                      \Arrow{\Cref{thm:usage-abstracts-need}} \\
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

Step \labelcref{arrow:usg-abs} applies the central abstract interpretation
\Cref{thm:usage-abstracts-need} that is the main topic of this section,
abstracting the dynamic trace property in terms of the static semantics.

Finally, step \labelcref{arrow:usg-anal-context} applies
\Cref{thm:usage-bound-vars-context}, which proves that absence information
doesn't change when an expression is put in an arbitrary evaluation context.
The final step is just algebra.
\end{proof}

We have therefore proved that usage analysis correctly infers the semantic property
of absence, as defined in \Cref{defn:absence}.
From this result, one could further prove that the dead code removal constitutes
an optimization that \emph{improves} the program in the sense of \citet{MoranSands:99}.
However, such a proof typically is best carried out in a high-level syntactic
inequational theory; we do not anticipate that the denotational interpreter
perspective offers a significant advantage in that context.

\subsection{Discussion}

The proof exercises the benefits of the framework.
It involves a single semantic artefact, the denotational interpreter, instantiated
at |UD| and at the by-need domain; there is no separate operational semantics to
define and keep consistent.

Above all, the soundness argument needs no step-indexed logical relation over
machine configurations, the device a conventional proof would build to relate a
compositional analysis to a non-compositional machine.
A step-indexed logical relation is still at work, the soundness relation behind
\Cref{thm:abstract-by-need}, but it relates denotations rather than machine
configurations.
The fundamental theorem, that this relation is a congruence, follows from the
compositional structure of the interpreter: a structural induction on the
expression, each case discharged by the abstraction laws and a few reusable
framework lemmas.
This cleaves the soundness obligation in two: the framework discharges the
fundamental theorem once per semantics, while a new analysis supplies only the
abstraction laws of \Cref{fig:abstraction-laws}, properties of its abstract
domain that never mention the machine.
The most substantial of these laws, \textsc{Beta-App}, has a \emph{modular} proof
by parametricity whose complexity is constant in the size of the interpreter.
Making \Cref{thm:abstract-by-need} itself modular for by-need remains open; the
by-name version (\Cref{thm:abstract-by-name}) already is.

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
search states.

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

For concise notation, we define the following abstract substitution operation:

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst-usage}
  We call |abssubst φ x φ' := (ext φ x U0) + (φ !? x) * φ'| the
  \emph{abstract substitution} operation on |Uses|
  and overload this notation for |UT|, so that
  |abssubst (MkUT φ v) x φ' := MkUT (abssubst φ x φ') v|.
\end{definition}

From \Cref{thm:usage-subst-sem}, we can derive the following auxiliary lemma:
\begin{lemma}
  \label{thm:usage-subst-abs}
  If |x| does not occur in |ρ|, then
  |evalUsg e (ext ρ x d) ⊑ abssubst (evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) x (d^.φ)|.
\end{lemma}
\begin{proof}
  Define |f (hat d) := evalUsg e (ext ρ x (hat d))| and |a := d|.
  Note that |f| could be defined polymorphically as
  |f d = eval e (ext ρ x d)|, for suitably polymorphic |ρ|.
  Furthermore, |x| could well be lambda-bound, since it does not occur in the
  range of |ρ| (and that is really what we need).
  Hence we may apply \Cref{thm:usage-subst-sem} to get
  \begin{spec}
    evalUsg e (ext ρ x d)
  ⊑   {- \Cref{thm:usage-subst-sem} -}
    apply (fun x (\(hat d) -> evalUsg e (ext ρ x (hat d)))) d
  =   {- Inline |apply|, |fun| -}
    let MkUT φ v = evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω))) in MkUT (ext φ x U0 + (φ !? x) * d^.φ) v
  =   {- Refold |abssubst| -}
    abssubst (evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) x d^.φ
  \end{spec}
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
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst-abs} -}
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
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst-abs} -}
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
