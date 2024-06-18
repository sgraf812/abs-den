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

\section{Generic By-Name and By-Need Soundness}
\label{sec:soundness}

In this section we prove and apply a generic abstract interpretation theorem
of the form
\[
  |abstract (evalNeed2 e emp) ⊑ eval3 (hat D) e emp|.
\]
This statement reads as follows:
for a closed expression |e|, the \emph{static analysis} result |eval3 (hat D) e emp|
on the right-hand side \emph{overapproximates} ($⊒$) a property of the by-need
\emph{semantics} |evalNeed2 e emp| on the left-hand side.
The abstraction function |abstract :: D (ByNeed T) -> hat D| describes what
semantic property we are interested in, in terms of the abstract semantic domain
|hat D| of |eval3 (hat D) e ρ|, which is short for |eval e ρ :: hat D|.
In our framework, |abstract| is entirely derived from type class
instances on |hat D|.

We will instantiate the theorem at |UD| in order to prove that usage analysis
|evalUsg e ρ = evalD UD e ρ| infers absence, just as absence analysis in
\Cref{sec:problem}.
This proof will be much simpler than the proof for \Cref{thm:absence-correct}.
The main body will only discuss abstraction of closed terms, but the underlying
\Cref{thm:soundness-by-need} in the Appendix considers open terms as well.

%In \Cref{sec:problem} we argued that a proof for such a lemma drowned in
%semantic complexity unrelated to the analysis at hand, so the proof became
%tedious, hand-wavy and error-prone.

%This section will finally link back to \Cref{sec:problem}
%and prove that usage analysis infers absence in the sense of
%\Cref{defn:absence}\sven{Section title is more general then what you promis here. The section title makes you believe that you explain how soundness can be proved in general (for all analyses), but in the first sentence you refer to the usage analysis}\sven{Add one sentence motivating why proving that the usage analysis infering absence is important}.

%Instead, we instantiate a generic soundness statement, one
%that can be reused across many static analyses instantiating our denotational
%interpreter, provided they are sound \wrt by-name and by-need evaluation.
%%The analysis-specific proof mainly concerns the operations of the abstract
%%|Domain|; in case of usage analysis, this proof takes about half a page.
%The soundness statement can be understood in terms of \emph{abstract
%interpretation}, justifying our view of usage analysis as formally abstracting a
%concrete denotational interpreter.

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
      \textstyle|stuck ⊑ Lub (apply (con k ds) a, select (fun x f) alts)|} \\
    \\[-0.5em]
    \inferrule[\textsc{Beta-App}]{%
      |f d = step App2 (eval3 (hat D) e (ext ρ x d))|}{%
      |f a ⊑ apply (fun x f) a|} \qquad
    \inferrule[\textsc{Beta-Sel}]{\begin{minipage}[c]{0.6\textwidth}{%
      \begin{spec}
        (alts ! k) ds  |  len ds /= len xs  = stuck
                       |  otherwise         = step Case2 (eval3 (hat D) er (exts ρ xs ds))
      \end{spec}}\end{minipage}}{%
      |(alts ! k) (map (ρ1 !) ys) ⊑ select (con k (map (ρ1 !) ys)) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Bind-ByName}]{|rhs d1 = eval3 (hat D) e1 (ext ρ x (step (Look x) d1))|\\ |body d1 = step Let1 (eval3 (hat D) e2 (ext ρ x d1))|}{|body (lfp rhs) ⊑ bind rhs body|}
  \end{array}\]
  \fcolorbox{lightgray}{white}{$\begin{array}{c}
    \inferrule[\textsc{Step-Inc}]{}{|d ⊑ step ev d|}
    \qquad
    \inferrule[\textsc{Update}]{}{|step Upd d = d|} \\
  \end{array}$}
  \caption{By-name and \fcolorbox{lightgray}{white}{by-need} abstraction laws for type class instances of abstract domain |hat D|}
  \label{fig:abstraction-laws}
\end{figure}

\subsection{Sound By-name and By-need Interpretation}

This subsection is dedicated to the following derived inference rule for sound
by-need interpretation (\Cref{thm:soundness-by-need-closed}), referring to the
\emph{abstraction laws} in \Cref{fig:abstraction-laws} by name:
\[\begin{array}{c}
  \inferrule{%
    \textsc{Mono} \\ \textsc{Step-App} \\ \textsc{Step-Sel} \\ \textsc{Unwind-Stuck} \\
    \textsc{Intro-Stuck} \\ \textsc{Beta-App} \\ \textsc{Beta-Sel} \\ \textsc{Bind-ByName} \\
    \textsc{Step-Inc} \\ \textsc{Update}
  }{%
  |abstract (evalNeed2 e emp) ⊑ eval3 (hat D) e emp|
  }
\end{array}\]
\noindent
In other words: prove the abstraction laws for an abstract domain |hat D| of
your choosing and we give you for free a proof of sound abstract by-need
interpretation for the static analysis |eval3 (hat D) e emp|!

%The significance of \Cref{thm:usage-abstracts-need-closed} is that it approximates a
%value computed from the \emph{dynamic by-need semantics} on the left-hand side
%with a result of the \emph{static analysis} on the right-hand side; it provides
%\Cref{thm:usage-absence} with an ``interface'' between semantic properties
%and static analysis.

\begin{figure}
\belowdisplayskip=0pt
\begin{spec}
data Pow a = P (Set a); instance Lat Pow where ...
data GC a b = (a -> b) :<->: (b -> a)
repr :: Lat b => (a -> b) -> GC (Pow a) b
repr β = α :<->: γ where α (P as) = Lub (β a | a <- as); γ b = P (setundef (a | β a ⊑ b))

abstract d = β (d emp)

β (Step e d)           = step e (β d)
β (Ret (Stuck, μ))     = stuck
β (Ret (Fun f, μ))     = fun {-"\iffalse"-}"" ""{-"\fi"-} (\(hat d) -> Lub (β (f d μ) | d ∈ γE (hat d)))  where unused (  _   :<->: γE)  = untyped (persistHeap μ)
β (Ret (Con k ds, μ))  = con {-"\iffalse"-}""{-"\fi"-} k (map (\d -> αE (set d)) ds)                      where           αE  :<->: _    = persistHeap μ

persistHeap μ = untyped (repr β where β (Step (Look x) (fetch a))  |  memo a (evalNeed2 e ρ) <- μ ! a
                                                                   =  step (Look x) (eval3 (hat D) e (β << ρ)))
\end{spec}
\caption{Galois connection for sound by-name and by-need abstraction}
\label{fig:name-need-gist}
\end{figure}

Note that \emph{we} get to determine the abstraction function |abstract| based
on the |Trace|, |Domain| and |Lat| instance on \emph{your} |hat D|.
\Cref{fig:name-need-gist} replicates the gist of how |abstract| is thus derived.

Function |abstract| runs its denotation in the empty heap |emp| and hands over
to a function |β| that folds the trace into an abstract domain element in |hat
D|.
Since |hat D| has a |Lat| instance, such a |β| is called a \emph{representation
function}~\citep[Section 4.3]{Nielson:99} which gives rise to a Galois
connection defined via |repr β| from the powerset lattice of by-need traces
(\ie trace properties) into |hat D|.
Function |β| eliminates every |Step ev| in the by-need trace with a call to
|step ev|, and eliminates every concrete |Value| at the end of the trace with a
call to the corresponding |Domain| method.

To that end, the final heap |μ| is then persisted into a Galois connection
|persistHeap μ| that abstracts entries in concrete environments |ρ ! x|
into entries of abstract environments |hat ρ ! x|, resolving all |fetch a|
operations using entries |μ ! a| in the persisted heap.
The precise type of |persistHeap| involves a predicate to characterise the
definable entities in the heap and is omitted here; details can be found in
\Cref{fig:name-need}.
Clearly, \Cref{fig:name-need-gist} is no longer computable Haskell, but it is
mathematiclly well-defined; for example, the recursion in $|persistHeap|.|β|$
is defined via least fixpoints in |Lat (hat D)|.

When the trace ends in a |Con| value, every field denotation |d| is abstracted
via |persistHeap μ|.
When the trace ends in a |Fun| value, an abstract argument denotation |hat d| is
concretised to call the concrete function |f|, and the resulting trace is
recursively abstracted via |β| afterwards.

Thanks to fixing |abstract|, we can prove the following abstraction theorem,
corresponding to the inference rule at the begin of this subsection:

\begin{theoremrep}[Sound By-need Interpretation]
\label{thm:soundness-by-need-closed}
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |abstract| be the abstraction function from \Cref{fig:name-need-gist}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |eval3 (hat D)| is an abstract interpreter that is sound \wrt |abstract|,
that is,
\[
  |abstract (evalNeed2 e emp) ⊑ eval3 (hat D) e emp|.
\]
\end{theoremrep}
\begin{proof}
When we inline |abstract|, the goal is simply \Cref{thm:soundness-by-need} for
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
\begin{abbreviation}[Field access]
  |(MkUT φ' v').φ := φ'|, |(MkUT φ' v').v = v'|.
\end{abbreviation}

For concise notation, we define the following abstract substitution operation:

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst-usage}
  We call |abssubst φ x φ' := (ext φ x U0) + (φ ! x) * φ'| the
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
        evalUsg z (ext ρ x (ρ ! y))
    =   {- |x //= z| -}
        ρ ! z
    =   {- Refold |evalUsg| -}
        evalUsg z (ext ρ x (prx x))
    =   {- |((ρ ! z)^.φ) ! x = U0| -}
        abssubst (evalUsg z (ext ρ x (prx x))) x ((ρ ! y)^.φ)
    =   {- Definition of |evalUsg| -}
        evalUsg (Lam x (Var z) `App` y) ρ
    \end{spec}
    Otherwise, we have |x = z|.
    \begin{spec}
        evalUsg z (ext ρ x (ρ ! y))
    =   {- |x = y|, unfold -}
        ρ ! y
    ⊑   {- |v ⊑ (Rep Uω)| -}
        MkUT ((ρ ! y)^.φ) (Rep Uω)
    =   {- Definition of abstract substitution -}
        abssubst (prx x) x ((ρ ! y)^.φ)
    =   {- Refold |evalUsg| -}
        abssubst (evalUsg z (ext ρ x (prx x))) x ((ρ ! y)^.φ)
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
syntactic definition |f d := step App2 (eval3 UD e (ext ρ x d))|.
Then we get, for |a := ρ ! y :: UD|,
\begin{equation}
  \label{eqn:usage-beta-app}
  \hspace{-1ex}
  |f a = step App2 (eval3 UD e (ext ρ x a)) = eval3 UD e (ext ρ x a) ⊑ eval3 UD (Lam x e `App` y) ρ = apply (fun x f) a|
\end{equation}
Without the syntactic premise of \textsc{Beta-App} to rule out undefinable
entities in |UD -> UD|, the rule cannot be proved for usage analysis; we give a counterexample
in the Appendix (\Cref{ex:syntactic-beta-app}).%
\footnote{Finding domains where all entities $d$ are definable is the classic full
abstraction problem~\citep{Plotkin:77}.}
We discuss concerns of proof modularity in \Cref{sec:related-work}.

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
function |abstract|.
This is how fixing the concrete semantics and |abstract| pays off; the usual
abstraction laws such as |α (apply d a) ⊑ hat apply (α d) (α a)| further
decompose into \textsc{Beta-App}.
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
by-need semantics with usage analysis:

\begin{lemmarep}[|evalUsg| abstracts |evalNeed2|]
\label{thm:usage-abstracts-need-closed}
Let |e| be a closed expression and |abstract| the abstraction function from
\Cref{fig:name-need-gist}.
Then |abstract (evalNeed2 e emp) ⊑ evalUsg e emp|.
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
The abstraction function |abstract| induced by |UD| aggregates lookups in the
trace into a |φ' :: Uses|, \eg
  |abstract ({-" \LookupT(i) \smallstep \LookupT(x) \smallstep \LookupT(i) \smallstep \langle ... \rangle "-})
    = MkUT [ i {-" ↦ "-} Uω, x {-" ↦ "-} U1 ] (...)|.
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

\subsection{Preservation for Boxity Analysis and Evaluation}

\Cref{thm:soundness-by-need-closed} is useful for more analyses than just usage
analysis.
This is easily demonstrated by applying it to boxity analysis:

TODO

Similar to usage analysis, this preservation lemma is not of much use by itself, but
it would be an important part of, \eg an improvement theorem that connects
boxity analysis with a corresponding unboxing transformation.

Let us compare to the preservation-style proof framework in \Cref{sec:problem}.
\begin{itemize}
  \item
    Where there were multiple separate \emph{semantic artefacts} such as a separate
    small-step semantics and an extension of the absence analysis function to
    machine configurations $σ$ in order to state a preservation lemma,
    our proof only has a single semantic artefact that needs to be defined and
    understood: the denotational interpreter, albeit with different instantiations.
  \item
%    The substitution lemma is common to both approaches and indispensable in
%    proving the summary mechanism correct.
    What is more important is that a simple proof for
    \Cref{thm:usage-abstracts-need-closed} in half a page (we encourage the
    reader to take a look) replaces a tedious, error-prone and incomplete (for a
    lack of step indexing) \emph{proof for the preservation lemma}.
    Of course, we lean on \Cref{thm:soundness-by-need-closed} to prove what
    amounts to a preservation lemma; the difference is that our proof properly
    accounts for heap update and can be shared with other analyses that are
    sound \wrt by-name and by-need such as boxity analysis.
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

\subsection{Abstract Interpretation and Denotational Interpreters}
\label{sec:abstract-interpretation}

So far, we have seen how to \emph{use} the abstraction
\Cref{thm:soundness-by-need-closed}, but its proof merely points to
its generalisation for open terms, \Cref{thm:soundness-by-need}.
Proving this theorem correct is the goal of this subsection and the following,
where we approach the problem from the bottom up.

We begin by describing how we intend to apply abstract interpretation to our
denotational interpreter, considering open expressions as well, which
necessitate abstraction of environments.

Given a ``concrete'' (but perhaps undecidable, infinite or coinductive)
semantics and a more ``abstract'' (but perhaps decidable, finite and inductive)
semantics, when does the latter \emph{soundly approximate} properties of the former?
This question is a prominent one in program analysis, and \emph{Abstract
Interpretation}~\citet{Cousot:21} provides a generic framework to formalise
this question.

Sound approximation is encoded by a Galois connection $(|D|, ≤) \galois{|α|}{|γ|}
(|hat D|,⊑)$ between concrete and abstract semantic domains |D| and |hat D|
equipped with a partial order.
An element |hat d ∈ hat D| soundly approximates |d ∈ D| iff |d
≤ γ(hat d)|, iff |α d ⊑ hat d|.
This theory bears semantic significance when $(|D|,≤)$ is instantiated to the
complete lattice of trace properties $(\pow{\Traces},⊆)$, where $\Traces$ is
the set of program traces.
Then the \emph{collecting semantics} relative to a concrete, trace-generating
semantics |eval3 Traces|, defined as |eval3 Collecting e ρ := set (eval3 Traces
e ρ)|, provides the strongest trace property that a given program |(e,ρ)|
satisfies.
In this setting, we extend the original Galois connection to the signature of
|eval3 Traces e| \emph{parametrically},%
\footnote{``Parametrically'' in the sense of \citet{Backhouse:04}, \ie the
structural properties of a Galois connection follow as a free theorem.}
to
\[
  (|(Name :-> pow Traces) -> pow Traces|, |dot (⊆)|)
  \galois{|\f -> α . f . (γ <<)|}{|\(hat f) -> γ . hat f . (α <<)|}
  (|(Name :-> hat D) -> hat D|, |dot (⊑)|),
\]
and state soundness of the abstract semantics |eval3 (hat D)| as
\[
  |eval3 Collecting e ρ ⊆ γ (eval3 (hat D) e (α << set << ρ))|
  \Longleftrightarrow
  |α (set (eval3 Traces e ρ)) ⊑ eval3 (hat D) e (α << set << ρ)|.
\]
The statement should be read as ``The concrete semantics implies the abstract
semantics up to concretisation''~\citet[p. 26]{Cousot:21}.
It looks a bit different to what we exemplified in
\Cref{thm:soundness-by-need-closed} for the following reasons:
(1) |eval3 Traces| and |eval3 (hat D)| are in fact different type class
instantiations of the same denotational interpreter |eval| from
\Cref{sec:interp}, thus both functions share a lot of common structure.
(2) The Galois connections |byName| and |nameNeed| defined below are completely
determined by type class instances, even for infinite traces.
(3) It turns out that we need to syntactically restrict the kind
of |D| that occurs in an environment |ρ| due to the full
abstraction problem~\citep{Plotkin:77}, so that the Galois connection
|byName| looks a bit different.
(4) By-need semantics is stateful whereas analyses such as usage analysis are
rarely so; this again leads to a slightly different use of the final Galois
connection |nameNeed| as exemplified in \Cref{thm:soundness-by-need-closed}.

\subsection{Guarded Fixpoints, Safety Properties and Safety Extension of a Galois Connection}
\label{sec:safety-extension}

We like to describe a semantic trace property as a ``fold'', in terms of a
|Trace| instance.
For example, we collect a trace into a |Uses| in
\Cref{sec:usage-trace-abstraction} and \Cref{thm:usage-abstracts-need-closed}.
Of course such a fold (an inductive elimination procedure) has no meaning when
the trace is infinite!
Yet it is always clear what we mean: when the trace is infinite, we consider the
meaning of the fold as the limit (\ie least fixpoint) of its finite prefixes.
In this subsection, we discuss when and why this meaning is correct.

Suppose for a second that we were only interested in the trace component of our
semantic domain, thus effectively restricting ourselves to
$\Traces \triangleq |T ()|$, and that we were to approximate properties $P ∈
\pow{\Traces}$ about such traces by a Galois connection
$(\pow{\Traces},⊆) \galois{|α|}{|γ|} (|hat D|, ⊑)$.
Alas, although the abstraction function |α| is well-defined as a mathematical
function, it most certainly is \emph{not} computable at infinite inputs (in
$\Traces^{\infty}$), for example at
|fix (Step (Look x)) = Step (Look x) (Step (Look x) ...)|!

Computing with such an |α| is of course inacceptable for a \emph{static} analysis.
Usually this is resolved by approximating the fixpoint by the least fixpoint of
the abstracted iteratee, \eg |lfp (α . Step (Look x) . γ)|.
It is however not the case that this yields a sound approximation of infinite
traces for \emph{arbitrary} trace properties.
A classic counterexample is the property
$P \triangleq \{ |τ| \mid |τ|\text{ terminates} \}$;
if $P$ is restricted to finite traces $\Traces^{*}$, the analysis that
constantly says ``terminates'' is correct; however this result doesn't carry over
``to the limit'', when |τ| may also range over infinite traces in
$\Traces^{\infty}$.
Hence it is impossible to soundly approximate $P$ with a least fixpoint in the
abstract.

Rather than making the common assumption that infinite traces are soundly
approximated by $\bot$ (such as in strictness
analysis~\citep{Mycroft:80,Wadler:87}), thus effectively assuming that all
executions are finite, our framework assumes that the properties of interest are
\emph{safety properties}~\citep{Lamport:77}:

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
and we can exploit safety to extend a finitary Galois connection to infinite
inputs:
\begin{lemma}[Safety extension]
\label{thm:safety-extension}
Let |hat D| be a domain with instances for |Trace| and |Lat|,
$(\pow{\Traces^{*}},⊆) \galois{|α|}{|γ|} (|hat D|, ⊑)$ a Galois connection and
$P ∈ \pow{\Traces}$ a safety property.
Then any domain element |hat d| that soundly approximates $P$ via |γ| on finite
traces soundly approximates $P$ on infinite traces as well:
\[
  \forall |hat d|.\ P ∩ \Traces^{*} ⊆ |γ|(|hat d|) \Longrightarrow P ∩ \Traces^{\infty} ⊆ |γinf|(|hat d|),
\]
where the \emph{extension} $(\pow{\Traces^{*}},⊆) \galois{|αinf|}{|γinf|} (|hat D|, ⊑)$ of
$\galois{|α|}{|γ|}$ is defined by the following abstraction function:
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
On the other hand, $P$ is a safety property and $|τ| ∈ P$, so for any
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
Let |hat D| be a domain with instances for |Trace| and
|Lat|, and let $(\pow{\Traces},⊆) \galois{α}{γ} (|hat D|, ⊑)$ a Galois
connection extended to infinite traces via \Cref{thm:safety-extension}.
Then, for any guarded iteratee |f :: Later Traces -> Traces|,
\[
  |α|(\{ |fix f| \}) ⊑ |lfp (α . powMap f . γ)|,
\]
where |lfp (hat f)| denotes the least fixpoint of |hat f| and |powMap f :: pow (Later Traces) -> pow
Traces| is the lifting of |f| to powersets.
\end{lemma}
\begin{proof}
We should note that the proposition is sloppy in the treatment of
$\later$ and should rather have been
\[
  |α|(\{ |fix f| \}) ⊑ |lfp (α . powMap (f . next) . γ)|,
\]
where |next :: Later T -> T|.
Since we have proven totality in \Cref{sec:totality}, the utility of being
explicit in |next| is rather low (much more so since a pen and paper proof is
not type checked) and we will admit ourselves this kind of sloppiness from now
on.

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

We will now see how the by-name abstraction laws in \Cref{fig:abstraction-laws}
induce an abstract interpretation of by-name evaluation.
The corresponding proofs are somewhat simpler than for by-need because no heap
update is involved.

As we are getting closer to the point where we reason about idealised,
total Haskell code, it is important to nail down how Galois connections are
represented in Haskell, and how we construct them.
Following \citet[Section 4.3]{Nielson:99}, every \emph{representation function}
|β :: a -> b| into a partial order $(|b|,⊑)$ yields a Galois connection between
|Pow|ersets of |a| and $(|b|,⊑)$:
\begin{code}
data Pow a = P (Set a) deriving (Eq, Ord)
data GC a b = (a -> b) :<->: (b -> a)
repr :: Lat b => (a -> b) -> GC (Pow a) b
repr β = α :<->: γ where α (P as) = Lub (β a | a <- as); γ b = P (setundef (a | β a ⊑ b))
\end{code}
While the |γ| exists as a mathematical function, it is in general impossible to
compute even for finitary inputs.
Every domain |hat D| with instances |(Trace (hat D), Domain (hat D), Lat (hat D))|
induces a \emph{trace abstraction} via the following representation
function, writing |powMap f| to map |f| over |Pow|%
\footnote{
Recall that |fun| actually takes |x :: Name| as the first argument as a cheap
De Bruijn level. Every call to |fun| would need to chose a fresh |x|. We omit
the bookkeeping here; an alternative would be to require the implementation of
usage analysis/|UD| to track their own De Bruijn levels.}
\begin{code}
type (named d) = d  -- exact meaning defined below
trace  ::  (Trace (hat d), Domain (hat d), Lat (hat d))
       =>  GC (Pow (D r)) (hat d) -> GC (Pow (named (D r))) (named (hat d)) -> GC (Pow (T (Value r))) (hat d)
trace (αT :<->: γT) (αE :<->: γE) = repr β where
  β (Ret Stuck)       = stuck
  β (Ret (Fun f))     = fun {-"\iffalse"-}"" ""{-"\fi"-} (αT . powMap f . γE)
  β (Ret (Con k ds))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)
  β (Step e (hat d))  = step e (β (hat d))
\end{code}
Note how |trace| expects two Galois connections: The first one is applicable
in the ``recursive case'' and the second one applies to (the powerset over)
|named (D (ByName T))|, a subtype of |D (ByName T)|.
Every |d :: (named (ByName T))| is of the form |Step (Look x) (eval e ρ)| for
some |x|, |e|, |ρ|, characterising domain elements that end up in an
environment or are passed around as arguments or in fields.
We have seen a similar characterisation in the Agda encoding of
\Cref{sec:adequacy}.
The distinction between |αT| and |αE| will be important for proving that
evaluation preserves trace abstraction (comparable to \Cref{thm:preserve-absent}
for a big-step-style semantics),
a necessary auxiliary lemma for \Cref{thm:soundness-by-name}.

We utilise the |trace| combinator to define |byName| abstraction as its
(guarded) fixpoint:
\begin{code}
env :: (Trace (hat d), Domain (hat d), Lat (hat d)) => GC (Pow (named (D (ByName T)))) (named (hat d))
env = untyped (repr β where β (Step (Look x) (eval e ρ)) = step (Look x) (eval e (β << ρ)))

byName :: (Trace (hat d), Domain (hat d), Lat (hat d)) => GC (Pow (D (ByName T))) (hat d)
byName = (αT . powMap unByName) :<->: (powMap ByName . γT) where αT :<->: γT = trace byName env
\end{code}
There is a need to clear up the domain and range of |env|.
Since its domain is sets of elements from |named (D (ByName T))|, its range
|named d| is the (possibly infinite) join over abstracted elements that
look like |step (Look x) (eval e (β << ρ))| for some ``closure'' |x|, |e|, |ρ|.
Although we have ``sworn off'' operational semantics for abstraction, we
defunctionalise environments into syntax to structure the vast semantic domain
in this way, thus working around the full abstraction problem~\citep{Plotkin:77}.
More formally,

\begin{definition}[Syntactic by-name environments]
  \label{defn:syn-name}
  Let |hat D| be a domain satisfying |Trace|, |Domain| and |Lat|.
  We write |named (hat D) d| (resp. |nameenv (hat D) ρ|) to say that the
  denotation |d| (resp. environment |ρ|) is \emph{syntactic}, which we define
  by mutual guarded recursion as
  \begin{itemize}
    \item |named (hat D) d| iff there exists a set |Clo| of syntactic closures such
      that \\
      |d = Lub (step (Look x) (eval e ρ1 :: (hat D)) || (x,e,ρ1) ∈ Clo && Later (nameenv (hat D) ρ1))|,
      and
    \item |nameenv (hat D) ρ| iff for all |x|, |named (hat D) (ρ ! x)|.
  \end{itemize}
\end{definition}
% We really need to generalise over |D|, because we need this characterisation in the abstract as well.

For the remainder of this subsection, we assume a refined definition of |Domain|
and |HasBind| that expects |named (hat D)| (denoting the set of
|hat d :: hat D| such that |named (hat D) (hat d)|) where we pass around
denotations that end up in an environment.
It is then easy to see that |eval e ρ| preserves |nameenv (hat D)| in recursive
invocations, and |trace| does so as well.

% Let's not bother with monotonicity
%\begin{lemma}[Monotonicity]
%  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
%  |Lat|, satisfying property \textsc{Mono} in
%  \Cref{fig:abstraction-laws}.
%  Then |eval e :: (Name :-> hat D) -> hat D| is a monotone function.
%\end{lemma}
%\begin{proofsketch}
%  Follows by parametricity.
%\end{proofsketch}

\begin{lemma}[By-name evaluation preserves trace abstraction]
  \label{thm:eval-preserves}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the soundness properties \textsc{Step-App},
  \textsc{Step-Sel}, \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName}
  in \Cref{fig:abstraction-laws}.

  If |evalName e ρ1 = many (Step ev) (evalName v ρ2)| in the concrete,
  then |many (step ev) (eval v (αE << set << ρ2)) ⊑ eval e (αE << set << ρ1)|
  in the abstract,
  where |αE :<->: γE = env|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    |evalName x ρ1 = Step (Look y) (evalName e' ρ3) = many (Step ev) (evalName v ρ2)|
    for some |y|, |e'|, |ρ3|,
    so that |many ev = Look y : many ev1| for some |ev1| by determinism.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = Look y : many ev1| -}
        step (Look y) (many (step ev1) (eval v (βE << ρ2)))
    ⊑   {- Induction hypothesis at |ev1|, |ρ3| as above -}
        step (Look y) (eval e' (βE << ρ3))
    =   {- Refold |βE|, |ρ3 ! x| -}
        βE (ρ1 ! x)
    =   {- Refold |eval x (βE << ρ1)| -}
        eval x (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Lam|, |ConApp|: By reflexivity of $⊑$.
  \item \textbf{Case} |App e x|:
    Then |evalName e ρ1 = many (Step ev1) (evalName (Lam y body) ρ3)|,
    |evalName body (ext ρ3 y (ρ1 ! x)) = many (Step ev2) (evalName v ρ2)|.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = [App1] ++ many ev1 ++ [App2] ++ many ev2|, IH at |ev2| -}
        step App1 (many (step ev1) (step App2 (eval body (ext (βE << ρ3) y (βE << ρ1 ! x)))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        step App1 (many (step ev1) (apply (eval (Lam y body) (βE << ρ3)) (βE << ρ1 ! x)))
    ⊑   {- Assumption \textsc{Step-App} -}
        step App1 (apply (many (step ev1) (eval (Lam y body) (βE << ρ3))) (βE << ρ1 ! x))
    ⊑   {- Induction hypothesis at |ev1| -}
        step App1 (apply (eval e (βE << ρ1)) (βE << ρ1 ! x))
    =   {- Refold |eval (App e x) (βE << ρ1)| -}
        eval (App e x) (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Case e alts|:
    Then |evalName e ρ1 = many (Step ev1) (evalName (ConApp k ys) ρ3)|,
    |evalName er (exts ρ1 xs (map (ρ3 !) ys)) = many (Step ev2) (evalName v ρ2)|,
    where |alts ! k = (xs,er)| is the matching RHS.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    ⊑   {- |many ev = [Case1] ++ many ev1 ++ [Case2] ++ ev2|, IH at |ev2| -}
        step Case1 (many (step ev1) (step Case2 (eval er (βE << (exts ρ1 xs (map (hat ρ3 !) ys))))))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev1) (select (eval (ConApp k ys) (βE << ρ3)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (many (step ev1) (eval (ConApp k ys) (βE << ρ3))) (cont << alts))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Case1 (select (eval e (βE << ρ1)) (cont << alts))
    =   {- Refold |eval (Case e alts) (βE << ρ1)| -}
        eval (Case e alts) (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Let x e1 e2|:
    We make good use of \Cref{thm:guarded-fixpoint-abstraction} below:
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = Let1 : many ev1| -}
        step Let1 (many (step ev1) (eval v (βE << ρ2)))
    ⊑   {- Induction hypothesis at |ev1| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (βE (Step (Look x) (fix (\d1 -> evalName e1 (ext ρ1 x (Step (Look x) d1))))))))
    =   {- Partially roll |fix| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (βE (fix (\d1 -> Step (Look x) (evalName e1 (ext ρ1 x d1)))))))
    ⊑   {- \Cref{thm:guarded-fixpoint-abstraction} -}
        step Let1 (eval e2 (ext (βE << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE << ρ1) x (αE (γE (hat d1)))))))))
    ⊑   {- |αE . γE ⊑ id| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (lfp (\(hat d1) -> step (Look x) (eval e1 (ext (βE << ρ1) x (hat d1)))))))
    =   {- Partially unroll |lfp| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (step (Look x) (lfp (\(hat d1) -> eval e1 (ext (βE << ρ1) x (step (Look x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName} -}
        bind  (\(hat d1) -> eval e1 (ext ((βE << ρ1)) x (step (Look x) (hat d1))))
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE << ρ1)) x (step (Look x) (hat d1)))))
    =   {- Refold |eval (Let x e1 e2) (βE << ρ1)| -}
        eval (Let x e1 e2) (βE << ρ1)
    \end{spec}
\end{itemize}
\end{proof}

We can now prove the by-name abstraction theorem:

\begin{theorem}[Sound By-name Interpretation]
\label{thm:soundness-by-name}
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT := byName|, |αE :<->: γE := env|.
If the by-name abstraction laws in \Cref{fig:abstraction-laws} hold,
then |eval| instantiates to an abstract interpreter that is sound
\wrt |γE -> αT|, that is,
\[
  |αT (set (evalName e ρ) :: Pow (D (ByName T))) ⊑ evalD (hat D) e (αE << set << ρ)|.
\]
\end{theorem}
\begin{proof}
We first restate the goal in terms of the |repr|esentation functions
|βT := αT . set| and |βE := αE . set|:
\[
  \forall |ρ|.\ |βT (evalName e ρ) ⊑ (evalD (hat D) e (βE << ρ))|.
\]
We will prove this goal by Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |αT|.
    Otherwise,
    \begin{spec}
        βT (ρ ! x)
    =   {- |nameenv (Pow (D (ByName T))) (set << ρ)|, Unfold |βT| -}
        step (Look y) (βT (evalName e' ρ'))
    ⊑   {- Induction hypothesis -}
        step (Look y) (eval e' (βE << ρ'))
    =   {- Refold |βE| -}
        βE (ρ ! x)
    \end{spec}
  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        βT (evalName (Lam x body) ρ)
    =   {- Unfold |eval|, |βT| -}
        fun (\(hat d) -> Lub (step App2 (βT (evalName body (ext ρ x d))) | βE d ⊑ hat d))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> Lub (step App2 (eval body (βE << (ext ρ x d))) | βE d ⊑ hat d))
    ⊑   {- Least upper bound / |αE . γE ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext ((βE << ρ)) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k ds|:
    \begin{spec}
        βT (evalName (ConApp k xs) ρ)
    =   {- Unfold |eval|, |βT| -}
        con k (map ((βE << ρ) !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    The stuck case follows by unfolding |βT|.

    Our proof obligation can be simplified as follows
    \begin{spec}
        βT (evalName (App e x) ρ)
    =   {- Unfold |eval|, |βT| -}
        step App1 (βT (apply (evalName e ρ) (ρ ! x)))
    =   {- Unfold |apply| -}
        step App1 (βT (evalName e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    ⊑   {- By cases, see below -}
        step App1 (apply (eval e (βE << ρ)) ((βE << ρ) ! x))
    =   {- Refold |eval| -}
        eval (App e x) (βE << ρ)
    \end{spec}

    When |evalName e ρ| diverges, we have
    \begin{spec}
    =   {- |evalName e ρ| diverges, unfold |βT| -}
        step ev1 (step ev2 (...))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (step ev1 (step ev2 (...))) ((βE << ρ) ! x)
    =   {- Refold |βT|, |evalName e ρ| -}
        apply (βT (evalName e ρ)) ((βE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}
    Otherwise, |evalName e ρ| must produce a value |v|.
    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
    (resp. |d := con k (map βE ds)|) and have
    \begin{spec}
        βT (evalName e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |evalName e ρ = many (Step ev) (return v)|, unfold |βT| -}
        many (step ev) (βT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v| not |Fun|, unfold |βT| -}
        many (step ev) stuck
    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map βT ds)| -}
        many (step ev) (apply d a)
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) d) ((βE << ρ) ! x)
    =   {- Refold |βT|, |evalName e ρ| -}
        apply (βT (evalName e ρ)) ((βE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}
    In the final case, we have |v = Fun f|, which must be the result of some
    call |evalName (Lam y body) ρ1|; hence
    |f := \d -> Step App2 (evalName body (ext ρ1 y d))|.
    \begin{spec}
        βT (evalName e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |evalName e ρ = many (Step ev) (return v)|, unfold |βT| -}
        many (step ev) (βT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v=Fun f|, with |f| as above; unfold |βT| -}
        many (step ev) (step App2 (βT (evalName body (ext ρ1 y (ρ ! x)))))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step App2 (eval body (βE << (ext ρ1 y (ρ ! x)))))
    =   {- Rearrange -}
        many (step ev) (step App2 (eval body (ext (βE << ρ1) y ((βE << ρ) ! x))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        many (step ev) (apply (eval (Lam y body) (βE << ρ1)) ((βE << ρ) ! x))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) (eval (Lam y body) (βE << ρ1))) ((βE << ρ) ! x)
    ⊑   {- \Cref{thm:eval-preserves} applied to |many ev| -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The stuck case follows by unfolding |βT|.
    When |evalName e ρ| diverges or does not evaluate to |evalName (ConApp k ys) ρ1|,
    the reasoning is similar to |App e x|, but in a |select| context.
    So assume that |evalName e ρ = many (Step ev) (evalName (ConApp k ys) ρ1)| and that
    there exists |((cont << alts) ! k) ds = Step Case2 (evalName er (exts ρ xs ds))|.
    \begin{spec}
        βT (evalName (Case e alts) ρ)
    =   {- Unfold |eval|, |βT| -}
        step Case1 (βT (select (evalName e ρ) (cont << alts))
    =   {- Unfold |select| -}
        step Case1 (βT (evalName e ρ >>= \case Con k ds | k ∈ dom alts -> ((cont << alts) ! k) ds))
    =   {- |evalName e ρ = many (Step ev) (evalName (ConApp k ys) ρ1)|, unfold |βT| -}
        step Case1 (many (step ev) (βT (evalName (ConApp k ys) ρ1) >>= \case Con k ds | k ∈ dom (cont << alts) -> ((cont << alts) ! k) ds))
    =   {- Simplify |return (Con k ds) >>= f = f (Con k ds)|, |(cont << alts) ! k| as above -}
        step Case1 (many (step ev) (βT (Step Case2 (evalName er (exts ρ xs (map (ρ1 !) ys))))))
    =   {- Unfold |βT| -}
        step Case1 (many (step ev) (step Case2 (βT (evalName er (exts ρ xs (map (ρ1 !) ys))))))
    ⊑   {- Induction hypothesis -}
        step Case1 (many (step ev) (step Case2 (eval er (exts (βE << ρ) xs (map ((βE << ρ1) !) ys)))))
    =   {- Refold |cont| -}
        step Case1 (cont (alts ! k) (map ((βE << ρ1) !) xs))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev) (select (eval (ConApp k ys) (βE << ρ1)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (many (step ev) (eval (ConApp k ys) (βE << ρ1))) (cont << alts))
    ⊑   {- \Cref{thm:eval-preserves} applied to |many ev| -}
        step Case1 (select (eval e (βE << ρ)) (cont << alts))
    =   {- Refold |eval| -}
        eval (Case e alts) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        βT (evalName (Let x e1 e2) ρ)
    =   {- Unfold |eval| -}
        βT (bind  (\d1 -> evalName e1 (ext ρ x (Step (Look x) d1)))
                  (\d1 -> Step Let1 (evalName e2 (ext ρ x (Step (Look x) d1)))))
    =   {- Unfold |bind|, |βT| -}
        step Let1 (βT (evalName e2 (ext ρ x (Step (Look x) (fix (\d1 -> evalName e1 (ext ρ x (Step (Look x) d1))))))))
    ⊑   {- Induction hypothesis -}
        step Let1 (eval e2 (ext (βE << ρ) x (βE (Step (Look x) (fix (\d1 -> evalName e1 (ext ρ x (Step (Look x) d1))))))))
    \end{spec}
    And from hereon, the proof is identical to the |Let| case of
    \Cref{thm:eval-preserves}:
    \begin{spec}
    ⊑   {- By \Cref{thm:guarded-fixpoint-abstraction}, as in the proof for \Cref{thm:eval-preserves} -}
        step Let1 (eval e2 (ext (βE << ρ) x (step (Look x) (lfp (\(hat d1) -> eval e1 (ext (βE << ρ) x (step (Look x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = βE << ρ| -}
        bind  (\d1 -> eval e1 (ext (βE << ρ) x (step (Look x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (βE << ρ) x (step (Look x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βE << ρ)| -}
        eval (Let x e1 e2) (βE << ρ)
    \end{spec}
\end{itemize}
\end{proof}

We can now show a generalisation to open expressions of the by-name version of
\Cref{thm:usage-abstracts-need-closed}:
\begin{lemma}[|evalUsg| abstracts |evalName|, open]
\label{thm:usage-abstracts-name}
Usage analysis |evalUsg| is sound \wrt |evalName|, that is,
\[
  |αT (set (evalName e ρ)) ⊑ (evalUsg e (αE << set << ρ) :: UD) where αT :<->: _ = byName; αE :<->: _ = env|.
\]
\end{lemma}
\begin{proof}
By \Cref{thm:soundness-by-name}, it suffices to show the abstraction laws
in \Cref{fig:abstraction-laws} as done in the proof for \Cref{thm:usage-abstracts-need-closed}.
\end{proof}

The following example shows why we need syntactic premises in \Cref{fig:abstraction-laws}.
It defines a monotone, but non-syntactic |f :: UD -> UD| for which
|f a {-" \not⊑ "-} apply (fun x f) a|.
So if we did not have the syntactic premises, we would not be able to prove usage
analysis correct.
\begin{example}
\label{ex:syntactic-beta-app}
Let |z //= x //= y|.
The monotone function |f| defined as follows
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

\subsection{Abstract By-need Soundness, in Detail}
\label{sec:by-need-soundness}

\begin{figure}
\begin{code}
persistHeap :: (Trace (hat d), Domain (hat d), Lat (hat d)) => needheap -> GC (needd ) (named (hat d))
persistHeap μ = untyped (repr β where β (Step (Look x) (fetch a))  |  memo a (evalNeed2 e ρ) <- μ ! a
                                                                   =  step (Look x) (eval e (β << ρ)))

nameNeed  ::  (Trace (hat d), Domain (hat d), Lat (hat d)) =>  GC (Pow (T (Value (ByNeed T), needheap))) (hat d)
nameNeed = repr β where
  β (Step e d)           = step e (β d)
  β (Ret (Stuck, μ))     = stuck
  β (Ret (Fun f, μ))     = fun {-"\iffalse"-}"" ""{-"\fi"-} (\(hat d) -> Lub (β (f d μ) | d ∈ γE (hat d)))  where unused (  _   :<->: γE)  = untyped (persistHeap μ)
  β (Ret (Con k ds, μ))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)                              where           αE  :<->: _    = persistHeap μ
\end{code}
\caption{Galois connection for sound by-name and by-need abstraction}
\label{fig:name-need}
\end{figure}

Now that we have gained some familiarity with the proof framework while
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

In order to formalise this intuition, we must find a Galois connection that does
so, starting with its domain.
Although in \Cref{sec:evaluation-strategies} we considered a |d :: D (ByNeed T)|
as an atomic denotation, such a denotation actually only makes sense when it
travels together with an environment |ρ| that ties free variables to their addresses
in the heap that |d| expects.

For our purposes, the key is that a by-need environment |ρ| and a heap |μ| can
be ``persisted'' into a corresponding by-name environment.
This operation forms a Galois connection |persistHeap| in \Cref{fig:name-need},
where |needd| serves a similar purpose as |named (hat d)| from
\Cref{defn:syn-name}, restricting environment entries to the syntactic by-need
form |Step (Look x) (fetch a)| and heap entries in |needheap| to |memo a (eval
e ρ)|.

\begin{definition}[Syntactic by-need heaps and environments, address domain]
  \label{defn:syn-heap}
  We write |needenv ρ| (resp. |needheap μ|) to say that the by-need
  environment |ρ :: Name :-> Pow (D (ByNeed T))| (resp. by-need heap |μ|) is
  \emph{syntactic}, defined by mutual guarded recursion as
  \begin{itemize}
    \item |needd d| iff there exists a set |Clo| of syntactic closures such that \\
      |d = Cup (Step (Look x) (fetch a) || (x,a) ∈ Clo)|.
    \item |needenv ρ| iff for all |x|, |needd (ρ ! x)|.
    \item |adom d := set (a || Step (Look y) (fetch a) ∈ d)|
    \item |adom ρ := Cup (adom (ρ ! x) || x ∈ dom ρ)|.
    \item |needheap μ| iff for all |a|, there is a set |Clo| of syntactic closures such that \\
      |μ ! a = Cup (memo a (evalNeed2 e ρ) || Later ((e,ρ) ∈ Clo && needenv ρ && adom ρ ⊆ dom μ))|.
  \end{itemize}
  We refer to |adom d| (resp. |adom ρ|) as the \emph{address domain} of |d| (resp. |ρ|).
\end{definition}

We assume that all concrete environments |Name :-> D (ByNeed T)| and heaps |Heap
(ByNeed T)| satisfy |needenv| resp. |needheap|.
It is easy to see that syntacticness is preserved by |evalNeed| whenever
the environment or heap is extended, assuming that |Domain| and |HasBind| are
adjusted accordingly.

The environment abstraction |αE μ :<->: _ = persistHeap μ| improves the more
``evaluated'' |μ| is.
E.g.,\ when |μ1| \emph{progresses} into |μ2| during evaluation, written
|μ1 ~> μ2|, it is |αE μ2 d ⊑ αE μ1 d| for all |d|.
The heap progression relation is formally defined (on syntactic heaps
|needheap|) in \Cref{fig:heap-progression}, and we will now work
toward a proof for the approximation statement about |αE| in
\Cref{thm:heap-progress-persist}.

\begin{figure}
  \[\begin{array}{c}
    \ruleform{ μ_1 \progressto μ_2 }
    \\ \\[-0.5em]
    \inferrule[\textsc{$\progressto$-Refl}]{|needheap μ|}{|μ ~> μ|}
    \qquad
    \inferrule[\progresstotrans]{|μ1 ~> μ2| \quad |μ2 ~> μ3|}{|μ1 ~> μ3|}
    \qquad
    \inferrule[\progresstoext]{|a| \not∈ |dom μ| \quad |adom ρ ⊆ dom μ ∪ set a|}{|μ ~> ext μ a (memo a (evalNeed2 e ρ))|}
    \\ \\[-0.5em]
    \inferrule[\progresstomemo]{|μ1 ! a = memo a (evalNeed2 e ρ1)| \quad |Later (evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2))|}{|μ1 ~> ext μ2 a (memo a (evalNeed2 v ρ2))|}
    \\[-0.5em]
  \end{array}\]
  \caption{Heap progression relation}
  \label{fig:heap-progression}
\end{figure}

% Currently dead:
%\begin{lemma}
%\label{thm:progression-allocates}
%If |μ1 ~> μ2|, then |dom μ1 ⊆ dom μ2|.
%\end{lemma}
%\begin{proof}
%Simple proof by induction after realising that |eval| never deletes heap
%entries.
%\end{proof}

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

\begin{lemma}[Evaluation progresses the heap]
\label{thm:eval-progression}
If |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|, then |μ1 ~> μ2|.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
Since there is no approximation yet, all occurring closure sets in |needenv| are
singletons.
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
    =   {- Determinism of |evalNeed|, assumption -}
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
    =   {- Unfold |evalNeed| -}
        bind  (\d1 -> evalNeed e1 (ext ρ1 x (step (Look x) d1)))
              (\d1 -> step Let1 (evalNeed e2 (ext ρ1 x (step (Look x) d1))))
              μ1
    =   {- Unfold |bind|, |a := nextFree μ| with $|a| \not\in |dom μ|$ -}
        step Let1 (evalNeed e2 (ext ρ1 x (step (Look x) (fetch a)))
                               (ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a)))))))
    \end{spec}
    At this point, we can apply the induction hypothesis to |evalNeed e2 (ext ρ1 x
    (step (Look x) (fetch a)))| to conclude that
    |ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a))))) ~> μ2|.

    On the other hand, we have
    |μ1 ~> ext μ1 a (memo a (evalNeed2 e1 (ext ρ1 x (step (Look x) (fetch a)))))|
    by rule \progresstoext (note that $|a| \not∈ |dom μ|$), so the goal follows
    by \progresstotrans.
\end{itemize}
\end{proof}

\Cref{thm:eval-progression} exposes nested structure in \progresstomemo.
For example, if |μ1 ~> ext μ2 a (memo a (evalNeed2 v ρ2))| is the result of applying
rule \progresstomemo, then we obtain a proof that the memoised expression
|evalNeed2 e ρ1 μ1 = many (Step ev) (evalNeed2 v ρ2 μ2)|, and this
evaluation in turn implies that |μ1 ~> μ2|.

Heap progression is useful to state a number of semantic properties, for example
the ``update once'' property of memoisation and that a heap binding is
semantically irrelevant when it is never updated:

\begin{lemma}[Update once]
\label{thm:update-once}
If   |μ1 ~> μ2| and |μ1 ! a = memo a (evalNeed2 v ρ)|,
then |μ2 ! a = memo a (evalNeed2 v ρ)|.
\end{lemma}
\begin{proof}
Simple proof by induction on |μ1 ~> μ2|.
The only case updating a heap entry is \progresstomemo, and there we can see
that |μ2 ! a = memo (evalNeed2 v ρ)| because evaluating |v| in |μ1| does not make
a step.
\end{proof}

\begin{lemma}[No update implies semantic irrelevance]
\label{thm:no-update-irrelevance}
If |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|
and |μ1 ! a = μ2 ! a = memo a (evalNeed2 e1 ρ3)|, |e1| not a value,
then
\[
  |forall d. evalNeed e ρ1 (ext μ1 a d) = many (Step ev) (evalNeed v ρ2 (ext μ2 a d))|
\]
as well.
\end{lemma}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
     It is |evalNeed x ρ1 μ1 = Step (Look y) (memo a1 (evalNeed e1 ρ3 μ1))| for the
     suitable |a1|,|y|.
     Furthermore, it must be $|a| \not= |a1|$, because otherwise, |memo a| would
     have updated |a| with |evalNeed2 v ρ2|.
     Then we also have
     \[|evalNeed x ρ1 (ext μ1 a d) = Step (Look y) (memo a1 (evalNeed e1 ρ3 (ext μ1 a d)))|.\]
     The goal follows from applying the induction hypothesis and realising that
     |μ2 ! a1| has been updated consistently with |memo a1 (evalNeed2 v ρ2)|.
  \item \textbf{Case} |Lam x e|, |ConApp k xs|: Easy to see for |μ1 = μ2|.
  \item \textbf{Case} |App e x|:
    We can apply the induction hypothesis twice, to both of
    \begin{align*}
      |evalNeed e ρ1 μ1| & = |many (step ev1) (evalNeed (Lam y body) ρ3 μ3)| \\
      |evalNeed body (ext ρ3 y (ρ1 ! x)) μ3| & = |many (step ev2) (evalNeed v ρ2 μ2)|
    \end{align*}
    to show the goal.
  \item \textbf{Case} |Case e alts|: Similar to |App|.
  \item \textbf{Case} |Let x e1 e2|:
    We have |evalNeed (Let x e1 e2) ρ1 μ1 = step Let1 (evalNeed e2 ρ1' μ1')|,
    where |ρ1' := ext ρ1 x (step (Look x) (fetch a1))|, |a1 := nextFree μ1|,
    |μ1' := ext μ1 a1 (memo a1 (evalNeed2 e1 ρ1'))|.
    We have $|a| \not= |a1|$ by a property of |nextFree|, and applying the
    induction hypothesis yields
    |step Let1 (evalNeed e2 ρ1' (ext μ1' a d)) = many (Step ev) (evalNeed v ρ2 μ2)|
    as required.
\end{itemize}
\end{proof}

Now we move on to proving auxiliary lemmas about |persistHeap|.

\begin{lemma}[Heap extension preserves persisted entries]
\label{thm:ext-persist-heap}
Let |αE μ :<->: γE μ = persistHeap μ|.
If |adom d ⊆ dom μ| and $|a| \not∈ |dom μ|$,
then |αE μ d = αE (ext μ a d2) d|.
\end{lemma}
\begin{proof}
By Löb induction.
Since |needd d|, we have |d = Cup (step (Look y) (fetch a1))|
and |a1 ∈ dom μ|.
Let |memo a1 (evalNeed2 e ρ) := μ ! a1 = (ext μ a d2) ! a|.
Then |adom ρ ⊆ dom μ| due to |needheap μ| and the goal follows by the
induction hypothesis:
\begin{align*}
  |αE μ d| & = |Lub (step (Look y) (eval e (αE μ << ρ)))| \\
           & = |Lub (step (Look y) (eval e (αE (ext μ a d2) << ρ))) = αE (ext μ a d2) d|
\end{align*}
\end{proof}

An by-name analysis that is sound \wrt by-need must improve when an expression
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
  Furthermore, let |αE μ :<->: γE μ = persistHeap μ| for all |μ|
  and |βE μ := αE μ . set| the representation function.
  \begin{enumerate}[label=(\alph*),ref=\thelemma.(\alph*)]
    \item
      If   |evalNeed e ρ1 μ1 = many (Step ev) (evalNeed v ρ2 μ2)|
      and  |μ1 ! a = memo a (evalNeed2 e ρ1)|,\\
      then |eval v (βE (ext μ2 a (memo a (evalNeed2 v ρ2))) << ρ2) ⊑ eval e (βE μ2 << ρ1)|.
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

    Then |(βE μ3 << ρ3) ! y = (βE μ1 << ρ1) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:ext-persist-heap},
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
    =   {- Expose fixpoint, rewriting |βE μ3 << ρ3| to |ext (βE μ1 << ρ1) x (βE μ3 (ρ3 ! x))| -}
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

\begin{theorem}[Sound By-need Interpretation]
\label{thm:soundness-by-need}
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT = nameNeed|, as well as |αE μ :<->: γE μ =
persistHeap μ| from \Cref{fig:name-need}.
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

    Then |(βE μ1 << ρ1) ! y = (βE μ << ρ) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:ext-persist-heap},
    and |(βE μ1 << ρ1) ! x = step (Look x) (eval e1 (βE μ1 << ρ1))|.
    \begin{spec}
        βT (evalNeed (Let x e1 e2) ρ μ)
    =   {- Unfold |evalNeed| -}
        βT (bind  (\d1 -> evalNeed2 e1 ρ1) (\d1 -> Step Let1 (evalNeed2 e2 ρ1)) μ)
    =   {- Unfold |bind|, $|a| \not\in |dom μ|$, unfold |βT| -}
        step Let1 (βT (evalNeed e2 ρ1 μ1))
    ⊑   {- Induction hypothesis, unfolding |ρ1| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ) x (βE μ1 (ρ1 ! x))))
    =   {- Expose fixpoint, rewriting |βE μ1 (ρ1 ! x)| to |ext (βE μ << ρ) x (βE μ1 (ρ1 ! x))| using \Cref{thm:ext-persist-heap} -}
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

\end{toappendix}

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
