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
import Abstractions

instance Eq (D (ByName T)) where
  (==) = undefined
instance Ord (D (ByName T)) where
  compare = undefined
powMap :: (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ undefined $ map f $ Set.toList s
set = P . Set.singleton
\end{code}
%endif

\section{Abstract Soundness}
\label{sec:soundness}

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
Then the \emph{collecting semantics} relative to the concrete semantics |eval3
Traces|, defined as |eval3 Collecting e ρ := set (eval3 Traces e ρ)|, provides
the strongest trace property that a given program |(e,ρ)| satisfies.
In this setting, we extend the original Galois connection to the signature of
|eval3 Traces e| \emph{parametrically} (in the sense of \citet{Backhouse:04},
\eg, that the structural properties of a Galois connection follow as a free
theorem), to
\[
  (|(Name :-> pow Traces) -> pow Traces|, |dot (⊆)|)
  \galois{|\f -> α . f . (γ <<)|}{|\(hat f) -> γ . hat f . (α <<)|}
  (|(Name :-> hat D) -> hat D|, |dot (⊑)|)
\]
and state soundness of the abstract semantics |eval3 (hat D)| as
\[
  |eval3 Collecting e ρ ⊆ γ (eval3 (hat D) e (α << set << ρ) :: hat D)|
  \Longleftrightarrow
  |α (set (eval3 Traces e ρ)) ⊑ eval3 (hat D) e (α << set << ρ)|.
\]
The statement should be read as ``The concrete semantics implies the abstract
semantics up to concretisation''~\citet[p. 26]{Cousot:21}.
Proving such a statement is the goal of the following subsections, although we
deviate from the above in the following ways:
(1) |eval3 Traces| and |eval3 (hat D)| are in fact different type class
instantiations of the same denotational interpreter |eval| from
\Cref{sec:interp}, thus both functions share a lot of common structure.
(2) The Galois connection is completely determined by type class instances, even
for infinite traces.
(3) It turns out that we need to syntactically restrict the kind
of |D| that occurs in an environment |ρ| due to a lack of full
abstraction~\citep{Plotkin:77}, so that the final Galois connection looks a bit
different.

Astonishingly, since both the Galois connection \emph{and} the abstract
semantics are fixed by the type class instantiation at |hat D|, we can provide
sufficient soundness criteria \wrt to a concrete by-name instantiation |D
(ByName T)| that are formulated \emph{completely in the abstract}, that is,
without referencing concrete semantics or the Galois connection.
The soundness proof for usage analysis \wrt by-name semantics thus fits on the
back of an envelope.

\subsection{Guarded Fixpoints, Safety Properties and Safety Extension of a Galois Connection}

Suppose for a second that we were only interested in the trace component of our
semantic domain, thus effectively restricting ourselves to
$\Traces \triangleq |T ()|$, and that we were to approximate properties $P ∈
\pow{\Traces}$ about such traces by a Galois connection
$(\pow{\Traces},⊆) \galois{α}{γ} (|hat D|, ⊑)$.
Alas, although the abstraction function |α| is well-defined as a mathematical
function, it most certainly is \emph{not} computable at infinite inputs (in
$\Traces^{\infty}$), for example at
|fix (Step (Lookup x)) = Step (Lookup x) (Step (Lookup x) ...)|!

Computing with such an |α| is of course inacceptable for a \emph{static} analysis.
Usually this is resolved by approximating the fixpoint by the least fixpoint of
the abstracted iteratee, \eg, |lfp (α . Step (Lookup x) . γ)|.
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
approximated by $\bot$ (such as in strictness analysis), thus effectively
assuming that all executions are finite, our framework assumes that the
properties of interest are \emph{safety properties}~\citep{Lamport:77}:

\begin{definition}[Safety property]
A trace property $P ⊆ \Traces$ is a \emph{safety property} iff,
whenever |τ1| violates $P$ (so $|τ1| \not∈ P$), then there exists some proper
prefix $|τ2|$ (written $|τ2| \lessdot |τ1|$) such that $|τ2| \not∈ P$.
\end{definition}

Note that both well-typedness (``|τ| does not go wrong'') and usage cardinality
abstract safety properties.
Conveniently, guarded recursive predicates (on traces) always describe safety
properties~\citep{Spies:21,iris-lecture-notes}.
The contraposition of the above definition is
\[
  \forall |τ1|.\ (\forall |τ2|.\ |τ2| \lessdot |τ1| \Longrightarrow |τ2| ∈ P ∩ \Traces^{*}) \Longrightarrow |τ1| ∈ P ∩ \Traces^{\infty},
\]
and we can exploit safety to extend a finitary Galois connection to infinite
inputs:
\begin{lemmarep}[Safety extension]
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
\end{lemmarep}
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

From now on, we tacitcly assume that all trace properties of interest are safety
properties, and that any Galois connection defined in Haskell has been extended
to infinite traces via \Cref{thm:safety-extension}.
Any such Galois connection can be used to approximate guarded fixpoints via
least fixpoints:

\begin{lemmarep}[Guarded fixpoint abstraction for safety extensions]
\label{thm:guarded-fixpoint-abstraction}
Let |hat D| be a domain with instances for |Trace| and
|Lat|, and let $(\pow{\Traces},⊆) \galois{α}{γ} (|hat D|, ⊑)$ a Galois
connection extended to infinite traces via \Cref{thm:safety-extension}.
Then, for any guarded iteratee |f :: Later Traces -> Traces|,
\[
  |α|(\{ |fix f| \}) ⊑ |lfp (α . powMap f . γ)|,
\]
where |lfp (hat f)| denotes (the least) fixpoint of |hat f| and |powMap f :: pow (Later Traces) -> pow
Traces| is the lifting of |f| to powersets.
\end{lemmarep}
\begin{proof}
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

\subsection{Soundness \wrt |D (ByName T)|}

What is required of an abstract instantiation |hat D| of |eval| to prove it
sound \wrt the by-name interpretation |D (ByName T)|?
Not much, it turns out: \Cref{fig:by-name-soundness-lemmas} lists sufficient
soundness conditions on the type class instances of |hat D|.
While the inference rules have considerable syntactic complexity, most
complexity is in the \emph{premises}.
For a preliminary reading the premises can be ignored, but they are crucial
for clients to be able to conduct their proofs.

As we are getting closer to the point where we reason about idealised,
total Haskell code, it is important to nail down how Galois connections are
represented in Haskell, and how we construct them.
Following \citet[Section 4.3]{Nielson:99}, every \emph{representation function}
|β :: a -> b| into a partial order $(|b|,⊑)$ yields a Galois connection between
|Pow|ersets of |a| $(|Pow a|,⊆)$ and $(|b|,⊑)$:
\begin{code}
data GC a b = (a -> b) :<->: (b -> a)
repr :: Lat b => (a -> b) -> GC (Pow a) b
repr β = α :<->: γ where α (P as) = Lub (β a | a <- as); γ b = P (setundef (a | β a ⊑ b))
\end{code}
(While the |γ| exists as a mathematical function, it is in general impossible to
compute even for finitary inputs.)
Every domain |hat D| with instances |(Trace (hat D), Domain (hat D), Lat (hat D))|
induces a \emph{trace abstraction} |trace| via the following representation
function, writing |powMap f| to map |f| over |Pow|
\begin{code}
type NameD d = d
trace  ::  (Trace (hat d), Domain (hat d), Lat (hat d))
       =>  GC (Pow (D r)) (hat d) -> GC (Pow (NameD (D r))) (NameD (hat d)) -> GC (Pow (T (Value r))) (hat d)
trace (αT :<->: γT) (αE :<->: γE) = repr β where
  β (Ret Stuck)       = stuck
  β (Ret (Fun f))     = fun {-"\iffalse"-}""{-"\fi"-} (αT . powMap f . γE)
  β (Ret (Con k ds))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)
  β (Step e (hat d))        = step e (β (hat d))
\end{code}
Note how |trace| expects two Galois connections: The first one is applicable
in the ``recursive case'' and the second one applies to (the powerset over)
|NameD (D (ByName T))|, a subtype of |D (ByName T)|.
Every |d :: NameD (ByName T)| is of the form |Step (Lookup x) (eval e ρ)| for
some |x|, |e|, |ρ|, characterising domain elements that end up in an
environment or are passed around as arguments or in fields.
We have seen a similar characterisation in the Agda encoding of
\Cref{sec:adequacy}.
The distinction between |αT| and |αE| will be important for proving that
evaluation improves trace abstraction, a necessary auxiliary lemma for
\Cref{thm:soundness-by-name}.

We utilise the |trace| combinator to define |byName| abstraction as its
(guarded) fixpoint:
\begin{code}
env :: (Trace (hat d), Domain (hat d), HasBind (hat d), Lat (hat d)) => GC (Pow (NameD (D (ByName T)))) (NameD (hat d))
env = untyped (repr β where β (Step (Lookup x) (eval e ρ)) = step (Lookup x) (eval e (β << ρ)))

byName :: (Trace (hat d), Domain (hat d), HasBind (hat d), Lat (hat d)) => GC (Pow (D (ByName T))) (hat d)
byName = (αT . powMap unByName) :<->: (powMap ByName . γT) where αT :<->: γT = trace byName env
\end{code}
There is a need to clear up the domain and range of |env|.
Since its domain is sets of elements from |NameD (D (ByName T))|, its range
|NameD d| is the (possibly infinite) join over abstracted elements that
look like |step (Lookup x) (eval e (β << ρ))| for some ``closure'' |x|, |e|, |ρ|.
Although we have ``sworn off'' operational semantics for abstraction, we
defunctionalise environments into syntax to structure the vast semantic domain
in this way, thus working around matters of full abstraction~\citep{Plotkin:77}.
More formally,

\begin{definition}[Syntactic by-name environments]
  Let |hat D| be a domain satisfying |Trace|, |Domain|, |HasBind| and |Lat|.
  We write |named (hat D) d| (resp. |nameenv (hat D) ρ|) to say that the
  denotation |d| (resp. environment |ρ|) is \emph{syntactic}, which we define
  by mutual guarded recursion as
  \begin{itemize}
    \item |named (hat D) d| iff |d| is of the form |Lub (step (Lookup x) (eval e ρ1 :: (hat D)) || Later (named (hat D) ρ1))|, and
    \item |nameenv (hat D) ρ| iff for all |x|, |named (hat D) (ρ ! x)|.
  \end{itemize}
\end{definition}
% We really need to generalise over |D|, because we need this characterisation in the abstract as well.

For the remainder of this Subsection, we assume a refined definition of |Domain|
and |HasBind| that expects |named (hat D)| (denoting the set of
|hat d :: hat D| such that |named (hat D) (hat d)|) where we pass around
denotations that end up in an environment, and we will write |named (hat D)| in
place of |NameD (hat D)|.
It is then easy to see that |eval e ρ| preserves |nameenv (hat D)| in recursive
invocations, and |trace| does so as well.

\begin{figure}
  \[\begin{array}{c}
    \inferrule[\textsc{Mono}]{|hat d1 ⊑ hat d2| \\ |hat f1 ⊑ hat f2|}{%
      |apply (hat f1) (hat d1) ⊑ apply (hat f2) (hat d2)|%
      \textit{ and so on, for all methods of |Trace|, |Domain|, |HasBind|}} \\
    \\[-0.5em]
    \inferrule[\textsc{Step-App}]{}{%
      |step ev (apply (hat d) (hat a)) ⊑ apply (step ev (hat d)) (hat a)|} \qquad
    \inferrule[\textsc{Step-Sel}]{}{%
      |step ev (select (hat d) (hat alts)) ⊑ select (step ev (hat d)) (hat alts)|} \\
    \\[-0.5em]
    \inferrule[\textsc{Unwind-Stuck}]{}{%
      \textstyle|stuck ⊑ Lub (apply stuck (hat a), select stuck (hat alts))|} \hspace{1.5em}
    \inferrule[\textsc{Intro-Stuck}]{}{%
      \textstyle|stuck ⊑ Lub (apply (con k (hat ds)) (hat a), select (fun (hat f)) (hat alts))|} \\
    \\[-0.5em]
    \inferrule[\textsc{Beta-App}]{%
      |hat f (hat d) = step App2 (eval e (ext (hat ρ) x (hat d)))|}{%
      |hat f (hat a) ⊑ apply (fun (hat f)) (hat a)|} \qquad
    \inferrule[\textsc{Beta-Sel}]{\begin{minipage}[c]{0.6\textwidth}{%
      \begin{spec}
        (hat alts ! k) (hat ds)  |  len (hat ds) /= len (xs)  = stuck
                                 |  otherwise                 = step Case2 (eval er (exts (hat ρ) xs (hat ds)))
      \end{spec}}\end{minipage}}{%
      |(hat alts ! k) (map (hat ρ1 !) ys) ⊑ select (con k (map (hat ρ1 !) ys)) (hat alts)|} \\
    \\[-0.5em]
    \inferrule[\textsc{Bind-ByName}]{|hat rhs (hat d1) = eval e1 (ext (hat ρ) x (step (Lookup x) (hat d1)))|\\ |hat body (hat d1) = step Let1 (eval e2 (ext (hat ρ) x (hat d1)))|}{|(hat body) (lfp (hat rhs)) ⊑ bind (hat rhs) (hat body)|}
  \end{array}\]
  \caption{By-name soundness lemmas}
  \label{fig:by-name-soundness-lemmas}
\end{figure}

\begin{toappendix}
\begin{lemma}[Monotonicity]
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying property \textsc{Mono} in
  \Cref{fig:by-name-soundness-lemmas}.
  Then |eval e :: (Name :-> hat D) -> hat D| is a monotone function.
\end{lemma}
\begin{proofsketch}
  Follows by parametricity.
\end{proofsketch}

\begin{lemmarep}[By-name evaluation improves trace abstraction]
  \label{thm:eval-improves}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the soundness properties \textsc{Step-App},
  \textsc{Step-Sel}, \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName}
  in \Cref{fig:by-name-soundness-lemmas}.

  If |eval e ρ1 = many (Step ev) (eval v ρ2)|,
  then |many (step ev) (eval v (αE << set << ρ2)) ⊑ eval e (αE << set << ρ1)|,
  where |αE :<->: γE = env|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    |eval x ρ1 = Step (Lookup y) (eval e' ρ3) = many (Step ev) (eval v ρ2)|
    for some |y|, |e'|, |ρ3|,
    so that |many ev = Lookup y : many ev1| for some |ev1| by determinism.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    =   {- |many ev = Lookup y : many ev1| -}
        step (Lookup y) (many (step ev1) (eval v (βE << ρ2)))
    ⊑   {- Induction hypothesis at |ev1|, |ρ3| as above -}
        step (Lookup y) (eval e' (βE << ρ3))
    =   {- Refold |βE|, |ρ3 ! x| -}
        βE (ρ1 ! x)
    =   {- Refold |eval x (βE << ρ1)| -}
        eval x (βE << ρ1)
    \end{spec}
  \item \textbf{Case} |Lam|, |ConApp|: By reflexivity of $⊑$.
  \item \textbf{Case} |App e x|:
    Then |eval e ρ1 = many (Step ev1) (eval (Lam y body) ρ3)|,
    |eval body (ext ρ3 y (ρ1 ! x)) = many (Step ev2) (eval v ρ2)|.
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
    Then |eval e ρ1 = many (Step ev1) (eval (ConApp k ys) ρ3)|,
    |eval er (exts ρ1 xs (map (ρ3 !) ys)) = many (Step ev2) (eval v ρ2)|,
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
        step Let1 (eval e2 (ext (βE << ρ1) x (βE (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ1 x (step (Lookup x) d1))))))))
    =   {- Partially roll |fix| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (βE (fix (\d1 -> step (Lookup x) (eval e1 (ext ρ1 x d1)))))))
    ⊑   {- \Cref{thm:guarded-fixpoint-abstraction} -}
        step Let1 (eval e2 (ext (βE << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE << ρ1) x (αE (γE (hat d1)))))))))
    ⊑   {- |αE . γE ⊑ id| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE << ρ1) x (hat d1)))))))
    =   {- Partially unroll |lfp| -}
        step Let1 (eval e2 (ext (βE << ρ1) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (βE << ρ1) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName} -}
        bind  (\(hat d1) -> eval e1 (ext ((βE << ρ1)) x (step (Lookup x) (hat d1))))
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE << ρ1)) x (step (Lookup x) (hat d1)))))
    =   {- Refold |eval (Let x e1 e2) (βE << ρ1)| -}
        eval (Let x e1 e2) (βE << ρ1)
    \end{spec}
\end{itemize}
\end{proof}
\end{toappendix}

We can finally prove the following soundness theorem:

\begin{theoremrep}[Sound By-name Interpretation]
\label{thm:soundness-by-name}
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT := byName|, |αE :<->: γE := env|.
If the soundness lemmas in \Cref{fig:by-name-soundness-lemmas} hold,
then |eval| instantiates at |hat D| to an abstract interpreter that is sound
\wrt |γE -> αT|, that is,
\[
  |αT (eval e ρ :: Pow (D (ByName T))) ⊑ (eval e (αE << ρ) :: hat D)|.
\]
\end{theoremrep}
\begin{proof}
We first simplify our proof obligation by assuming, without loss of generality,
that |ρ| only maps into singleton sets, henceforth interpreting |ρ| in |Name :->
D (ByName T)|.
This is not losing generality as any other |ρ1| can be represented
as the (pointwise) join over a potentially infinite set of such singleton |ρ|s,
in which case we have
\[
  |αT (eval e ρ1 :: Pow (D (ByName T))) = Lub (βT (eval e ρ :: D (ByName T)) || (set << ρ) `subseteqdot` ρ1)|,
\]
where |βT := αT . set| is the |repr|esentation function used to define |αT|.
|eval e (αE << ρ1) :: hat D| is an upper bound to the left-hand side if and only
if it is an upper bound on each element of the set on the right,
\[
  \forall |ρ|.\ |((set << ρ) `subseteqdot` ρ1) ==> βT (eval e ρ) ⊑ eval e (αE << ρ1)|.
\]
Clearly this is implied by the simplified correctness proposition
\[
  \forall |ρ|.\ |βT (eval e ρ :: D (ByName T)) ⊑ (eval e (βE << ρ) :: hat D)|,
\]
which we will prove by Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |αT|.
    Otherwise,
    \begin{spec}
        βT (ρ ! x)
    =   {- |nameenv (Pow (D (ByName T))) (set << ρ)|, Unfold |βT| -}
        step (Lookup y) (βT (eval e' ρ'))
    ⊑   {- Induction hypothesis -}
        step (Lookup y) (eval e' (βE << ρ'))
    =   {- Refold |βE| -}
        βE (ρ ! x)
    \end{spec}
  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        βT (eval (Lam x body) ρ)
    =   {- Unfold |eval|, |βT| -}
        fun (\(hat d) -> Lub (step App2 (βT (eval body (ext ρ x d))) | βE d ⊑ hat d))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> Lub (step App2 (eval body (βE << (ext ρ x d))) | βE d ⊑ hat d))
    ⊑   {- Least upper bound / |αE . γE ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext ((βE << ρ)) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k ds|:
    \begin{spec}
        βT (eval (ConApp k xs) ρ)
    =   {- Unfold |eval|, |βT| -}
        con k (map ((βE << ρ) !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    The stuck case follows by unfolding |βT|.

    Our proof obligation can be simplified as follows
    \begin{spec}
        βT (eval (App e x) ρ)
    =   {- Unfold |eval|, |βT| -}
        step App1 (βT (apply (eval e ρ) (ρ ! x)))
    =   {- Unfold |apply| -}
        step App1 (βT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    ⊑   {- By cases, see below -}
        step App1 (apply (eval e (βE << ρ)) ((βE << ρ) ! x))
    =   {- Refold |eval| -}
        eval (App e x) (βE << ρ)
    \end{spec}

    When |eval e ρ| diverges, we have
    \begin{spec}
    =   {- |eval e ρ| diverges, unfold |βT| -}
        step ev1 (step ev2 (...))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (step ev1 (step ev2 (...))) ((βE << ρ) ! x)
    =   {- Refold |βT|, |eval e ρ| -}
        apply (βT (eval e ρ)) ((βE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}
    Otherwise, |eval e ρ| must produce a value |v|.
    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
    (resp. |d := con k (map βE ds)|) and have
    \begin{spec}
        βT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |βT| -}
        many (step ev) (βT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v| not |Fun|, unfold |βT| -}
        many (step ev) stuck
    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map βT ds)| -}
        many (step ev) (apply d a)
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) d) ((βE << ρ) ! x)
    =   {- Refold |βT|, |eval e ρ| -}
        apply (βT (eval e ρ)) ((βE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}
    In the final case, we have |v = Fun f|, which must be the result of some
    call |eval (Lam y body) ρ1|; hence
    |f := \d -> step App2 (eval body (ext ρ1 y d))|.
    \begin{spec}
        βT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |βT| -}
        many (step ev) (βT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v=Fun f|, with |f| as above; unfold |βT| -}
        many (step ev) (step App2 (βT (eval body (ext ρ1 y (ρ ! x)))))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step App2 (eval body (βE << (ext ρ1 y (ρ ! x)))))
    =   {- Rearrange -}
        many (step ev) (step App2 (eval body (ext (βE << ρ1) y ((βE << ρ) ! x))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        many (step ev) (apply (eval (Lam y body) (βE << ρ1)) ((βE << ρ) ! x))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) (eval (Lam y body) (βE << ρ1))) ((βE << ρ) ! x)
    ⊑   {- \Cref{thm:eval-improves} applied to |many ev| -}
        apply (eval e (βE << ρ)) ((βE << ρ) ! x)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The stuck case follows by unfolding |βT|.
    When |eval e ρ| diverges or does not evaluate to |eval (ConApp k ys) ρ1|,
    the reasoning is similar to |App e x|, but in a |select| context.
    So assume that |eval e ρ = many (step ev) (eval (ConApp k ys) ρ1)| and that
    there exists |((cont << alts) ! k) ds = step Case2 (eval er (exts ρ xs ds))|.
    \begin{spec}
        βT (eval (Case e alts) ρ)
    =   {- Unfold |eval|, |βT| -}
        step Case1 (βT (select (eval e ρ) (cont << alts))
    =   {- Unfold |select| -}
        step Case1 (βT (eval e ρ >>= \case Con k ds | k ∈ dom alts -> ((cont << alts) ! k) ds))
    =   {- |eval e ρ = many (step ev) (eval (ConApp k ys) ρ1)|, unfold |βT| -}
        step Case1 (many (step ev) (βT (eval (ConApp k ys) ρ1) >>= \case Con k ds | k ∈ dom (cont << alts) -> ((cont << alts) ! k) ds))
    =   {- Simplify |return (Con k ds) >>= f = f (Con k ds)|, |(cont << alts) ! k| as above -}
        step Case1 (many (step ev) (βT (step Case2 (eval er (exts ρ xs (map (ρ1 !) ys))))))
    =   {- Unfold |βT| -}
        step Case1 (many (step ev) (step Case2 (βT (eval er (exts ρ xs (map (ρ1 !) ys))))))
    ⊑   {- Induction hypothesis -}
        step Case1 (many (step ev) (step Case2 (eval er (exts (βE << ρ) xs (map ((βE << ρ1) !) ys)))))
    =   {- Refold |cont| -}
        step Case1 (cont (alts ! k) (map ((βE << ρ1) !) xs))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev) (select (eval (ConApp k ys) (βE << ρ1)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (many (step ev) (eval (ConApp k ys) (βE << ρ1))) (cont << alts))
    ⊑   {- \Cref{thm:eval-improves} applied to |many ev| -}
        step Case1 (select (eval e (βE << ρ)) (cont << alts))
    =   {- Refold |eval| -}
        eval (Case e alts) (βE << ρ)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        βT (eval (Let x e1 e2) ρ)
    =   {- Unfold |eval| -}
        βT (bind  (\d1 -> eval e1 (ext ρ x (Step (Lookup x) d1)))
                  (\d1 -> Step Let1 (eval e2 (ext ρ x (Step (Lookup x) d1)))))
    =   {- Unfold |bind|, |βT| -}
        step Let1 (βT (eval e2 (ext ρ x (Step (Lookup x) (fix (\d1 -> eval e1 (ext ρ x (Step (Lookup x) d1))))))))
    ⊑   {- Induction hypothesis -}
        step Let1 (eval e2 (ext (βE << ρ) x (βE (Step (Lookup x) (fix (\d1 -> eval e1 (ext ρ x (Step (Lookup x) d1))))))))
    \end{spec}
    And from hereon, the proof is identical to the |Let| case of
    \Cref{thm:eval-improves}:
    \begin{spec}
    ⊑   {- By \Cref{thm:guarded-fixpoint-abstraction}, as in the proof for \Cref{thm:eval-improves} -}
        step Let1 (eval e2 (ext (βE << ρ) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (βE << ρ) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = βE << ρ| -}
        bind  (\d1 -> eval e1 (ext (βE << ρ) x (step (Lookup x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (βE << ρ) x (step (Lookup x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βE << ρ)| -}
        eval (Let x e1 e2) (βE << ρ)
    \end{spec}
\end{itemize}
\end{proof}

A delightful consequence of fixing |byName| as the Galois connection for the
soundness statement is that many soundness lemmas, such as
|αT (step ev d) ⊑ step ev (αT d)| or |αT (fun f) ⊑ fun (αT . f . γE)|
follow by definition.
\sg{We could connect |αT (eval e ρ1 :: Pow (D (ByName T)))| here to the
semantic usage abstraction in \Cref{sec:abstractions}}

To show that the decomposition into 11 remaining lemmas is useful, we will now
bring the soundness proof for usage analysis, \emph{in full}:

\begin{theorem} Usage analysis as specified by |UD| in \Cref{fig:abs-usg}
is sound \wrt |D (ByName T)|, that is,
\[
  |αT (eval e ρ :: Pow (D (ByName T))) ⊑ (eval e (αE << ρ) :: UD) where αT :<->: _ = byName; αE :<->: _ = env|
\]
\end{theorem}
\begin{proof}
It suffices to show the soundness lemmas in \Cref{fig:by-name-soundness-lemmas}.
\begin{itemize}
  \item \textsc{Mono}:
    Always immediate, since |⊔| and |+| are the only functions matching on |U|,
    and these are monotonic.
  \item \textsc{Unwind-Stuck}, \textsc{Intro-Stuck}:
    Trivial, since |stuck = bottom|.
  \item \textsc{Step-App}, \textsc{Step-Sel}:
    Follows by unfolding |step|, |apply|, |select|, |>>| and associativity of |+|.
  \item \textsc{Beta-App}:
    Follows by unfolding |apply| and |fun| and applying \Cref{thm:usage-squeezing}.
  \item \textsc{Beta-Sel}:
    Follows by unfolding |select| and |con| and applying
    \Cref{thm:usage-squeezing} multiple times.
  \item \textsc{Bind-ByName}:
    |kleeneFix| approximates the least fixpoint |lfp| since the iteratee is
    monotone and |UD| is finite.
\end{itemize}
\end{proof}

Building on the ``substitution'' \Cref{thm:usage-squeezing}, this proof is
delightfully simple.
The main lemmas \textsc{Beta-App} and \textsc{Beta-Sel} encode soundness of
the summary mechanism and hence appeal to \Cref{thm:usage-squeezing}, while the
proof for \textsc{Bind-ByName} governs sound fixpoint approximation.

Note that in order to appeal to \Cref{thm:usage-squeezing}, we really need the
syntactic premises in \Cref{fig:by-name-soundness-lemmas}.
It would not be possible to show |hat f (hat a) ⊑ apply (fun (hat f)) (hat a)|
for any monotone |hat f| due to the lack of full abstraction, and likewise for
\textsc{Beta-Sel}.
\sg{Bring this earlier! Perhaps even in \Cref{sec:abstractions}.}
For example,
\begin{center}
\begin{spec}
  hat f (Uses φ _) := if φ ! x ⊑ 0 then nopD else step (Lookup z) nopD
\end{spec}
\end{center}
defines a monotone |hat f| that violates \textsc{Beta-App}
(abbreviating |look x := step (Lookup x)|):
\begin{center}
\begin{spec}
 hat f (look x nopD) = look z nopD {-" \not⊑ "-} manify (look x nopD) = apply (fun (hat f)) (look x nopD)
\end{spec}
\end{center}

\subsection{Sound By-Need Abstraction}

\sg{Here be dragons. This is work-in-progress, don't expect to understand anything of it.}

\begin{definition}[Syntactic by-need heaps and environments, address domain]
  \label{defn:syn-heap}
  We write |needenv ρ| (resp. |needheap μ|) to say that the by-need
  environment |ρ :: Name :-> Pow (D (ByNeed T))| (resp. by-need heap |μ|) is
  \emph{syntactic}, defined by mutual guarded recursion as
  \begin{itemize}
    \item |needd d| iff |d = Cup (step (Lookup y) (fetch a))|.
    \item |needenv ρ| iff for all |x|, |needd (ρ ! x)|.
    \item |adom d := set (a || step (Lookup y) (fetch a) ∈ ρ ! x)|
    \item |adom ρ := Cup (adom (ρ ! x) || x ∈ dom ρ)|.
    \item |needheap μ| iff for all |a|, |μ ! a = Cup (memo a (eval e ρ) || Later (needenv ρ && adom ρ ⊆ dom μ))|.
  \end{itemize}
  We refer to |adom d| (resp. |adom ρ|) as the \emph{address domain} of |d| (resp. |ρ|).
\end{definition}

For an analysis that approximates lazy heaps in an interesting way, there might
be merit in inlining |fetch a := \μ -> (μ ! a)(μ)| so as to parameterise
\Cref{defn:syn-heap} over the domain, but for our by-name analyses that is
unnecessary.

As before, for the remainder of this Subsection we assume that all concrete
environments and heaps satisfy |needenv| resp. |needheap|.
It is easy to see that syntacticness is preserved by |eval| whenever environment
or heap is extended, assuming that |Domain| and |HasBind| are adjusted
accordingly.

Thus we proceed to define the following evaluation relation on (syntactic) heaps:
\[\begin{array}{c}
  \ruleform{ μ_1 \progressto μ_2 }
  \\ \\[-0.5em]
  \inferrule[\textsc{$\progressto$-Refl}]{|needheap μ|}{|μ ~> μ|}
  \qquad
  \inferrule[\progresstotrans]{|μ1 ~> μ2| \quad |μ2 ~> μ3|}{|μ1 ~> μ3|}
  \qquad
  \inferrule[\progresstoext]{|a| \not∈ |dom μ| \quad |adom ρ ⊆ dom μ ∪ set a|}{|μ ~> ext μ a (memo a (eval e ρ))|}
  \\ \\[-0.5em]
  \inferrule[\progresstomemo]{|μ1 ! a = memo a (eval e ρ1)| \quad |Later (eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2))|}{|μ1 ~> ext μ2 a (memo a (eval v ρ2))|}
  \\[-0.5em]
\end{array}\]

Transitivity and reflexivity of $(\progressto)$ are definitional.
Antisymmetry is not so simple to show for a lack of full abstraction.

(TODO: Perhaps we could gain define a coarser equivalence relation on heaps that
only compares heap entries on any more progressive entries, but that is still a
far cry from being fully abstract. Don't want to go there!
So perhaps it's just antisymmetry modulo contextual equivalence; fair enough.)

TODO: See if we need the following lemma
\begin{lemmarep}
\label{thm:progression-allocates}
If |μ1 ~> μ2|, then |dom μ1 ⊆ dom μ2|.
\end{lemmarep}
\begin{proof}
Simple proof by induction after realising that |eval| never deletes heap
entries.
\end{proof}

\begin{lemmarep}[Update once]
\label{thm:update-once}
If   |μ1 ~> μ2| and |μ1 ! a = memo a (eval v ρ)|,
then |μ2 ! a = memo a (eval v ρ)|.
\end{lemmarep}
\begin{proof}
Simple proof by induction on |μ1 ~> μ2|.
The only case updating a heap entry is \progresstomemo, and there we can see
that |μ2 ! a = memo (eval v ρ)| because evaluating |v| in |μ1| does not make
a step.
\end{proof}

\begin{lemmarep}[Evaluation progresses the heap]
\label{thm:eval-progression}
If |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|, then |μ1 ~> μ2|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    Let |many ev1 := tail (init (many ev))|.
    \begin{spec}
        (ρ1 ! x) μ1
    =   {- |needenv ρ1|, some |y|, |a| -}
        Step (Lookup y) (fetch a μ1)
    =   {- Unfold |fetch| -}
        Step (Lookup y) ((μ1 ! a) μ1)
    =   {- |needheap μ|, some |e|, |ρ3| -}
        Step (Lookup y) (memo a (eval e ρ3 μ1))
    =   {- Unfold |memo| -}
        Step (Lookup y) (eval e ρ3 μ1 >>= upd)
    =   {- |eval e ρ3 μ1 = many (Step ev1) (eval v ρ2 μ3)| for some |μ3| -}
        Step (Lookup y) (many (Step ev1) (eval v ρ2 μ3 >>= \v μ3 -> Step Update (Ret (v, ext μ3 a (memo a (return v))))))
    \end{spec}
    Now let |sv :: Value (ByNeed T)| be the semantic value such that |eval v ρ2 μ3 = Ret (sv, μ3)|.
    \begin{spec}
    =   {- |eval v ρ2 μ3 = Ret (sv, μ3)| -}
        Step (Lookup y) (many (Step ev1) (Step Update (Ret (sv, ext μ3 a (memo a (return sv))))))
    =   {- Refold |eval v ρ2|, |many ev = [Lookup y] ++ many ev1 ++ [Update]| -}
        many (Step ev) (eval v ρ2 (ext μ3 a (memo a (eval v ρ2))))
    =   {- Determinism of |eval|, assumption -}
        many (Step ev) (eval v ρ2 μ2)
    \end{spec}
    We have
    \begin{align}
      & |μ1 ! a = memo a (eval e ρ3)| \label{eqn:eval-progression-memo} \\
      & |Later (eval e ρ3 μ1 = many (Step ev1) (eval v ρ2 μ3))| \label{eqn:eval-progression-eval} \\
      & |μ2 = ext μ3 a (memo a (eval v ρ2))| \label{eqn:eval-progression-heaps}
    \end{align}
    We can apply rule \progresstomemo to \Cref{eqn:eval-progression-memo} and \Cref{eqn:eval-progression-eval}
    to get |μ1 ~> ext μ3 a (memo a (eval v ρ2))|, and rewriting along
    \Cref{eqn:eval-progression-heaps} proves the goal.
  \item \textbf{Case} |Lam x body|, |ConApp k xs|:
    Then |μ1 = μ2| and the goal follows by \progresstorefl.
  \item \textbf{Case} |App e1 x|:
    Let us assume that |eval e1 ρ1 μ1 = many (Step ev1) (eval (Lam y e2) ρ3 μ3)| and
    |eval e2 (ext ρ3 y (ρ ! x)) μ3 = many (Step ev2) (eval v ρ2 μ2)|, so that
    |μ1 ~> μ3|, |μ3 ~> μ2| by the induction hypothesis.
    The goal follows by \progresstotrans, because
    |many ev = [App1] ++ many ev1 ++ [App2] ++ many ev2|.
  \item \textbf{Case} |Case e1 alts|:
    Similar to |App e1 x|.
  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        eval (Let x e1 e2) ρ1 μ1
    =   {- Unfold |eval| -}
        bind  (\d1 -> eval e1 (ext ρ1 x (step (Lookup x) d1)))
              (\d1 -> step Let1 (eval e2 (ext ρ1 x (step (Lookup x) d1))))
              μ1
    =   {- Unfold |bind|, some $|a| \not\in |dom μ|$ -}
        step Let1 (eval e2 (ext ρ1 x (step (Lookup x) (fetch a))) (ext μ1 a (memo a (eval e1 (ext ρ1 x (step (Lookup x) (fetch a)))))))
    \end{spec}
    At this point, we can apply the induction hypothesis to |eval e2 (ext ρ1 x
    (step (Lookup x) (fetch a)))| to conclude that
    |ext μ1 a (memo a (eval e1 (ext ρ1 x (step (Lookup x) (fetch a))))) ~> μ2|.

    On the other hand, we have
    |μ1 ~> ext μ1 a (memo a (eval e1 (ext ρ1 x (step (Lookup x) (fetch a)))))|
    by rule \progresstoext (note that $|a| \not∈ |dom μ|$), so the goal follows
    by \progresstotrans.
\end{itemize}
\end{proof}

\Cref{thm:eval-progression} exposes in \progresstomemo nested structure:
for example, if |μ1 ~> ext μ2 a (memo a (eval v ρ2))| is the result of applying
rule \progresstomemo, then we obtain a proof that the memoised expression
|eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|, and this evaluation in turn
implies that |μ1 ~> μ2|.

% Can't prove the following lemma:
%\begin{lemmarep}
%If |μ1 ~> μ2| by \progresstomemo,
%then also |ext μ2 a (μ1 ! a) ~> μ2| for the updated |a ∈ dom μ1|.
%\end{lemmarep}
%\begin{proof}
%By rule inversion, we have |μ1 ! a = memo a (eval e ρ1)|
%and |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 (ext μ2 a (memo a (eval e ρ1)))|
%for some |e|, |ρ1|, |v|, |ρ2|.
%Then
%|eval x (ext emp x (step (Lookup x) (fetch a))) μ1 = step (Lookup x) (many (step ev) (step Update (eval v ρ2 μ2)))|,
%hence by \Cref{thm:eval-progression} |μ1 ~> μ2|.
%\end{proof}

\begin{corollary}
  $(\progressto)$ is a preorder.
\end{corollary}

For the next lemma, we need to identify heaps modulo $α$, \ie, \emph{readressing},
in the following sense: $|μ1| =_α |μ2|$ iff there exists a permutation |σ ::
Addr -> Addr| such that |heap σ μ1 = μ2|, where
\begin{center}
\begin{spec}
  heap σ μ  = [ σ a ↦ memo (σ a) (eval e (env σ ρ)) | memo a (eval e ρ) <- μ ]
  env σ ρ   = [ x ↦ step (Lookup y) (fetch (σ a)) | step (Lookup y) (fetch a) <- ρ ]
\end{spec}
\end{center}
\noindent
We will make use of the overloaded notation |σ μ := heap σ μ|, |σ ρ := env σ ρ|
for convenience.

\sg{I think we can show antisymmetry and confluence modulo readressing,
compensating for the deterministic allocator that is |nextFree|. I don't plan
to prove that, though.}

\begin{lemmarep}[Congruence modulo readdressing]
\label{thm:eval-perm}
Let |σ1 :: dom μ1 -> dom μ1| be a permutation.
If   |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|,
then there exists a permutation |σ2 :: dom μ2 -> dom μ2|
such that |forall a ∈ dom μ1. σ1 a = σ2 a|
and |eval e (σ1 ρ1) (σ1 μ1) = many (Step (σ1 ev)) (eval v (σ2 ρ2) (σ2 μ2))|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    It is |σ1 ρ1 ! x = step (Lookup y) (fetch (σ1 a))|
    and   |σ1 μ1 ! σ1 a = memo (σ1 a) (eval e1 (σ1 ρ3))|,
    so |eval x (σ1 ρ1) (σ1 μ1) = Step (Lookup y) (memo (σ1 a) (eval e1 (σ1 ρ3)) (σ1 μ1))|.
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

From now on we identify heaps and ambient environments modulo readressing.
Furthermore, let |μ `oplus` μ'| denote the disjoint extension of |μ| with
the bindings in |μ'| (each of which may scope over |μ| and thus |μ'| is not a
realisable heap).

\begin{lemmarep}[Frame rule]
% Currently dead, but nevertheless interesting
If   |adom ρ1 ⊆ dom μ1|,
then |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
if and only if |eval e ρ1 (μ1 `oplus` μ') = many (Step ev) (eval v ρ2 (μ2 `oplus` μ'))|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
     It is |eval x ρ1 μ1 = Step (Lookup y) (memo a (eval e1 ρ3 μ1))| for the
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

We now define the key abstraction function that allows us to use a by-name
analysis for by-need:

\begin{code}
freezeHeap  ::  (Trace d, Domain d, HasBind d, Lat d)
           =>  Heap (ByNeed T) -> GC (needd ) (named d)
freezeHeap μ = untyped (repr β where
  β (step (Lookup x) (fetch a)) | memo a (eval e ρ) <- μ ! a = step (Lookup x) (eval e (β << ρ)))
\end{code}

|freezeHeap| takes as input a heap |μ| the contents of which are used to
``freeze'' a by-need environment into an abstract by-name environment.
For a by-name analysis to be re-used as a by-need analysis, we need this
abstraction function to be antitone in the heap progression relation, \eg,
|μ1 ~> μ2 ==> α μ2 ρ ⊑ α μ1 ρ|.
(TODO: Perhaps it even is a GC, but I don't think we need that. Besides, that would need asymmetry.)

\begin{lemmarep}
\label{thm:freeze-heap-eq}
If |forall a ∈ adom d. μ1 ! a = μ2 ! a|,
then |αE μ1 d = αE μ2 d|, where |αE μ :<->: γE μ = freezeHeap μ|.
\end{lemmarep}
\begin{proof}
By Löb induction.
Since |needd d|, we have |d = Cup (step (Lookup y) (fetch a))|.
Let |memo a (eval e ρ) := μ1 ! a = μ2 ! a|.
Then |adom ρ ⊆ dom μi| due to |needheap μi| and the goal follows by the
induction hypothesis:
\[
  |αE μ1 d = Lub (step (Lookup y) (eval e (αE μ1 << ρ))) = Lub (step (Lookup y) (eval e (αE μ2 << ρ))) = αE μ2 d|
\]
\end{proof}

\begin{lemmarep}[No update implies semantic irrelevance]
\label{thm:no-update-irrelevance}
If |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
and |μ1 ! a = μ2 ! a = memo a (eval e1 ρ3)|, |e1| not a value,
then |eval e ρ1 (ext μ1 a d) = many (Step ev) (eval v ρ2 (ext μ2 a d))|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
     It is |eval x ρ1 μ1 = Step (Lookup y) (memo a1 (eval e1 ρ3 μ1))| for the
     suitable |a1|,|y|.
     Furthermore, it must be $|a| \not= |a1|$, because otherwise, |memo a| would
     have updated |a| with |eval v ρ2|.
     Then we also have |eval x ρ1 (ext μ1 a d) = Step (Lookup y) (memo a1 (eval e1 ρ3 (ext μ1 a d)))|.
     The goal follows from applying the induction hypothesis and realising that
     |μ2 ! a1| has been updated consistently with |memo a1 (eval v ρ2)|.
  \item \textbf{Case} |Lam x e|, |ConApp k xs|: Easy to see for |μ1 = μ2|.
  \item \textbf{Case} |App e x|:
    We can apply the induction hypothesis twice,
    to     |eval e ρ1 μ1 = many (step ev1) (eval (Lam y body) ρ3 μ3)|
    and to |eval body (ext ρ3 y (ρ1 ! x)) μ3 = many (step ev2) (eval v ρ2 μ2)|
    to show the goal.
  \item \textbf{Case} |Case e alts|: Similar to |App|.
  \item \textbf{Case} |Let x e1 e2|:
    We have |eval (Let x e1 e2) ρ1 μ1 = step Let1 (eval e2 ρ1' μ1')|,
    where |ρ1' := ext ρ1 x (step (Lookup x) (fetch a1))|, |a1 := nextFree μ1|,
    |μ1' := ext μ1 a1 (memo a1 (eval e1 ρ1'))|.
    We have $|a| \not= |a1|$ by a property of |nextFree|, and applying the
    induction hypothesis yields
    |step Let1 (eval e2 ρ1' (ext μ1' a d)) = many (Step ev) (eval v ρ2 μ2)|
    as required.
\end{itemize}
\end{proof}

\begin{code}
byNeed  ::  (Trace d, Domain d, HasBind d, Lat d) =>  GC (Pow (T (Value (ByNeed T), Heap (ByNeed T)))) d
byNeed = repr β where
  β (Step e d)           = step e (β d)
  β (Ret (Stuck, μ))     = stuck
  β (Ret (Fun f, μ))     = fun {-"\iffalse"-}""{-"\fi"-} (\(hat d) -> Lub (β (f d μ) | d ∈ γE (hat d)))  where unused (  _   :<->: γE)  = untyped (freezeHeap μ)
  β (Ret (Con k ds, μ))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)                           where           αE  :<->: _    = freezeHeap μ
\end{code}

TODO There is potential to extract useful Galois Connections from this large
one, but it is far simpler for now to give it directly.

\begin{figure}
  \[\begin{array}{c}
    \inferrule[\textsc{Step-Inc}]{}{|hat d ⊑ step ev (hat d)|}
    \qquad
    \inferrule[\textsc{Update}]{}{|step Update (hat d) = hat d|}
  \end{array}\]
  \caption{Additional by-need soundness lemmas for by-name analyses}
  \label{fig:by-need-by-name-soundness-lemmas}
\end{figure}

\begin{lemmarep}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the soundness properties
  \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName} in \Cref{fig:by-name-soundness-lemmas}
  and \textsc{Step-Inc} from \Cref{fig:by-need-by-name-soundness-lemmas}.
  Furthermore, let |αE μ :<->: γE μ = freezeHeap μ| for all |μ|
  and |βE μ := αE μ . set| the representation function.
  \begin{enumerate}[label=(\alph*),ref=\thelemma.(\alph*)]
    \item
      If   |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
      and  |μ1 ! a = memo a (eval e ρ1)|,\\
      then |eval v (βE (ext μ2 a (memo a (eval v ρ2))) << ρ2) ⊑ eval e (βE μ2 << ρ1)|.
      \label{thm:memo-improves}
    \item
      If   |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
      and  |μ2 ~> μ3|,
      then |eval v (βE μ3 << ρ2) ⊑ eval e (βE μ3 << ρ1)|.
      \label{thm:value-improves}
  \end{enumerate}
\end{lemmarep}
\begin{proof}
By Löb induction, we assume that both properties hold \emph{later}.
\begin{itemize}
  \item \labelcref{thm:memo-improves}:
    We assume that |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|
    and |μ1 ! a = memo a (eval e ρ1)|
    to show |eval v (αE (ext μ2 a (memo a (eval v ρ2))) << set << ρ2) ⊑ eval e (αE μ2 << set << ρ1)|.

    We can use the IH \labelcref{thm:memo-improves} to prove that
    |βE (ext μ2 a (memo a (eval v ρ2))) d ⊑ βE μ2 d|
    for all |d| such that |adom d ⊆ adom μ2|.
    This is simple to see unless |d = step (Lookup y) (fetch a)|, in
    which case we have:
    \begin{spec}
        βE (ext μ2 a (memo a (eval v ρ2))) (step (Lookup y) (fetch a))
    = {- Unfold |βE| -}
        step (Lookup y) (eval v (βE (ext μ2 a (memo a (eval v ρ2))) << ρ2))|
    ⊑ {- IH \labelcref{thm:memo-improves} -}
        step (Lookup y) (eval e (βE μ2 << ρ1))|
    = {- Refold |βE| -}
        βE μ2 (step (Lookup y) (fetch a))
    \end{spec}

    This is enough to show the goal:
    \begin{spec}
        eval v (βE (ext μ2 a (memo a (eval v ρ2))) << ρ2)
    ⊑   {- |βE (ext μ2 a (memo a (eval v ρ2))) ⊑ βE μ2| -}
        eval v (βE μ2 << ρ2)
    ⊑   {- IH \labelcref{thm:value-improves} applied to |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ3)| -}
        eval e (βE μ2 << ρ1)
    \end{spec}

  \item \labelcref{thm:value-improves}
    |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2) && μ2 ~> μ3 ==> eval v (βE μ3 << ρ2) ⊑ eval e (βE μ3 << ρ1)|:

    By Löb induction and cases on |e|.
    \begin{itemize}
      \item \textbf{Case} |Var x|:
        Let |a| be the address such that |ρ1 ! x = step (Lookup y) (fetch a)|.
        Note that |μ1 ! a = memo a _|, so the result has been memoised in
        |μ2|, and by \Cref{thm:update-once} in |μ3| as well.
        Hence the entry in |μ3| must be of the form |μ3 ! a = memo a (eval v ρ2)|.
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step (Lookup y) (eval v (βE μ3 << ρ2))
        =   {- Refold |βE| for the appropriate |y| -}
            (βE μ3 << ρ1) ! x
        =   {- Refold |eval| -}
            eval x (βE μ3 << ρ1)
        \end{spec}
      \item \textbf{Case} |Lam x body|, |ConApp k xs|: Follows by reflexivity.
      \item \textbf{Case} |App e x|:
        Then |eval e ρ1 μ1 = many (Step ev1) (eval (Lam y body) ρ3 μ4)|\\
        and |eval body (ext ρ3 y (ρ1 ! x)) μ4 = many (Step ev2) (eval v ρ2 μ2)|.
        Note that |μ4 ~> μ2| by \Cref{thm:eval-progression}, hence |μ4 ~> μ3|
        by \progresstotrans.
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- IH \labelcref{thm:value-improves} at |μ2 ~> μ3| -}
            eval body (βE μ3 << ext ρ3 y (ρ1 ! x))
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step App2 (eval body (βE μ3 << ext ρ3 y (ρ1 ! x)))
        ⊑   {- Assumption \textsc{Beta-App} -}
            apply (eval (Lam y body) (βE μ3 << ρ3)) (βE μ3 (ρ1 ! x))
        ⊑   {- IH \labelcref{thm:value-improves} at |μ4 ~> μ3| -}
            apply (eval e (βE μ3 << ρ1)) (βE μ3 << ρ1 ! x)
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step App1 (apply (eval e (βE μ3 << ρ1)) (βE μ3 << ρ1 ! x))
        =   {- Refold |eval (App e x) (βE μ3 << ρ1)| -}
            eval (App e x) (βE μ3 << ρ1)
        \end{spec}
      \item \textbf{Case} |Case e alts|: Similar to |App|.
      \item \textbf{Case} |Let x e1 e2|:
        Then |eval (Let x e1 e2) ρ1 μ1 = step Let1 (eval e2 ρ4 μ4)|, where
        |a := nextFree μ1|, |ρ4 := ext ρ1 x (step (Lookup x) (fetch a))|,
        |μ4 := ext μ1 a (memo a (eval e1 ρ4))|.
        Observe that |μ4 ~> μ2 ~> μ3|.
        Since |μ4 ! a = memo a (eval e1 ρ4)|, |μ3 ! a| must either be the same
        entry or the result of \progresstomemo, that is,
        \begin{spec}
            eval v (βE μ3 << ρ2)
        ⊑   {- IH \labelcref{thm:value-improves} at |μ4~>μ3| -}
            eval e2 (βE μ3 << ρ4)
        ⊑   {- Assumption \textsc{Step-Inc} -}
            step Let1 (eval e2 (βE μ3 << ρ4))
        =   {- Unfold |ρ4| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (βE μ3 (ρ4 ! x))))
        \end{spec}
        Here, we proceed by case analysis on whether or not |μ4 ~> μ3| contains
        a \progresstomemo application updating |μ4 ! a|.
        If that is not the case, we have |μ3 ! a = μ4 ! a|.
        We get
        \begin{spec}
        =   {- Unfold |βE μ3 (ρ4 ! x)|, |μ3 ! a = μ4 ! a| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE μ3 << ρ1) x (hat d1)))))))
        ⊑   {- Assumption \textsc{Bind-ByName} -}
            bind  (\(hat d1) -> eval e1 (ext ((βE μ3 << ρ1)) x (step (Lookup x) (hat d1))))
                  (\(hat d1) -> step Let1 (eval e2 (ext ((βE μ3 << ρ1)) x (step (Lookup x) (hat d1)))))
        =   {- Refold |eval| -}
            eval (Let x e1 e2) (βE μ3 << ρ1)
        \end{spec}
        Otherwise, |μ3 ! a| is the result of updating it to the form
        |memo a (eval v1 ρ3)|, where |eval e1 ρ4 μ4' = many (Step ev1) (eval v1 ρ3 μ3')|
        such that |μ4 ~> μ4' ~> (ext μ3' a (memo a (eval v1 ρ3))) ~> μ3| and
        |μ3' ! a = μ4' ! a = μ4 ! a|.
        (NB: if there are multiple such occurrences of \progresstomemo in
        |μ4 ~> μ3|, this must be the first one, because afterwards it is
        $|μ4' ! a| \not= |μ4 ! a|$.)

        It is not useful to apply the IH \labelcref{thm:memo-improves} to this
        situation directly, because |μ3' ~> μ3| does not hold.
        However, since $|μ4' ! a = μ3' ! a| \not= |μ3 ! a|$, we can apply
        \Cref{thm:no-update-irrelevance} to get
        |eval e1 ρ4 (ext μ4' a (memo a (eval v1 ρ3))) = many (Step ev1) (eval v1 ρ3 (ext μ3' a (memo a (eval v1 ρ3))))|
        and applying the induction hypothesis
        \labelcref{thm:memo-improves} to |ext μ3' a (memo a (eval v1 ρ3)) ~> μ3|
        yields |eval v1 (βE μ3 << ρ3) ⊑ eval e1 (βE μ3 << ρ1)|, which we use below:
        \begin{spec}
        =   {- Unfold |βE μ3 (ρ4 ! x)|, |μ3 ! a = memo a (eval v1 ρ3)| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval v1 (ext (βE μ3 << ρ3) x (hat d1)))))))
        ⊑   {- |eval v1 (βE μ3 << ρ3) ⊑ eval e1 (βE μ3 << ρ1)| -}
            step Let1 (eval e2 (ext (βE μ3 << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE μ3 << ρ1) x (hat d1)))))))
        ⊑   {- ... as above ... -}
            eval (Let x e1 e2) (βE μ3 << ρ1)
        \end{spec}
    \end{itemize}
\end{itemize}
\end{proof}

\begin{lemmarep}[Heap progression improves abstraction]
  \label{thm:heap-progress-freeze}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the soundness properties
  \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName}
  in \Cref{fig:by-name-soundness-lemmas} and \textsc{Step-Inc}
  from \Cref{fig:by-need-by-name-soundness-lemmas}.
  Furthermore, let |αE μ :<->: γE μ = freezeHeap μ| for all |μ|.

  If |μ1 ~> μ2| and |adom d ⊆ dom μ1|, then |αE μ2 d ⊑ αE μ1 d|.
\end{lemmarep}
\begin{proof}
By Löb induction.
Let us assume that |μ1 ~> μ2| and |adom d ⊆ dom μ1|.
Since |needd d|, we have |d = Cup (step (Lookup y) (fetch a))|.
Similar to \Cref{thm:soundness-by-name}, it suffices to show the goal for a
single |d = step (Lookup y) (fetch a)| for some |y|, |a| and the representation
function |βE μ := αE μ << set|.

Furthermore, let us abbreviate |memo a (eval ei ρi) := μi ! a|.
The goal is to show
\[
  |step (Lookup y) (eval e2 (βE μ2 << ρ2)) ⊑ step (Lookup y) (eval e1 (βE μ1 << ρ1))|,
\]
Monotonicity allows us to drop the |step (Lookup x)| context
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
  \item \textbf{Case} $\inferrule*[vcenter,left=\progresstoext]{|a1| \not∈ |dom μ1| \quad |adom ρ ⊆ dom μ1 ∪ set a1|}{|μ ~> ext μ1 a1 (memo a1 (eval e ρ))|}$:\\
    We get to refine |μ2 = ext μ1 a1 (memo a1 (eval e ρ))|.
    Since |a ∈ dom μ1|,
    we have $|a1| \not= |a|$
    and thus |μ1 ! a = μ2 ! a|, thus |e1=e2|, |ρ1=ρ2|.
    The goal can be simplified to
    |Later (eval e1 (βE μ2 << ρ1) ⊑ eval e1 (βE μ1 << ρ1))|.
    We can apply the induction hypothesis to get
    |Later (βE μ2 ⊑ βE μ1)|, and the goal follows by monotonicity.
  \item \textbf{Case} $\inferrule*[vcenter,left=\progresstomemo]{|μ1 ! a1 = memo a1 (eval e ρ3)| \quad |Later (eval e ρ3 μ1 = many (Step ev) (eval v ρ2 μ3))|}{|μ1 ~> ext μ3 a1 (memo a1 (eval v ρ2))|}$:\\
    We get to refine |μ2 = ext μ3 a1 (memo a1 (eval v ρ2))|.
    When $|a1| \not= |a|$, we have |μ1 ! a = μ2 ! a| and the goal follows as in the \progresstoext case.
    Otherwise, |a = a1|, |e1 = e|, |ρ3 = ρ1|, |e2 = v|.

    We can use Lemma \labelcref{thm:memo-improves} to prove that
    |βE μ2 d ⊑ βE μ3 d| for all |d| such that |adom d ⊆ adom μ2|.
    This is simple to see unless |d = step (Lookup y) (fetch a)|, in
    which case we have:
    \begin{spec}
        βE μ2 (step (Lookup y) (fetch a))
    = {- Unfold |βE| -}
        step (Lookup y) (eval v (βE μ2 << ρ2))
    ⊑ {- Lemma \labelcref{thm:memo-improves} -}
        step (Lookup y) (eval e (βE μ3 << ρ1))
    = {- Refold |βE| -}
        βE μ3 (step (Lookup y) (fetch a))
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

\begin{lemmarep}[By-need evaluation improves by-name trace abstraction]
  \label{thm:eval-improves-need}
  Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
  |Lat|, satisfying the soundness properties \textsc{Step-App},
  \textsc{Step-Sel}, \textsc{Beta-App}, \textsc{Beta-Sel}, \textsc{Bind-ByName}
  in \Cref{fig:by-name-soundness-lemmas} and \textsc{Step-Inc}, \textsc{Update}
  from \Cref{fig:by-need-by-name-soundness-lemmas}.
  Furthermore, let |αE μ :<->: γE μ = freezeHeap μ| for all |μ|.

  If   |eval e ρ1 μ1 = many (Step ev) (eval v ρ2 μ2)|,
  then |many (step ev) (eval v (αE μ2 << set << ρ2)) ⊑ eval e (αE μ1 << set << ρ1)|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    \begin{spec}
      eval x ρ1 μ1 = Step (Lookup y) (memo a (eval e1 ρ3 μ1)) = many (Step ev) (eval v ρ2 μ2)
    \end{spec}
    for some |y|, |a|, |e1|, |ρ3|,
    such that |ρ1 = step (Lookup y) (fetch a)|, |μ1 ! a = memo a (eval e1 ρ3)| and
    |many ev = [Lookup y] ++ many ev1 ++ [Update]| for some |ev1| by determinism.
    \begin{spec}
        many (step ev) (eval v (βE μ2 << ρ2))
    =   {- |many ev = [Lookup y] ++ many ev1 ++ [Update]| -}
        step (Lookup y) (many (step ev1) (step Update (eval v (βE μ2 << ρ2))))
    =   {- Assumption \textsc{Update} -}
        step (Lookup y) (many (step ev1) (eval v (βE μ2 << ρ2)))
    ⊑   {- \Cref{thm:value-improves} implies |(βE (ext μ2 a (memo a (eval v ρ2))) << ρ2) ⊑ (βE μ2 << ρ2)|  -}
        step (Lookup y) (many (step ev1) (eval v (βE (ext μ2 a (memo a (eval e1 ρ3))) << ρ2)))
    ⊑   {- \Cref{thm:eval-improves-need} -}
        step (Lookup y) (eval e1 (βE μ1 << ρ3))
    =   {- Refold |βE|, |ρ3 ! x| -}
        βE (ρ1 ! x)
    =   {- Refold |eval x (βE μ1 << ρ1)| -}
        eval x (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    We can make one step to see
    \begin{spec}
      eval (Let x e1 e2) ρ1 μ1 = Step Let1 (eval e2 ρ3 μ3) = Step Let1 (many (Step ev1) (eval v ρ2 μ2)),
    \end{spec}
    where |ρ3 := ext ρ1 x (step (Lookup x) (fetch a))|,
    |a := nextFree μ1|,
    |μ3 := ext μ1 a (memo a (eval e1 ρ3))|.

    Then |(βE μ3 << ρ3) ! y = (βE μ1 << ρ1) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:freeze-heap-eq},
    and |(βE μ3 << ρ3) ! x = step (Lookup x) (eval e1 (βE μ3 << ρ3))|.

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
        step Let1 (eval e2 (ext (βE μ1 << ρ1) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE μ1 << ρ1) x (hat d1)))))))
    =   {- Partially unroll |lfp| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ1) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (βE μ1 << ρ1) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName} -}
        bind  (\(hat d1) -> eval e1 (ext ((βE μ1 << ρ1)) x (step (Lookup x) (hat d1))))
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE μ1 << ρ1)) x (step (Lookup x) (hat d1)))))
    =   {- Refold |eval (Let x e1 e2) (βE μ1 << ρ1)| -}
        eval (Let x e1 e2) (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Lam|, |ConApp|: By reflexivity.

  \item \textbf{Case} |App e x|:
    Very similar to \Cref{thm:eval-improves}, since the heap is never updated or
    extended.
    There is one exception: We must apply \Cref{thm:heap-progress-freeze}
    to argument denotations.

    We have |eval e ρ1 μ1 = many (Step ev1) (eval (Lam y body) ρ3 μ3)|
    and |eval body (ext ρ3 y (ρ1 ! x)) μ3 = many (Step ev2) (eval v ρ2 μ2)|.
    We have |μ1 ~> μ3| by \Cref{thm:eval-progression}.
    \begin{spec}
        step App1 (many (Step ev1) (step App2 (many (Step ev2) (eval v (βE μ2 << ρ2)))))
    =   {- Induction hypothesis at |many ev2| -}
        step App1 (many (step ev1) (step App2 (eval body (βE μ3 << (ext ρ3 y (ρ1 ! x))))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        step App1 (many (step ev1) (apply (eval (Lam y body) (βE μ3 << ρ3)) ((βE μ3 << ρ1) ! x)))
    ⊑   {- Assumption \textsc{Step-App} -}
        step App1 (apply (many (step ev1) (eval (Lam y body) (βE μ3 << ρ3))) ((βE μ3 << ρ1) ! x))
    ⊑   {- Induction hypothesis at |many ev1| -}
        step App1 (apply (eval e (βE μ1 << ρ1)) ((βE μ3 << ρ1) ! x))
    ⊑   {- \Cref{thm:heap-progress-freeze} -}
        step App1 (apply (eval e (βE μ1 << ρ1)) ((βE μ1 << ρ1) ! x))
    =   {- Refold |eval| -}
        eval (App e x) (βE μ1 << ρ1)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The same as in \Cref{thm:eval-improves}.

    We have |eval e ρ1 μ1 = many (Step ev1) (eval (ConApp k ys) ρ3 μ3)|,
    |eval er (exts ρ1 xs (map (ρ3 !) ys)) μ3 = many (Step ev2) (eval v ρ2) μ2|,
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

\begin{theoremrep}[Sound By-need Interpretation]
\label{thm:soundness-by-need}
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT = byNeed|, |αE :<->: γE = freezeHeap|.
If the soundness lemmas in \Cref{fig:by-name-soundness-lemmas}
and \Cref{fig:by-need-by-name-soundness-lemmas} hold,
then |eval| instantiates at |hat D| to an abstract interpreter that is sound
\wrt |γE -> αT|, that is,
\[
  |αT (set (eval e ρ μ) :: Pow (T (Value (ByNeed T), Heap (ByNeed T)))) ⊑ (eval e (αE μ << ρ) :: hat D)|
\]
\end{theoremrep}
\begin{proof}
As in \Cref{thm:soundness-by-name}, we simplify our proof obligation to the single-trace case:
\[
  |βT (set (eval e ρ μ) :: T (Value (ByNeed T), Heap (ByNeed T))) ⊑ (eval e (βE μ << ρ) :: hat D)|,
\]
where |βT := αT . set| and |βE μ := αE μ . set| are the representation
functions corresponding to |αT| and |αE|.

We proceed by Löb induction.

Whenever |eval e ρ μ = many (Step ev) (eval v ρ2 μ2)| yields a balanced trace
and makes at least one step, we can reuse the proof for
\Cref{thm:eval-improves-need} as follows:
\begin{spec}
    βT (eval e ρ μ)
=   {- |eval e ρ μ = many (Step ev) (eval v ρ2 μ2)|, unfold |βT| -}
    many (step ev) (βT (eval v ρ2 μ2))
⊑   {- Induction hypothesis (needs non-empty |many ev|) -}
    many (step ev) (eval v (βE μ2 << ρ2))
⊑   {- \Cref{thm:eval-improves-need} -}
    eval e (βE μ << ρ)
\end{spec}

Thus, if |e| is not a value, either the trace diverges or is stuck.
We proceed by cases over |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |βT|.
    \begin{spec}
        βT ((ρ ! x) μ)
    =   {- |needenv ρ|, Unfold |βT| -}
        step (Lookup y) (βT (fetch a μ))
    =   {- |needheap μ| -}
        step (Lookup y) (βT (memo a (eval e1 ρ1 μ)))
    \end{spec}
    By assumption, |memo a (eval e1 ρ1 μ)| diverges or gets stuck and the result
    is equivalent to |eval e1 ρ1 μ|.
    \begin{spec}
    =   {- Diverging or stuck -}
        step (Lookup y) (βT (eval e1 ρ2 μ))
    ⊑   {- Induction hypothesis -}
        step (Lookup y) (eval e1 (βE μ << ρ1))
    =   {- Refold |βE| -}
        βE μ (ρ ! x)
    \end{spec}

  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        βT (eval (Lam x body) ρ μ)
    =   {- Unfold |eval|, |βT| -}
        fun (\(hat d) -> Lub (step App2 (βT (eval body (ext ρ x d) μ)) | βE μ d ⊑ hat d))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> Lub (step App2 (eval body (βE μ << (ext ρ x d))) | βE μ d ⊑ hat d))
    ⊑   {- Least upper bound / |αE . γE ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext ((βE μ << ρ)) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (βE μ << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k xs|:
    \begin{spec}
        βT (eval (ConApp k xs) ρ μ)
    =   {- Unfold |eval|, |βT| -}
        con k (map ((βE μ << ρ) !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (βE μ << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|, |Case e alts|:
    The same steps as in \Cref{thm:soundness-by-name}.
% When I checked last, it looked like this:
%    Our proof obligation can be simplified as follows
%    \begin{spec}
%        βT (eval (App e x) ρ μ)
%    =   {- Unfold |eval|, |βT| -}
%        step App1 (βT (apply (eval e ρ μ) (ρ ! x)))
%    =   {- Unfold |apply| -}
%        step App1 (βT (eval e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    ⊑   {- By cases, see below -}
%        step App1 (apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x))
%    =   {- Refold |eval| -}
%        eval (App e x) (βE μ << ρ)
%    \end{spec}
%
%    When |eval e ρ μ| diverges, we have
%    \begin{spec}
%    =   {- |eval e ρ μ| diverges, unfold |βT| -}
%        step ev1 (step ev2 (...))
%    ⊑   {- Assumption \textsc{Step-App} -}
%        apply (step ev1 (step ev2 (...))) ((βE μ << ρ) ! x)
%    =   {- Refold |βT|, |eval| -}
%        apply (βT (eval e ρ μ)) ((βE μ << ρ) ! x)
%    ⊑   {- Induction hypothesis -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}
%    Otherwise, |eval e ρ μ| must produce a value |v| in heap |μ2|.
%    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
%    (resp. |d := con k (map (βE μ) ds)|) and have
%    \begin{spec}
%        βT (eval e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
%    =   {- |eval e ρ μ = many (step ev) (return v)|, unfold |βT| -}
%        many (step ev) (βT (return v μ2 >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    =   {- |v| not |Fun|, unfold |βT| -}
%        many (step ev) stuck
%    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map βT ds)| -}
%        many (step ev) (apply (d μ2) a)
%    ⊑   {- Assumption \textsc{Step-App} -}
%        apply (many (step ev) (d μ2)) ((βE μ << ρ) ! x)
%    =   {- Refold |βT|, |eval| -}
%        apply (βT (eval e ρ μ)) ((βE μ << ρ) ! x)
%    ⊑   {- Induction hypothesis -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}
%    In the final case, we have |v = Fun f|, which must be the result of some
%    call |eval (Lam y body) ρ1 μ2|; hence
%    |f := \d μ2 -> step App2 (eval body (ext ρ1 y d) μ2)|.
%    \begin{spec}
%        βT (eval e ρ μ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
%    =   {- |eval e ρ μ = many (step ev) (return v μ2)|, unfold |βT| -}
%        many (step ev) (βT (return v μ2 >>= \case Fun f -> f (ρ ! x); _ -> stuck))
%    =   {- |v=Fun f|, with |f| as above; unfold |βT| -}
%        many (step ev) (step App2 (βT (eval body (ext ρ1 y (ρ ! x)) μ2)))
%    ⊑   {- Induction hypothesis -}
%        many (step ev) (step App2 (eval body (βE μ2 << (ext ρ1 y (ρ ! x)))))
%    ⊑   {- Same as in proof for \Cref{thm:eval-improves-need} -}
%        apply (eval e (βE μ << ρ)) ((βE μ << ρ) ! x)
%    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    We can make one step to see
    \begin{spec}
      eval (Let x e1 e2) ρ μ = Step Let1 (eval e2 ρ1 μ1),
    \end{spec}
    where |ρ1 := ext ρ x (step (Lookup x) (fetch a))|,
    |a := nextFree μ|,
    |μ1 := ext μ a (memo a (eval e1 ρ1))|.

    Then |(βE μ1 << ρ1) ! y = (βE μ << ρ) ! y| whenever $|x| \not= |y|$
    by \Cref{thm:freeze-heap-eq},
    and |(βE μ1 << ρ1) ! x = step (Lookup x) (eval e1 (βE μ1 << ρ1))|.
    \begin{spec}
        βT (eval (Let x e1 e2) ρ μ)
    =   {- Unfold |eval| -}
        βT (bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
                  (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))
                  μ)
    =   {- Unfold |bind|, $|a| \not\in |dom μ|$, unfold |βT| -}
        step Let1 (βT (eval e2 (ext ρ x (step (Lookup x) (fetch a))) (ext μ a (memo a (eval e1 (ext ρ x (step (Lookup x) (fetch a))))))))
    ⊑   {- Induction hypothesis, setting |μ1 := ext μ a (memo a (eval e1 (ext ρ x (step (Lookup x) (fetch a)))))| -}
        step Let1 (eval e2 (ext (βE μ1 << ρ) x (βE μ1 (step (Lookup x) (fetch a)))))
    =   {- Expose fixpoint, rewriting |βE μ1 << ρ1| to |ext (βE μ << ρ) x (βE μ1 (ρ1 ! x))| -}
        step Let1 (eval e2 (ext (βE μ << ρ) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (βE μ << ρ) x (hat d1)))))))
    =   {- Partially unroll fixpoint -}
        step Let1 (eval e2 (ext (βE μ << ρ) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (βE μ << ρ) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = βE μ << ρ| -}
        bind  (\d1 -> eval e1 (ext (βE μ << ρ) x (step (Lookup x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (βE μ << ρ) x (step (Lookup x) d1))))
    =   {- Refold |eval (Let x e1 e2) (βE μ << ρ)| -}
        eval (Let x e1 e2) (βE μ << ρ)
    \end{spec}
\end{itemize}
\end{proof}

