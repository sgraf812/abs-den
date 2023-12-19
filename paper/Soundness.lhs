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
import Control.Monad.Trans.State
import Data.Coerce
import Data.Functor.Identity

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
An element |hat d ∈ hat D| soundly approximates |d ∈ D| if and only if |d
≤ γ(hat d)|, if and only if |α d ⊑ hat d|.
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
A trace property $P ⊆ \Traces$ is a \emph{safety property} if and only if,
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
type EnvD d = d
trace  ::  (Trace d, Domain d, Lat d)
       =>  GC (Pow (D r)) d -> GC (Pow (EnvD (D r))) (EnvD d) -> GC (Pow (T (Value r))) d
trace (αT :<->: γT) (αE :<->: γE) = repr β where
  β (Ret Stuck)       = stuck
  β (Ret (Fun f))     = fun {-"\iffalse"-}""{-"\fi"-} (αT . powMap f . γE)
  β (Ret (Con k ds))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)
  β (Step e d)        = step e (β d)
\end{code}
Note how |trace| expects two Galois connections: The first one is applicable
in the ``recursive case'' and the second one applies to (the powerset over)
|EnvD (D (ByName T))|, a subtype of |D (ByName T)|.
Every |d :: EnvD (ByName T)| is of the form |Step (Lookup x) (eval e ρ)| for
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
env :: (Trace d, Domain d, HasBind d, Lat d) => GC (Pow (EnvD (D (ByName T)))) (EnvD d)
env = untyped (repr β where β (Step (Lookup x) (eval e ρ)) = step (Lookup x) (eval e (β << ρ)))

byName :: (Trace d, Domain d, HasBind d, Lat d) => GC (Pow (D (ByName T))) d
byName = (α . powMap unByName) :<->: (powMap ByName . γ) where α :<->: γ = trace byName env
\end{code}
There is a need to clear up the domain and range of |env|.
Since its domain is sets of elements from |EnvD (D (ByName T))|, its range
|EnvD d| looks like the (possibly infinite) join over abstracted elements that
look like |step (Lookup x) (eval e (β << ρ))| for some |x|,|e|,|ρ|.
Although we have ``sworn off'' operational semantics for abstraction, we still
rely on syntax to structure the vast semantic domain in this way, thus working
around matters of full abstraction~\citep{Plotkin:77}.
More formally,

\begin{definition}[Syntactic by-name environments]
  Let |D| be a domain satisfying |Trace|,|Domain|,|HasBind| and |Lat|.
  We write |syn D d| (resp. |syne D ρ|) to say that the denotation |d| (resp.
  environment |ρ|) is \emph{syntactic}, which we define mutually recursive as
  \begin{itemize}
    \item |syn D d| if and only if |d| is of the form |Lub (step (Lookup x) (eval e ρ1 :: D) || Later (syn D ρ1))|, and
    \item |syne D ρ| if and only if for all |x|, |syn D (ρ x)|.
  \end{itemize}
\end{definition}
% We really need to generalise over |D|, so that the following sentence makes sense:

Syntactic denotations are morally generated by closure powersets
|Clo := pow (Var,Exp,Name :-> Clo)|.
For the remainder of this Subsection, we assume a refined definition of |Domain|
and |HasBind| that expects |syn D| where we pass around denotations that end up
in an environment.
It is then easy to see that |eval e ρ| preserves |syne D| in recursive
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

  If |eval e ρ1 = many (step ev) (eval v ρ2)|,
  then |many (step ev) (eval v (αE << set << ρ2)) ⊑ eval e (αE << set << ρ1)|,
  where |αE :<->: γE = env|.
\end{lemmarep}
\begin{proof}
By Löb induction and cases on |e|, using the representation function
|βE := αE . set|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    By assumption, we know that
    |eval x ρ1 = step (Lookup y) (eval e' ρ3) = many (step ev) (eval v ρ2)|
    for some |y|,|e'|,|ρ3|,
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
  \item \textbf{Case} |Lam|,|ConApp|: By reflexivity of $⊑$.
  \item \textbf{Case} |App e x|:
    Then |eval e ρ1 = many (step ev1) (eval (Lam y body) ρ3)|,
    |eval body (ext ρ3 y (ρ1 ! x)) = many (step ev1) (eval v ρ2)|.
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
    Then |eval e ρ1 = many (step ev1) (eval (ConApp k ys) ρ3)|,
    |eval er (exts ρ1 xs (map (ρ3 !) ys)) = many (step ev2) (eval v ρ2)|,
    where |alts ! k = (xs,er)| is the matching RHS.
    \begin{spec}
        many (step ev) (eval v (βE << ρ2))
    ⊑   {- |many ev = [Case1] ++ many ev1 ++ [Case2] ++ ev2|, IH at |ev2| -}
        step Case1 (many (step ev1) (step Case2 (eval er (βE << (exts ρ1 xs (map (hat ρ3 !) ys))))))
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        step Case1 (many (step ev1) (select (eval (ConApp k ys) (βE << ρ3)) (cont << alts)))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        step Case1 (select (step ev1 (eval (ConApp k ys) (βE << ρ3))) (cont << alts))
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
              (\(hat d1) -> step Let1 (eval e2 (ext ((βE << ρ1)) x (hat d1))))
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
By Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |αT|.
    Otherwise,
    \begin{spec}
        αT (ρ ! x)
    =   {- |syne (Pow (D (ByName T))) ρ|, Unfold |αT| -}
        step (Lookup y) (αT (eval e' ρ'))
    ⊑   {- Induction hypothesis -}
        step (Lookup y) (eval e' (αE << ρ'))
    =   {- Refold |αE| -}
        αE (ρ ! x)
    \end{spec}
  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        αT (eval (Lam x body) ρ)
    =   {- Unfold |eval|, |αT| -}
        fun (\(hat d) -> step App2 (αT (eval body (ext ρ x (γE (hat d))))))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> step App2 (eval body (αE (ext ρ x (γE (hat d))))))
    ⊑   {- |αE . γE ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext (αE << ρ) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (αE << ρ)
    \end{spec}

  \item \textbf{Case} |ConApp k ds|:
    \begin{spec}
        αT (eval (ConApp k xs) ρ)
    =   {- Unfold |eval|, |αT| -}
        con k (map ((αT << ρ) !) xs)
    =   {- Refold |eval| -}
        eval (Lam x body) (αT << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    The stuck case follows by unfolding |αT|.

    Our proof obligation can be simplified as follows
    \begin{spec}
        αT (eval (App e x) ρ)
    =   {- Unfold |eval| -}
        αT (apply (eval e ρ) (ρ ! x))
    =   {- Unfold |apply| -}
        αT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    \end{spec}

    By determinism, it is sufficient to consider one class of traces
    at a time.
    (More formally, we'd argue on the representation function |βD|;
    the argument would be identical.)
    When |eval e ρ| diverges, we have
    \begin{spec}
    =   {- |eval e ρ| diverges, unfold |αT| -}
        step ev1 (step ev2 (...))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (step ev1 (step ev2 (...))) ((αE << ρ) ! x)
    =   {- Refold |αT|, |eval e ρ| -}
        apply (αT (eval e ρ)) ((αE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (αE << ρ)) ((αE << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE << ρ)
    \end{spec}
    Otherwise, |eval e ρ| must produce a value |v|.
    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
    (resp. |d := con k (map αE ds)|) and have
    \begin{spec}
        αT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |αT| -}
        many (step ev) (αT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v| not |Fun|, unfold |αT| -}
        many (step ev) stuck
    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map αT ds)| -}
        many (step ev) (apply d a)
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) d) ((αE << ρ) ! x)
    =   {- Refold |αT|, |eval e ρ| -}
        apply (αT (eval e ρ)) ((αE << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (αE << ρ)) ((αE << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE << ρ)
    \end{spec}
    In the final case, we have |v = Fun f|, which must be the result of some
    call |eval (Lam y body) ρ1|; hence
    |f := \d -> step App2 (eval body (ext ρ1 y d))|.
    \begin{spec}
        αT (eval e ρ >>= \case Fun f -> f (ρ ! x); _ -> stuck)
    =   {- |eval e ρ = many (step ev) (return v)|, unfold |αT| -}
        many (step ev) (αT (return v >>= \case Fun f -> f (ρ ! x); _ -> stuck))
    =   {- |v=Fun f|, with |f| as above; unfold |αT| -}
        many (step ev) (step App2 (αT (eval body (ext ρ1 y (ρ ! x)))))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step App2 (eval body (αE << (ext ρ1 y (ρ ! x)))))
    =   {- Rearrange -}
        many (step ev) (step App2 (eval body (ext (αE << ρ1) y ((αE << ρ) ! x))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        many (step ev) (apply (eval (Lam y body) (αE << ρ1)) ((αE << ρ) ! x))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) (eval (Lam y body) (αE << ρ1))) ((αE << ρ) ! x)
    ⊑   {- \Cref{thm:eval-improves} applied to |many ev| -}
        apply (eval e (αE << ρ)) ((αE << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE << ρ)
    \end{spec}

  \item \textbf{Case} |Case e alts|:
    The stuck case follows by unfolding |αT|.
    When |eval e ρ| diverges or does not evaluate to |eval (ConApp k ys) ρ1|,
    the reasoning is similar to |App e x|, but in a |select| context.
    So assume that |eval e ρ = many (step ev) (eval (ConApp k ys) ρ1)| and that
    there exists |((cont << alts) ! k) ds = step Case2 (eval er (exts ρ xs ds))|.
    \begin{spec}
        αT (eval (Case e alts) ρ)
    =   {- Unfold |eval| -}
        αT (select (eval e ρ) (cont << alts))
    =   {- Unfold |select| -}
        αT (eval e ρ >>= \case Con k ds | k ∈ dom alts -> ((cont << alts) ! k) ds)
    =   {- |eval e ρ = many (step ev) (eval (ConApp k ys) ρ1)|, unfold |αT| -}
        many (step ev) (αT (eval (ConApp k ys) ρ1) >>= \case Con k ds | k ∈ dom (cont << alts) -> ((cont << alts) ! k) ds)
    =   {- Simplify |return (Con k ds) >>= f = f (Con k ds)|, |(cont << alts) ! k| as above -}
        many (step ev) (αT (step Case2 (eval er (exts ρ xs (map (ρ1 !) ys)))))
    =   {- Unfold |αT| -}
        many (step ev) (step Case2 (αT (eval er (exts ρ xs (map (ρ1 !) ys)))))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step Case2 (eval er (exts (αE << ρ) xs (map ((αE << ρ1) !) ys))))
    =   {- Refold |cont| -}
        cont (alts ! k) (map ((αE << ρ1) !) xs)
    ⊑   {- Assumption \textsc{Beta-Sel} -}
        many (step ev) (select (eval (ConApp k ys) (αE << ρ1)) (cont << alts))
    ⊑   {- Assumption \textsc{Step-Sel} -}
        select (many (step ev) (eval (ConApp k ys) (αE << ρ1))) (cont << alts)
    ⊑   {- \Cref{thm:eval-improves} applied to |many ev| -}
        select (eval e (αT << ρ)) (cont << alts)
    =   {- Refold |eval| -}
        eval (Case e alts) (αT << ρ)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        αT (eval (Let x e1 e2) ρ)
    =   {- Unfold |eval| -}
        αT (bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
                  (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1)))))
    =   {- Unfold |bind|, |αT| -}
        step Let1 (αT (eval e2 (ext ρ x (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1))))))))
    ⊑   {- Induction hypothesis -}
        step Let1 (eval e2 (ext (αE << ρ) x (αE (step (Lookup x) (fix (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1))))))))
    \end{spec}
    And from hereon, the proof is identical to the |Let| case of
    \Cref{thm:eval-improves}:
    \begin{spec}
    ⊑   {- By \Cref{thm:guarded-fixpoint-abstraction}, as in the proof for \Cref{thm:eval-improves} -}
        step Let1 (eval e2 (ext (αE << ρ) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (αE << ρ) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = αE << ρ| -}
        bind  (\d1 -> eval e1 (ext (αE << ρ) x (step (Lookup x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (αE << ρ) x (step (Lookup x) d1))))
    =   {- Refold |eval (Let x e1 e2) (αE << ρ)| -}
        eval (Let x e1 e2) (αE << ρ)
    \end{spec}
\end{itemize}
\end{proof}

A delightful consequence of fixing |byName| as the Galois connection for the
soundness statement is that many soundness lemmas, such as
|αT (step ev d) ⊑ step ev (αT d)| or |αT (fun f) ⊑ fun (αT . f . γE)|
follow by definition.

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

Need heap forcing relation $\forcesto$ between syntactic heaps.

\begin{definition}[Syntactic by-need heaps and environments]
  Let |D| be a domain satisfying |Trace|,|Domain|,|HasBind| and |Lat|.
  We write |syn D d| (resp. |syne D ρ|) to say that the denotation |d| (resp.
  environment |ρ|) is \emph{syntactic}, which we define mutually recursive as
  \begin{itemize}
    \item |syn D d| if and only if |d| is of the form |Lub (step (Lookup x) (eval e ρ1 :: D) || Later (syn D ρ1))|, and
    \item |syne D ρ| if and only if for all |x|, |syn D (ρ x)|.
  \end{itemize}
\end{definition}


\[\begin{array}{c}
  \ruleform{ μ_1 \forcesto μ_2 }
  \\ \\[-0.5em]
  \inferrule[\textsc{Var}]{\px ∈ Γ}{\dead{Γ}{\px}}
  \quad
  \inferrule[\textsc{App}]{\dead{Γ}{\pe \quad \px ∈ Γ}}{\dead{Γ}{\pe~\px}}
  \quad
  \inferrule[\textsc{Lam}]{\dead{Γ, \px}{\pe}}{\dead{Γ}{\Lam{\px}{\pe}}}
  \\ \\[-0.5em]
  \inferrule[$\textsc{Let}_1$]{\dead{Γ, \py}{\pe_1} \quad \dead{Γ, \py}{\pe_2}}{\dead{Γ}{\Let{\py}{\pe_1}{\pe_2}}}
  \quad
  \inferrule[$\textsc{Let}_2$]{\dead{Γ}{\pe_2}}{\dead{Γ}{\Let{\py}{\pe_1}{\pe_2}}}
  \\[-0.5em]
\end{array}\]

Need new |αT|.

\begin{code}
stTrace  ::  (Trace d, Domain d, Lat d)
         =>  (Heap (ByNeed T) -> GC (Pow (D (ByNeed T))) d)
         ->  (Heap (ByNeed T) -> GC (Pow (EnvD (D (ByNeed T)))) (EnvD d))
         ->  GC (Pow (T (Value (ByNeed T), Heap (ByNeed T)))) d
stTrace _ envs = repr β where
  (αE,γE) = (\μ -> case envs μ of αE :<->: _ -> αE, \μ -> case envs μ of _ :<->: γE -> γE)
  β (Step e d)           = step e (β d)
  β (Ret (Stuck, μ))     = stuck
  β (Ret (Fun f, μ))     = fun {-"\iffalse"-}""{-"\fi"-} (\(hat d) -> Lub (β (f d μ') | (d,μ') `elem` γE μ, μ ~> μ'))
  β (Ret (Con k ds, μ))  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE μ . set) ds)

freezeEnv :: (Trace d, Domain d, HasBind d, Lat d) => Heap (ByNeed T) -> GC (Pow (EnvD (D (ByNeed T)))) (EnvD d)
freezeEnv μ = untyped (repr β where
  β (Step (Lookup x) (fetch a)) | memo a (eval e ρ) <- μ ! a = step (Lookup x) (eval e (β << ρ)))

byNeed :: (Trace d, Domain d, HasBind d, Lat d) => GC (Pow (T (Value (ByNeed T), Heap (ByNeed T)))) d
byNeed = (α) :<->: (γ) where α :<->: γ = stTrace undefined freezeEnv
\end{code}

\begin{lemmarep}[By-name, by-need]
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT = byNeed|, |αE :<->: γE = freezeEnv|.
If |step Update d ⊑ d| for all |d|, then
\[
  |αT (memo a (eval e ρ' (ext μ a d))) ⊑ αT (eval e ρ' (ext μ a d))|.
\]
\end{lemmarep}
\begin{proof}
Let us abbreviate |μ1 := ext μ a d| and proceed
by Löb induction and cases on |e|.
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |αT|.
    Otherwise,
    \begin{spec}
        αT (memo a ((ρ ! x) μ1))
    =   {- |syne (Pow (D (ByNeed T))) ρ|, Unfold |αT| -}
        memo a (step (Lookup y) (αT (fetch a1 μ)))
    =   {- Unfold |fetch| -}
        step (Lookup y) (αT ((μ ! a1) μ))
    =   {- |synh (Pow (D (ByNeed T))) μ|  TODO define |synh| -}
        step (Lookup y) (αT (memo (ρ ! x) (eval e ρ' μ)))
    ⊑   {- TODO Important lemma. Perhaps even the key lemma? -}
        step (Lookup y) (αT (eval e ρ' μ))
    ⊑   {- Induction hypothesis -}
        step (Lookup y) (eval e' (αE μ << ρ'))
    =   {- Refold |αE| -}
        αE μ (ρ ! x)
    \end{spec}
\end{itemize}
\end{proof}

\begin{theoremrep}[Sound By-need Interpretation]
Let |hat D| be a domain with instances for |Trace|, |Domain|, |HasBind| and
|Lat|, and let |αT :<->: γT = byNeed|, |αE :<->: γE = freezeEnv|.
If the soundness lemmas in \Cref{fig:by-need-soundness-lemmas} hold,
then |eval| instantiates at |hat D| to an abstract interpreter that is sound
\wrt |γE -> αT|, that is,
\[
  |αT (set (eval e ρ μ) :: Pow (T (Value (ByNeed T), Heap (ByNeed T)))) ⊑ (eval e (αE μ << ρ) :: hat D)|
\]
\end{theoremrep}
\begin{proof}
%if False
ρ(x) = step (Lookup y) (fetch a)
αE ([a↦eval e ρ'], (step (Lookup y) (fetch a))) = step (Lookup y) (eval e (αE μ << ρ'))
defined via least fixed point? Or perhaps via fixpoint abstraction lemma?

αE :<->: γE :: GC (Pow (Heap, EnvD (D (ByNeed T)))) (EnvD (hat d))

βT :: T (Value (ByNeed T), Heap (ByNeed T)) -> hat D
βT (Step e d) = step e (βD d)
βT (Ret (Stuck,μ)) = stuck
βT (Ret (Fun f,μ)) = fun (\(hat d) -> Lub (βD (f d μ') | (d,μ') `elem` γE μ, μ ~> μ'))
βT (Ret (Con k ds,μ)) = con k (map (αE μ !) ds)
αE :: Heap (ByNeed T) -> (EnvD (D (ByNeed T)) -> EnvD (hat D))

μ is index, so

αE μ d, γE μ (hat d)

Then |γE μ (hat d) = Cup (d | αE μ' d ⊑ hat d, μ ~> μ')|.

and μ ~> μ' ==> αE μ' ⊑ αE μ'[μ] (perhaps even `αE μ`? No, the latter is more general. When d is defined on both μ and μ', then `αE μ` follows)
    μ ~> μ' ==> γE μ' ⊆ γE μ'[μ]

and GC can be generalised as follows (assuming μ ~> μ'):
    αE μ'[μ] . γE μ ⊑ id
    id              ⊑ γE μ'[μ] . αE μ
regular definition is when dom(μ') = dom(μ)

Another lemma: If rng(ρ) ⊆ dom(μ), then
    αE μ'[μ] << ρ = αE μ << ρ
%endif
\begin{itemize}
  \item \textbf{Case} |Var x|:
    The stuck case follows by unfolding |αT|.
    Otherwise,
    \begin{spec}
        αT ((ρ ! x) μ)
    =   {- |syne (Pow (D (ByNeed T))) ρ|, Unfold |αT| -}
        step (Lookup y) (αT (fetch a μ))
    =   {- Unfold |fetch| -}
        step (Lookup y) (αT ((μ ! a) μ))
    =   {- |synh (Pow (D (ByNeed T))) μ|  TODO define |synh| -}
        step (Lookup y) (αT (memo a (eval e ρ' μ)))
    ⊑   {- TODO Important lemma. Perhaps even the key lemma? -}
        step (Lookup y) (αT (eval e ρ' μ))
    ⊑   {- Induction hypothesis -}
        step (Lookup y) (eval e' (αE μ << ρ'))
    =   {- Refold |αE| -}
        αE μ (ρ ! x)
    \end{spec}
  \item \textbf{Case} |Lam x body|:
    \begin{spec}
        αT (eval (Lam x body) ρ μ)
    =   {- Unfold |eval|, |αT| -}
        αV (Fun (\d μ' -> step App2 (eval body (ext ρ x d) μ')), µ)
    =   {- Definition of |αV| TODO check this, in particular the currying going on.
           How do we know $μ ~> μ'$??
           Perhaps integrate into αV/γE/attach upper bound to (hat d) or Fun. -}
        fun (\(hat d) -> αT (Cup (step App2 (eval e (ext ρ x d) μ') | (d,μ') `elem` γE μ (hat d), μ ~> μ')))
    =   {- |αT| Preserves Lubs, Unfold |αT|  -}
        fun (\(hat d) -> Lub (step App2 αT (eval e (ext ρ x d) μ') | (d,μ') `elem` γE μ (hat d), μ ~> μ'))
    ⊑   {- |step| is monotonic  -}
        fun (\(hat d) -> step App2 (Lub (αT (eval e (ext ρ x d) μ') | (d,μ') `elem` γE μ (hat d), μ ~> μ')))
    ⊑   {- |μ ~> μ' ==> αT (eval e ρ μ') ⊑ αT (eval e ρ μ'[μ])| -}
        fun (\(hat d) -> step App2 (Lub (αT (eval e (ext ρ x d) μ'[μ]) | (d,μ') `elem` γE μ (hat d), μ ~> μ')))
    ⊑   {- Induction hypothesis -}
        fun (\(hat d) -> step App2 (Lub (eval body (αE μ'[μ] << (ext ρ x d)) | (d,μ') `elem` γE μ (hat d), μ ~> μ')))
    ⊑   {- |αE μ'[μ] . γE μ ⊑ id| -}
        fun (\(hat d) -> step App2 (eval body (ext (αE μ'[μ] << ρ) x (hat d))))
    =   {- |dom μ ⊆ rng ρ ==> αE μ'[μ] << ρ = αE μ << ρ| -}
        fun (\(hat d) -> step App2 (eval body (ext (αE μ << ρ) x (hat d))))
    =   {- Refold |eval| -}
        eval (Lam x body) (αE << ρ)
    \end{spec}

  \item \textbf{Case} |App e x|:
    The stuck case follows by unfolding |αT|.

    Our proof obligation can be simplified as follows
    \begin{spec}
        αT (eval (App e x) ρ μ)
    =   {- Unfold |eval| -}
        αT (apply (eval e ρ) (ρ ! x) μ)
    =   {- Unfold |apply| -}
        αT (eval e ρ μ >>= \case (Fun f, μ') -> f (ρ ! x) μ'; _ -> stuck)
    \end{spec}

    By determinism, it is sufficient to consider one class of traces
    at a time.
    (More formally, we'd argue on the representation function |βD|;
    the argument would be identical.)
    When |eval e ρ μ| diverges, we have
    \begin{spec}
    =   {- |eval e ρ μ| diverges, unfold |αT| -}
        step ev1 (step ev2 (...))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (step ev1 (step ev2 (...))) ((αE μ << ρ) ! x)
    =   {- Refold |αT|, |eval e ρ μ| -}
        apply (αT (eval e ρ μ)) ((αE μ << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (αE μ << ρ)) ((αE μ << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE μ << ρ)
    \end{spec}
    Otherwise, |eval e ρ μ| must produce a value |(v, μ')|.
    If |v=Stuck| or |v=Con k ds|, we set |d := stuck|
    (resp. |d := con k (map (αE μ') ds)|) and have
    \begin{spec}
        αT (eval e ρ μ >>= \case (Fun f, μ') -> f (ρ ! x) μ'; _ -> stuck μ')
    =   {- |eval e ρ μ = many (Step ev) (return (v,μ'))|, unfold |αT| -}
        many (step ev) (αT (return (v, μ') >>= \case (Fun f, μ') -> f (ρ ! x) μ'; _ -> stuck μ'))
    =   {- |v| not |Fun|, unfold |αT|, TODO: Check that indeed |αT (stuck μ') = stuck| -}
        many (step ev) stuck
    ⊑   {- Assumptions \textsc{Unwind-Stuck}, \textsc{Intro-Stuck} where |d := stuck| or |d := con k (map (αE μ') ds)| -}
        many (step ev) (apply d ((αE μ << ρ) ! x))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) d) ((αE μ << ρ) ! x)
    =   {- Refold |αT|, |eval e ρ μ| -}
        apply (αT (eval e ρ μ)) ((αE μ << ρ) ! x)
    ⊑   {- Induction hypothesis -}
        apply (eval e (αE μ << ρ)) ((αE μ << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE μ << ρ)
    \end{spec}
    In the final case, we have |v = Fun f|, which must be the result of some
    call |eval (Lam y body) ρ1 μ1|; hence
    |f := \d μ2 -> step App2 (eval body (ext ρ1 y d) μ2)|.
    TODO: Attach constraint |μ1 ~> μ2| somehow
    \begin{spec}
        αT (eval e ρ μ >>= \case (Fun f, μ') -> f (ρ ! x) μ'; _ -> stuck μ')
    =   {- |eval e ρ μ = many (step ev) (return (v, μ'))|, unfold |αT| -}
        many (step ev) (αT (return (v, μ') >>= \case (Fun f, μ') -> f (ρ ! x) μ'; _ -> stuck μ'))
    =   {- |v=Fun f|, with |f| as above; unfold |αT| -}
        many (step ev) (step App2 (αT (eval body (ext ρ1 y (ρ ! x)) μ')))
    ⊑   {- Induction hypothesis -}
        many (step ev) (step App2 (eval body (αE μ' << (ext ρ1 y (ρ ! x)))))
    =   {- Rearrange -}
        many (step ev) (step App2 (eval body (ext (αE μ' << ρ1) y ((αE μ' << ρ) ! x))))
    ⊑   {- Assumption \textsc{Beta-App} -}
        many (step ev) (apply (eval (Lam y body) (αE μ' << ρ1)) ((αE μ' << ρ) ! x))
    ⊑   {- Assumption \textsc{Step-App} -}
        apply (many (step ev) (eval (Lam y body) (αE μ' << ρ1))) ((αE μ' << ρ) ! x)
    ⊑   {- \Cref{thm:eval-improves} applied to |many ev| TODO: Check whether it holds for by-need as well -}
        apply (eval e (αE μ' << ρ)) ((αE μ' << ρ) ! x)
    ⊑   {- |μ ~> μ' ==> αE μ' ⊑ αE μ'[μ]|, |rng(ρ) ⊆ dom(μ) ==> αE μ'[μ] << ρ = αE μ| -}
        apply (eval e (αE μ << ρ)) ((αE μ << ρ) ! x)
    =   {- Refold |eval| -}
        eval (App e x) (αE μ' << ρ)
    \end{spec}

  \item \textbf{Case} |Let x e1 e2|:
    \begin{spec}
        αT (eval (Let x e1 e2) ρ μ)
    =   {- Unfold |eval| -}
        αT (bind  (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
                  (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))
                  μ)
    =   {- Unfold |bind|, $|a| \not\in |dom μ|$, unfold |αT| -}
        step Let1 (αT (eval e2 (ext ρ x (step (Lookup x) (fetch a))) (ext μ a (memo a (eval e1 (ext ρ x (step (Lookup x) (fetch a))))))))
    ⊑   {- Induction hypothesis, setting |μ1 := ext μ a (memo a (eval e1 (ext ρ x (step (Lookup x) (fetch a)))))| -}
        step Let1 (eval e2 (ext (αE μ1 << ρ) x (αE μ1 (step (Lookup x) (fetch a)))))
    ⊑   {- By \Cref{thm:guarded-fixpoint-abstraction} applied to the guarded definition of |αE| -}
        step Let1 (eval e2 (ext (αE μ1 << ρ) x (lfp (\(hat d1) -> step (Lookup x) (eval e1 (ext (αE μ1 << ρ) x (hat d1)))))))
    =   {- Partially unroll fixpoint -}
        step Let1 (eval e2 (ext (αE μ1 << ρ) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (αE μ1 << ρ) x (step (Lookup x) (hat d1))))))))
    ⊑   {- |μ ~> μ' ==> αE μ' ⊑ αE μ'[μ]|, |rng(ρ) ⊆ dom(μ) ==> αE μ'[μ] << ρ = αE μ| -}
        step Let1 (eval e2 (ext (αE μ << ρ) x (step (Lookup x) (lfp (\(hat d1) -> eval e1 (ext (αE μ << ρ) x (step (Lookup x) (hat d1))))))))
    ⊑   {- Assumption \textsc{Bind-ByName}, with |hat ρ = αE μ1 << ρ| -}
        bind  (\d1 -> eval e1 (ext (αE μ << ρ) x (step (Lookup x) d1)))
              (\d1 -> step Let1 (eval e2 (ext (αE μ << ρ) x (step (Lookup x) d1))))
    =   {- Refold |eval (Let x e1 e2) (αE μ << ρ)| -}
        eval (Let x e1 e2) (αE μ << ρ)
    \end{spec}
\end{itemize}
\end{proof}

%if False
\begin{comment}
Γ ⊦ { P } d { v.Q }
:= Γ => ∀μ μ_f. μ # μ_f => [[P]] μ => d μ = ...(v,μ') => μ' # μ_f /\ [[Q v]] μ'

Syntactic sugar in pre- and postconditions:
[[ [] ]] := λμ. µ = []
[[ [a ↦ d] ]] := λμ. µ(a) = Later d
[[ A * B ]] := λμ. ∃μ1,μ2. μ1#μ2 /\ μ = μ1 ∪ μ2 /\ [[A]] μ1 /\ [[B]] μ2
[[ P(e) ]] := λμ. P(e) /\ μ = []

ρ syne ⊦ { adom(μ) ⊆ dom(ρ) /\ μ a = memo a (Later (eval e' ρ')) }
         eval e ρ
         { v. adom(μ) ⊆ adom(μ') /\ ∀a. μ' a = μ a \/ ((e',ρ') ~> (v,ρ'') /\ μ a = memo a (Later (eval v ρ''))) }

WHAT IS THE POINT? Why not more syntactic? It's all restricted to syntactic elements d anyway
But then we can't use Hoare Triples to describe, e.g., fetch:

{ Later ([ a ↦ d ]) * Later (P(d)) } fetch a { v. d => (v,μ') μ /\ [ a ↦ d ] })
{ [ a ↦ _ ] } memo a d { v. d μ => (v,μ') * μ'[a ↦ memo a (return v) ] }
{ [] } \μ -> ((), ext μ (nextFree μ) d) { [ a ↦ d ] }

heap

\end{comment}
%endif

%if False
\begin{code}
trace2  ::  (Trace d, Lat d)
        =>  GC (Pow v) d ->  GC (Pow (T v)) d
trace2 (α :<->: γ) = repr β where
  β (Ret v)     = α (set v)
  β (Step e d)  = step e (β d)

value  ::  (Domain d, Lat d)
       =>  GC (Pow (D τ)) d
       ->  GC (Pow (EnvD (D τ))) d
       ->  GC (Pow (Value τ)) d
value (αT :<->: γT) (αE :<->: γE) = repr β where
  β Stuck       = stuck
  β (Fun f)     = fun {-"\iffalse"-}""{-"\fi"-} (αT . powMap f . γE)
  β (Con k ds)  = con {-"\iffalse"-}""{-"\fi"-} k (map (αE . set) ds)

-- better decomposition of byName:
byName2 :: (Trace d, Domain d, HasBind d, Lat d) => GC (Pow (D (ByName T))) d
byName2 = (α . powMap unByName) :<->: (powMap ByName . γ) where α :<->: γ = trace2 (value byName2 env)

type HeapD d = d

newtype StateD d = StateD { unStateD :: State (Addr :-> HeapD (StateD d)) d }
  deriving (Eq, Lat)

-- but we need a more specific version of trace2 now
trace3  ::  (Trace d, Lat d, Lat (hat h))
        =>  GC (Pow (v,h)) (d,hat h)
        ->  GC (Pow (T (v, h))) (d, (hat h))
trace3 (α :<->: γ) = repr β where
  β (Ret (v, μ))  =  α (set (v, μ))
  β (Step e d)    |  (hat d,hat μ) <- β d = (step e (hat d), hat μ)

instance (Eq d, Eq h) => Eq (State h d)
instance (Lat d, Lat h) => Lat (State h d)

stateT  ::  forall d (hat h) h v. (Lat d, Trace d, Lat (hat h))
          =>  GC (Pow (v, h)) (d,hat h)
          ->  GC (Pow h) (hat h)
          ->  GC (Pow (StateT h T v, h)) (StateT (hat h) Identity d, hat h)
stateT val (αH :<->: γH) = repr β where
  trc :: GC (Pow (T (v, h))) (d, hat h)
  trc@(αT :<->: γT) = trace3 val
  β :: (StateT h T v, h) -> (State (hat h) d, hat h)
  β (StateT f, μ) = (state (αT . powMap f . γH), αH (set μ))

env' :: (Trace d, Lat d) => GC (Pow (EnvD (D (ByNeed T)))) (EnvD (StateD d))
env' = untyped (repr β where β (Step (Lookup x) (fetch a)) = step (Lookup x) (fetch a))

entry :: (Trace d, Domain d, HasBind d, Lat d) => GC (Pow (HeapD (D (ByNeed T)))) (HeapD (StateD d))
entry = untyped (repr β where β (Later (eval e ρ)) = Later (eval e (α << set << ρ)) where
  α :<->: _ = env')

pap :: b -> GC (a, b) (hat a, hat b) -> GC a (hat a)
pap b (α :<->: β) = (\a -> fst (α (a,b))) :<->: (\(hat a) -> Lub (set (a1 | α(a1,b) ⊑ α(a,b))))

-- Obs:
--  1. We have `Domain d`, but not `Domain (StateD d)`. The latter is not derivable from the former
--  2. Concretely, we need to abstract `StateD d` into `d` for use in `fun :: (d -> d) -> d`.
--     (For that, it is enough to be able to abstract `State (Addr :-> d) d` into `d`.)
--     But this needs least evaluated heap in which the `StateD` is defined.
--     Actually, a `StateD d` does not encode the same info as a `d` at all; it's rather `(StateD d, Heap) :<->: d`
--     So perhaps we need `(StateD d, Addr :-> StateD d) :<->: d`.
--     Can we get by without the `StateD`? perhaps just `(State (Addr :-> d) d, Addr :-> d)`? worry later
byNeed  ::  forall d. (Trace d, Domain d, Lat d)
        =>  GC (State (Addr :-> HeapD d) d) d
        ->  GC (Addr :-> HeapD (StateD d)) (Addr :-> HeapD d)
        ->  GC (Pow (D (ByNeed T))) d
byNeed (hat runState) (hat freeze) = undefined -- (α . powMap (\d -> (coerce d, emp))) :<->: (powMap (ByNeed . fst) . γ) where
  where
  t :: GC (Pow (StateT (Heap (ByNeed T)) T (Value (ByNeed T)), Heap (ByNeed T))) (StateT (Addr :-> HeapD d) Identity d, Addr :-> HeapD d)
  t@(α :<->: γ) = stateT val (hat freeze)
  val :: GC (Pow (Value (ByNeed T), Heap (ByNeed T))) (d, Addr :-> HeapD d)
  val = repr β where
    β (v, μ) = _ (f (set v))
      where
        f :<->: _ = value (pap μ t) env'
  αE :<->: _ = entry

noupdate :: GC (StateD d, Addr :-> HeapD (StateD d)) d
noupdate = α :<->: γ where
  α (StateD s, μ) = case runState s μ of (d, μ') -> (d, αH μ)
  γ (d, μ) = (StateD (state (\_μ -> (d, γH μ))), γH μ)
  αH μ = (\s -> fst (α (s,μ))) << μ
  γH μ = (\d -> fst (γ (d,μ))) << μ

noupdateHeap :: GC (StateD d, Addr :-> HeapD (StateD d)) d
noupdateHeap = αH :<->: γH where
  α (s, μ) = case runState s μ of (d, μ') -> (d, αH μ)
  γ (d, μ) = (StateD (state (\_μ -> (d, γH μ))), γH μ)
  αH μ = (\s -> fst (α (s,μ))) << μ
  γH μ = (\d -> fst (γ (d,μ))) << μ

nameNeed :: GC (StateD d, Addr :-> HeapD (StateD d)) (d, Addr :-> HeapD d)
nameNeed = α :<->: γ where
  α (StateD s, μ) = case runState s μ of (d, μ') -> (d, αH μ)
  γ (d, μ) = (StateD (state (\_μ -> (d, γH μ))), γH μ)
  αH μ = (\s -> fst (α (s,μ))) << μ
  γH μ = (\d -> fst (γ (d,μ))) << μ
  --   (s, μ)
  -- = (\μ -> case s μ of (d, μ') -> (d,μ'), μ)
  -- ⊑ (\μ -> case s μ of (d, _μ') -> (d,μ), μ)     -- these are the
  -- ⊑ (\_μ -> case s μ of (d, _μ') -> (d,μ), μ)    -- key steps (assumptions)
  -- = case s μ of (d, _μ') -> (\_μ -> (d, μ), μ)
  -- ⊑ case s μ of (d, _μ') -> (\_μ -> (d, γH (αH μ)), γH (αH μ)) -- proven below
  -- = case s μ of (d, _μ') -> γ (d, αH μ)
  -- = γ (case s μ of (d, _μ') -> (d, αH μ))
  -- = γ (α (s, μ))
  --
  --   μ    where μ = [many (a↦s)]
  -- = [many (a ↦ s)]
  -- = [many (a ↦ fst (s,μ))]
  -- ⊑ [many (a ↦ fst (γ (α (s,μ))))]
  -- = [many (a ↦ fst (γ (fst (α (s,μ)), αH μ)))]
  -- = (\d -> fst (γ (d, αH μ))) << [many (a ↦ fst (α (s,μ)))]
  -- = (\d -> fst (γ (d, αH μ))) << αH μ
  -- = γH (αH μ)
  --
  --   α (γ (d, μ)) -- NB: No assumptions here
  -- = α (\_μ -> (d, γH μ), γH μ)
  -- = α (\_μ -> (d, γH μ), γH μ)
  -- = case (d, γH μ) of (d, μ') -> (d, αH (γH μ))
  -- = (d, αH (γH μ)) -- proven below
  -- = (d, μ)  -- NB: Exact ==> Galois insertion
  --
  --   αH (γH μ)   where μ = [many (a↦d)]
  -- = (\s -> fst (α (s,γH μ))) << γH μ
  -- = (\s -> fst (α (s,γH μ))) << [many (a ↦ fst (γ (d,μ)))]
  -- = [many (a ↦ fst (α (fst (γ (d,μ)), γH μ)))]
  -- = [many (a ↦ fst (α (γ (d,μ))))] -- Löb IH
  -- = [many (a ↦ fst (d,μ))]
  -- = [many (a ↦ d)]
  -- = μ

\end{code}
%endif
