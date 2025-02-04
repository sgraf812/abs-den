%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances -Wno-unused-matches #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}

module StaticAnalysis where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Identity
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.STRef
import Data.Foldable
import Data.Coerce
import qualified Data.List as List
import Exp
import Order
import Interpreter
\end{code}
%endif

\section{Static Analysis}
\label{sec:abstraction}

So far, our semantic domains have all been \emph{infinite}, simply because the
dynamic traces they express are potentially infinite as well.
However, by instantiating the generic denotational interpreter with
a semantic domain in which every element is \emph{finite data}, we can run the
interpreter on the program statically, at compile time, to yield a \emph{finite}
abstraction of the dynamic behavior.
This gives us a \emph{static program analysis}.

%To show the applicability of our framework, \Cref{sec:more-analyses} briefly
%discusses other successful realisations of analyses such as boxity
%analysis~\citep{Henglein:94}, \citeauthor{Milner:78}'s ML-style type inference,
%0CFA control-flow analysis and GHC's Demand Analysis as denotational
%interpreters.

We can get a wide range of static analyses by choosing appropriate semantic domains.
For example, we have successfully realised the following analyses as
denotational interpreters:
\begin{itemize}
  \item
    \Cref{sec:usage-analysis} defines a summary-based \emph{usage analysis},
    the running example of this work.
    We prove that usage analysis correctly infers absence in \Cref{sec:soundness}.

  \item
    \Cref{sec:type-analysis} defines a \emph{type analysis} with
    let generalisation that implements \citeauthor{Milner:78}'s Algorithm~J,
    inferring polytypes such as $\forall α_3.\ \mathtt{option}\;(α_3
    \rightarrow α_3)$ that act as summaries.

  \item
    \Cref{sec:0cfa} defines 0CFA \emph{control-flow analysis}~\citep{Shivers:91},
    a non-modular analysis lacking a finite summary mechanism, simply as a
    proof of concept.

  \item
    To demonstrate that our framework scales to real-world compilers,
    we have refactored relevant parts of \emph{Demand Analysis} in the Glasgow
    Haskell Compiler into an abstract denotational interpreter as an artefact.
    The resulting compiler bootstraps and passes the testsuite.%
    \footnote{There is a small caveat: we did not try to optimise for compiler
    performance in our proof of concept and hence it regresses in a few
    compiler performance test cases.
    None of the runtime performance test cases regress and the inferred
    demand signatures stay unchanged.}
    Demand Analysis is the real-world implementation of the cardinality analysis
    work of \citet{Sergey:14}, generalising usage analysis and implementing
    strictness analysis as well.
    For a report of this case study, we defer to \Cref{sec:demand-analysis}.

  \item
    Static compiler analyses such as Demand Analysis usually drive a subsequent
    optimisation, for which a single denotation for the entire program is
    insufficient.
    Rather, we need one for every sub-expression, or at least every binding.
    \Cref{sec:annotations} proposes a very slight generalisation of the
    |Domain| type class that lifts a stateless analysis into a stateful
    analysis writing out annotations for let bindings in a separate, global map.
    As a substantial bonus, we can use another stateful map to cache the
    results of fixpoint iterations.

%    Boxity analysis infers when it is profitable to unbox let-bound variables
%    or function arguments.
%
%    Expressions are denoted by sets of program labels that evaluation might
%    return. These labels are given meaning in an abstract store.
%    For a function label, the abstract store maintains a single point
%    approximation of the function's abstract transformer as a \emph{polyvariant}
%    summary.
%
%    \Cref{sec:type-analysis} defines a variant of \citeauthor{Milner:78}'s
%    Algorithm J --- a \emph{type analysis} with let generalisation, inferring
%    types such as $\forall α_3.\ \mathtt{option}\;(α_3 \rightarrow α_3)$.
%    Function types act as summaries in the sense of the Introduction, and
%    fixpoints are solved via unification.

\end{itemize}

In the following, we discuss usage analysis (\Cref{sec:usage-analysis}) and type
analysis (\Cref{sec:type-analysis}) in detail.

\subsection{Usage Analysis}
\label{sec:usage-analysis}

In this subsection, we give a detailed account of \emph{usage analysis} as
an instance of the denotational interpreter.
Usage analysis generalises the summary-based absence analysis from
\Cref{sec:problem}.
It is a compelling example because it illustrates that our framework is suitable
to infer \emph{operational properties}, such as an upper bound on the number of
variable lookups.

\subsubsection{Trace Abstraction in |Trace UT|}
\label{sec:usage-trace-abstraction}

\begin{figure}
\begin{minipage}{0.4\textwidth}
\begin{code}
data U = U0 | U1 | Uω
type Uses = Name :-> U
class UVec a where
  (+)  :: a -> a -> a
  (*)  :: U -> a -> a
instance UVec U where {-" ... \iffalse "-}
  U1 + U1 = Uω
  u1 + u2 = u1 ⊔ u2
  U0 * _ = U0
  _ * U0 = U0
  U1 * u = u
  Uω * _ = Uω {-" \fi "-}
instance UVec Uses where {-" ... \iffalse "-}
  (+) = Map.unionWith (+)
  u * m = Map.map (u *) m
{-" \fi "-}
\end{code}
\end{minipage}%
\begin{minipage}{0.6\textwidth}
\begin{code}
data UT v = MkUT Uses v
instance Trace (UT v) where
  step (Look x)  (MkUT φ v)  = MkUT (singenv x U1 + φ) v
  step _         τ           = τ
instance Monad UT where
  return a = MkUT emp a
  MkUT φ1 a >>= k = let MkUT φ2 b = k a in MkUT (φ1+φ2) b
\end{code}
%if style == newcode
\begin{code}
instance Extract UT where getValue (MkUT _ v) = v
\end{code}
%endif
\end{minipage}
\\
\begin{minipage}{0.63\textwidth}
\begin{code}
evalUsg e ρ = eval e ρ :: UD

instance Domain UD where
  stuck                                  = bottom
  fun x {-" \iffalse "-}_{-" \fi "-} f   = case f (MkUT (singenv x U1) (Rep Uω)) of
    MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) v)
  apply (MkUT φ1 v1) (MkUT φ2 _)         = case peel v1 of
    (u, v2) -> MkUT (φ1 + u*φ2) v2
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = foldl apply (MkUT emp (Rep Uω)) ds
  select d fs                            =
    d >> lub  [  f (replicate (conArity k) (MkUT emp (Rep Uω)))
              |  (k,f) <- assocs fs ]

instance HasBind UD where
  bind # rhs body = body (kleeneFix rhs)
\end{code}
\end{minipage}%
\begin{minipage}{0.3\textwidth}
\begin{code}
data UValue = UCons U UValue | Rep U
type UD = UT UValue

instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
{-" \fi "-}
ifPoly (instance Lat Uses where ...)
instance Lat UValue where {-" ... \iffalse "-}
  bottom = (Rep U0)
  Rep u1 ⊔ Rep u2 = Rep (u1 ⊔ u2)
  Rep u1 ⊔ v = UCons u1 (Rep u1) ⊔ v
  v ⊔ Rep u2 = v ⊔ UCons u2 (Rep u2)
  UCons u1 v1 ⊔ UCons u2 v2 = UCons (u1 ⊔ u2) (v1 ⊔ v2)
{-" \fi "-}
instance Lat UD where {-" ... \iffalse "-}
  bottom = MkUT bottom bottom
  MkUT φ1 v1 ⊔ MkUT φ2 v2 = MkUT (φ1 ⊔ φ2) (v1 ⊔ v2)
{-" \fi "-}

peel :: UValue -> (U, UValue)
peel (Rep u)      = (u,(Rep u))
peel (UCons u v)  = (u,v)

(!?) :: Uses -> Name -> U
m !? x  | x ∈ dom m  = m ! x
        | otherwise  = U0
\end{code}
\end{minipage}
%if style == newcode
\begin{code}
deriving instance Eq U
deriving instance Eq a => Eq (UT a)
deriving instance Functor UT

instance Eq UValue where
  Rep u1 == Rep u2 = u1 == u2
  v1     == v2     = peel v1 == peel v2

instance Show U where
  show U0 = "\\concolor{\\mathsf{U_0}}"
  show U1 = "\\concolor{\\mathsf{U_1}}"
  show Uω = "\\concolor{\\mathsf{U_ω}}"

infixl 6 +
infixl 7 *

instance Show v => Show (UT v) where
  show (MkUT φ v) = "\\langle " ++ show (Map.filter (/= U0) φ) ++ ", " ++ show v ++ " \\rangle"

instance Applicative UT where
  pure a = MkUT emp a
  (<*>) = ap

instance Show UValue where
  show (Rep u) = "\\conid{Rep}\\;" ++ show u
  show (UCons u v) = show u ++ " \\argcons " ++ show v
\end{code}
%endif
\\[-1em]
\caption{Summary-based usage analysis}
\label{fig:usage-analysis}
\end{figure}

In order to recover usage analysis as an instance of our generic interpreter, we
must define its finitely represented semantic domain |UD|.
A good first step is to replace the potentially
infinite traces |T| in dynamic semantic domains such as |DName| with finite data
such as |UT| in \Cref{fig:usage-analysis}.
A \emph{usage trace} |MkUT φ val :: UT v| is a pair of a value |val :: v|
and a finite map |φ :: Uses|, mapping variables to a \emph{usage} |U|.
The usage |φ !? x| assigned to |x| is meant to approximate the number of |Look x|
events; |U0| means ``at most 0 times'', |U1| means ``at most 1 times'',
and |Uω| means ``an unknown number of times''.
%\slpj{This |φ !? x| is strange. Why bang questionmark? Later... ah, now I see
%that it's just the lookup operation, but I thought it was strange new math
%notation. I'd write |lookupUsage φ x|.}
%\sg{I'm inlinced to keep it. Here are my reasons:
%    |lookupUsage| would still not tell you how it is defined;
%    you would still need to search for it. Searching for !? is no harder.
%    Besides, space is precious, and !? is used *a lot* in the proofs of the
%    Appendix.
%    It is also the natural operator, given that we use the standard operator
%    (!) for env lookup.}
In this way, |UT| is an \emph{abstraction} of |T|: it squashes all |Look x|
events into a single entry |φ !? x :: U| and discards all other events.

Consider as an example the by-name trace evaluating $\pe \triangleq
\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$:
\[\perform{evalName (read "let i = λx.x in let j = λy.y in i j j") emp}\]
\noindent
We would like to abstract this trace into |MkUT [i ↦ U1, j ↦ Uω] dots|.
One plausible way to achieve this is to replace every |Step (Look x) dots|
in the by-name trace with a call to |step (Look x) dots| from the |Trace UT|
instance in \Cref{fig:usage-analysis}, essentially folding over the trace.
The |step| implementation increments the usage of |x| whenever a |Look x|
event occurs.
The addition operation used to carry out incrementation is defined in type class
instances |UVec U| and |UVec Uses|, together with scalar multiplication.
%\footnote{We think that |UVec| models |U|-modules. It is not a vector
%space because |U| lacks inverses, but the intuition is close enough.}
For example, |U0 + u = u| and |U1 + U1 = Uω| in |U|, as well as |U0 * u = U0|,
|Uω * U1 = Uω|.
These operations lift to |Uses| pointwise, \eg
|[i ↦ U1] + (Uω * [j ↦ U1]) = [i ↦ U1, j ↦ Uω]|.

Abstracting |T| into |UT| but keeping the concrete semantic |Value| definition
amounts to what \citet{adi} call a \emph{collecting semantics}.
To recover such an analysis-specific collecting semantics,
it is sufficient to define a |Monad| instance on |UT| mirroring trace
concatenation and then running our interpreter at, \eg $|D (ByName UT)| \cong
|UT (Value UT)|$ on expression $\pe$ from earlier:
\[
  |eval (({-"\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}"-})) emp| = \perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)}| :: D (ByName UT)|.
\]
\noindent
It is nice to explore whether the |Trace| instance encodes the desired
operational property in this way, but of little practical relevance because
this interpreter instance will diverge whenever the input expression diverges.
We will now fix this by introducing a finitely represented |UValue| to replace
|Value UT|.

\subsubsection{Value Abstraction |UValue| and Summarisation in |Domain UD|}

We complement the trace type |UT| with an abstract value type |UValue|
to get the finitely represented semantic domain |UD = UT UValue| in
\Cref{fig:usage-analysis}, and thus a \emph{static usage analysis} |evalUsg|
when we instantiate |eval| at |UD|.

%If we want to assess usage cardinality statically, we have to find a more
%abstract, finite representation of |Value|.%
%\footnote{In particular, the negative recursive occurrence in
%|Fun :: (τ (highlight Value τ) -> ...) -> Value τ| is disqualifying.}

The definition of |UValue| is just a copy of $π ∈ \Args$ in
\Cref{fig:absence} that lists argument usage |U| instead of $\Absence$ flags;
the entire intuition transfers.
For example, the |UValue| abstracting $\Lam{y}{\Lam{z}{y}}$ is
|UCons U1 (UCons U0 (Rep Uω))|, because the first argument is used once while
the second is used 0 times.
What we previously called absence types $θ ∈ \AbsTy$ in \Cref{fig:absence} is
now the abstract semantic domain |UD|.
It is now evident that usage analysis is a modest generalisation of absence
analysis in \Cref{fig:absence}:
a variable is absent ($\aA$) when it has usage |U0|, otherwise it is used
($\aU$).
%\slpj{Why generalise? It makes it a bit more complicated, and more importantly
%different, than Section 2.}
%\sg{The main reason (a year back) was to prove that we correctly approximate
%|U1| usages, which would not be possible in previous denotational semantics.
%Indeed, \Cref{thm:usage-abstracts-need-closed} proves that we do so successfully.
%But nowadays, Sec 2 proves against a small-step semantics, where the difference
%probably does not matter too much.
%Either way, I'm a bit hesitant to change it this close to submission.}

Consider
$|evalUsg (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalUsg (read "let k = λy.λz.y in k x_1 x_2") (Map.fromList [("x_1", MkUT (singenv "x_1" U1) (Rep Uω)), ("x_2", MkUT (singenv "x_2" U1) (Rep Uω))])}$,
analysing the example expression from \Cref{sec:problem}.
Usage analysis successfully infers that $x_1$ is used at most once and that
$x_2$ is absent, because it does not occur in the reported |Uses|.

%The resulting analysis is a strict generalisation of absence analysis, because
%it can infer ``at most once'' uses |U1| instead of going straight to ``many
%times'' $\aU$/|Uω|, and because it handles data types and recursive |let| as
%well.
%If we were to undo these enhancements and inlined all definitions into the
%generic interpreter, we would get the \emph{very same absence analysis}, so the
%intuition built in \Cref{sec:problem} transfers.

On the other hand,
$|evalUsg (({-" \Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~i~j}} "-})) emp|
 = \perform{evalUsg (read "let i = λx.x in let j = λy.y in i i j") emp}$
demonstrates the limitations of the first-order summary mechanism.
While the program trace would only have one lookup for $j$, the analysis is
unable to reason through the indirect call and conservatively reports that $j$
may be used many times.

The |Domain| instance is responsible for implementing the summary mechanism.
While |stuck| expressions do not evaluate anything and hence are denoted by
|bottom = MkUT emp (Rep U0)|, the |fun| and |apply| functions play exactly the same
roles as $\mathit{fun}_\px$ and $\mathit{app}$ in \Cref{fig:absence}.
Let us briefly review how the summary for the right-hand side $\Lam{x}{x}$ of
$i$ in the previous example is computed:
\begin{spec}
   eval (Lam x (Var x)) ρ =  fun x (\d -> step App2 (eval (Var x) (ext ρ x d)))
=  case step App2 (eval (Var x) (ext ρ x (MkUT (singenv x U1) (Rep Uω))))  of MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) (Rep Uω))
=  case MkUT (singenv x U1) (Rep Uω)                                       of MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) (Rep Uω))
=  MkUT emp (UCons U1 (Rep Uω))
\end{spec}
The definition of |fun x| applies the lambda body to a \emph{proxy} |(MkUT (singenv x U1) (Rep Uω))|
to summarise how the body uses its argument by way of looking at how it uses |x|.%
\footnote{As before, the exact identity of |x| is exchangeable; we use it as a
De Bruijn level.}
Every use of |x|'s proxy will contribute a usage of |U1| on |x|, and multiple
uses in the lambda body would accumulate to a usage of |Uω|.
In this case there is only a single use of |x| and the final usage |φ !? x =
U1| from the lambda body will be prepended to the value abstraction.
Occurrences of |x| unleash the uninformative top value (|Rep Uω|) from |x|'s
proxy for lack of knowing the actual argument at call sites.

The definition of |apply| to apply such summaries to an argument is nearly the
same as in \Cref{fig:absence}, except for the use of |+| instead of $⊔$ to
carry over |U1 + U1 = Uω|, and an explicit |peel| to view a |UValue| in terms
of $\argcons$ (it is $|Rep u| \equiv |UCons u (Rep u)|$).
The usage |u| thus pelt from the value determines how often the actual
argument was evaluated, and multiplying the uses of the argument |φ2| with |u|
accounts for that.

The example
$|evalUsg (({-" \Let{z}{Z()}{\Case{S(z)}{S(n) → n}} "-})) emp|
 = \perform{evalUsg (read "let z = Z() in case S(z) of { S(n) -> n }") emp}$
illustrates the summary mechanism for data types.
Our analysis imprecisely infers that |z| might be used many times when it is
only used once.%
\footnote{Following \citet{Sergey:14} we could model \emph{demand} as
a property of evaluation contexts and propagate uses of field binders to the
scrutinee's fields to do better.}
This is achieved in |con| by repeatedly |apply|ing to the top value |(Rep Uω)|,
as if a data constructor was a lambda-bound variable.
Dually, |select| does not need to track how fields are used and can pass |MkUT
emp (Rep Uω)| as proxies for field denotations.
The result uses anything the scrutinee expression used, plus the upper bound of
uses in case alternatives, one of which will be taken.

Note that the finite representation of the type |UD| rules out injective
implementations of |fun x :: (UD -> UD) -> UD| and thus requires the
aforementioned \emph{approximate} summary mechanism.
There is another potential source of approximation: the |HasBind|
instance discussed next.

\begin{figure}
\begin{spec}
class Eq a => Lat a where bottom :: a; (⊔) :: a -> a -> a;
kleeneFix :: Lat a => (a -> a) -> a; qquad lub :: Lat a => [a] -> a
kleeneFix f = go bottom where go x = let x' = f x in if x' ⊑ x then x' else go x'
\end{spec}
\\[-1em]
\caption{Order theory and Kleene iteration}
\label{fig:lat}
\end{figure}

\subsubsection{Finite Fixpoint Strategy in |HasBind UD| and Totality}
\label{sec:usage-fixpoint}

The third and last ingredient to recover a static analysis is the fixpoint
strategy in |HasBind UD|, to be used for recursive let bindings.

For the dynamic semantics in \Cref{sec:interp} we made liberal use of
\emph{guarded fixpoints}, that is, recursively defined values such as |let d =
rhs d in body d| in |HasBind DName| (\Cref{fig:eval}).
At least for |evalName| and |evalNeed2|, we have proved in \Cref{sec:adequacy}
that these fixpoints always exist by a coinductive argument.
Alas, among other things this argument relies on the |Step| constructor --- and
thus the |step| method --- of the trace type |T| being \emph{lazy} in
the tail of the trace!

When we replaced |T| in favor of the finite data type |UT| in
\Cref{sec:usage-trace-abstraction} to get a collecting semantics |D (ByName
UT)|, we got a partial interpreter.
That was because the |step| implementation of |UT| is \emph{not} lazy, and hence
the guarded fixpoint |let d = rhs d in body d| is not guaranteed to exist.

In general, finite data trace types cannot have a lazy |step|
implementation, so finite data domains such as |UD| require a different fixpoint
strategy to ensure termination.
Depending on the abstract domain, different fixpoint strategies can be employed.
For an unusual example, in our type analysis \Cref{sec:type-analysis}, we
generate and solve a constraint system via unification to define fixpoints.
In case of |UD|, we compute least fixpoints by Kleene iteration |kleeneFix|
in \Cref{fig:lat}.
|kleeneFix| requires us to define an order on |UD|, which is induced
by |U0 ⊏ U1 ⊏ Uω| in the same way that the order
on $\AbsTy$ in \Cref{sec:absence} was induced from the order $\aA ⊏ \aU$
on $\Absence$ flags.

The iteration procedure terminates whenever the type class instances of |UD| are
monotone and there are no infinite ascending chains in |UD|.
Alas, our |UValue| indeed contains such infinite chains, for example, |UCons U1
(UCons U1 (UCons dots Rep U0))|!
This is easily worked around in practice by employing appropriate monotone
widening measures such as trimming any |UValue| at depth 10 to flat |Rep Uω|.
The resulting definition of |HasBind| is safe for by-name and by-need semantics.%
%\footnote{Never mind totality; why is the use of \emph{least} fixpoints even correct?
%The fact that we are approximating a safety property~\citep{Lamport:77} is
%important.
%We discuss this topic in \Cref{sec:safety-extension}.}

\subsection{Type Analysis: Algorithm J}
\label{sec:type-analysis}

\begin{figure}
\belowdisplayskip0pt
\begin{code}
data TyCon = BoolTyCon | NatTyCon | OptionTyCon | PairTyCon
data Type = Type :->: Type | TyConApp TyCon [Type] | TyVar Name | Wrong
data PolyType = PT [Name] Type

evalTy e = closedType (eval e emp) :: PolyType

type Subst = Name :-> Type; type Constraint = (Type, Type)
newtype J a = J (StateT (Set Name,Subst) Maybe a)
freshTyVar :: J Type; qquad         instantiatePolyTy  :: PolyType -> J Type
unify :: Constraint -> J (); qquad  generaliseTy       :: J Type -> J PolyType
closedType :: J Type -> PolyType {-" \iffalse "-}
closedType d = runJ (generaliseTy d)
{-" \fi "-}; qquad                  instance Trace (J v) where step _ = id
instance Domain (J Type) where
  stuck                                 =  return Wrong
  fun _ {-" \iffalse "-}_{-" \fi "-} f  =  do θα <- freshTyVar; θ <- f (return θα); return (θα :->: θ)
  apply v a                             =  do θ1  <- v; θ2  <- a; θα  <- freshTyVar; unify (θ1, θ2 :->: θα); return θα {-" \iffalse "-}
  con _ k ds = do
    con_app_ty <- instantiateCon k
    arg_tys <- sequence ds
    res_ty <- freshTyVar
    unify (con_app_ty, foldr (:->:) res_ty arg_tys)
    return res_ty
  select dv fs = case Map.assocs fs of
    []            -> stuck
    fs@((k,_):_)  -> do
      con_ty <- dv
      res_ty <- snd . splitFunTys <$> instantiateCon k
      let TyConApp tc tc_args = res_ty
      unify (con_ty, res_ty)
      ks_tys <- enumerateCons tc tc_args
      tys <- forM ks_tys (\(k,tys) ->
        case List.find (\(k',_) -> k' == k) fs of
          Just (_,f) -> f tys
          _          -> stuck)
      case tys of
        []      -> stuck
        ty:tys' -> mapM (\ty' -> unify (ty,ty')) tys' >> return ty
{-" \fi "-}
uniFix :: (J Type -> J Type) -> J Type
uniFix rhs = do θα <- freshTyVar; θ <- rhs (return θα); unify (θα, θ); return θα
instance HasBind (J Type) where
  bind # rhs body = do σ <- generaliseTy (uniFix rhs); body (instantiatePolyTy σ)
\end{code}
\vspace{-1em}
\caption{Type analysis with let generalisation (Algorithm J)}
\label{fig:type-analysis}
\end{figure}

%if style == newcode
\begin{code}
deriving instance Eq TyCon
deriving instance Enum TyCon
deriving instance Bounded TyCon
deriving instance Eq Type
deriving instance Functor J

runJ :: J PolyType -> PolyType
runJ (J m) = case evalStateT m (Set.empty, emp) of Just ty -> ty; Nothing -> PT [] Wrong

instance Applicative J where
  pure = J . pure
  (<*>) = ap

instance Monad J where
  J m >>= k = J (m >>= unJ . k)

instance Show TyCon where
  show BoolTyCon = "\\texttt{bool}"
  show NatTyCon = "\\texttt{nat}"
  show OptionTyCon = "\\texttt{option}"
  show PairTyCon = "\\times"

instance Show Type where
  showsPrec _ (TyConApp k tys) = showsPrec 0 k . foldr (\t s -> showString "\\;" . showsPrec 1 t . s) id tys
  showsPrec _ (TyVar x)  = showString x
  showsPrec _ Wrong      = showString "\\textbf{wrong}"
  showsPrec p (l :->: r) =
    showParen (p > 0) $ showsPrec 1 l . showString " \\rightarrow " . showsPrec 0 r

instance Show PolyType where
  showsPrec _ (PT [] body) = shows body
  showsPrec _ (PT alphas body) = showString "\\forall" . showSep (showString ",") (map showString alphas) . showString ".\\ " . shows body

freeVars :: Type -> Set Name
freeVars (TyVar x) = Set.singleton x
freeVars (a :->: r) = freeVars a `Set.union` freeVars r
freeVars (TyConApp _ as) = Set.unions (map freeVars as)
freeVars Wrong = Set.empty

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = go [] ty
  where
    go as (a :->: r) = go (a:as) r
    go as ty = (reverse as, ty)

conTy :: Tag -> PolyType
conTy TT = PT [] (TyConApp BoolTyCon [])
conTy FF = PT [] (TyConApp BoolTyCon [])
conTy Z = PT [] (TyConApp NatTyCon [])
conTy S = PT [] (TyConApp NatTyCon [] :->: TyConApp NatTyCon [])
conTy None = PT ["a_none"] (TyConApp OptionTyCon [TyVar "a_none"])
conTy Some = PT ["a_some"] (TyVar "a_some" :->: TyConApp OptionTyCon [TyVar "a_some"])
conTy Pair = PT ["a_pair", "b_pair"]
  (TyVar "a_pair" :->: TyVar "b_pair" :->: TyConApp PairTyCon [TyVar "a_pair", TyVar "b_pair"])

tyConTags :: TyCon -> [Tag]
tyConTags tc =
  [ k | k <- [minBound..maxBound]
      , let PT _ ty = conTy k
      , TyConApp tc' _ <- [snd (splitFunTys ty)]
      , tc == tc' ]

applySubst :: Subst -> Type -> Type
applySubst subst ty@(TyVar y)
  | Just ty <- Map.lookup y subst = ty
  | otherwise                   = ty
applySubst subst (a :->: r) =
  applySubst subst a :->: applySubst subst r
applySubst subst (TyConApp k tys) =
  TyConApp k (map (applySubst subst) tys)
applySubst _ ty = ty

unJ :: J a -> StateT (Set Name,Subst) Maybe a
unJ (J m) = m

addCt (l,r) subst = case (applySubst subst l, applySubst subst r) of
  (l, r) | l == r -> Just subst
  (TyVar x, ty)
    | not (occurs x ty)
    -> Just (Map.insert x ty subst)
  (_, TyVar _) -> addCt (r,l) subst
  (a1 :->: r1, a2 :->: r2) -> addCt (a1,a2) subst >>= addCt (r1,r2)
  (Wrong, Wrong) -> Just subst
  (TyConApp k1 tys1, TyConApp k2 tys2) | k1 == k2 -> foldrM addCt subst (zip tys1 tys2)
  _ -> Nothing
  where
    occurs x ty = applySubst (singenv x ty) ty /= ty -- quick and dirty

unify ct = J $ StateT $ \(names,subst) -> case addCt ct subst of
  Just subst' -> Just ((), (names, subst'))
  Nothing     -> Nothing

freshTyVar = J $ state $ \(ns,subst) ->
  let n = "\\alpha_{" ++ show (Set.size ns) ++ "}"
  in (TyVar n,(Set.insert n ns,subst))

freshenVars :: [Name] -> J Subst
freshenVars alphas = foldM one emp alphas
  where
    one subst alpha = do
      beta <- freshTyVar
      pure (ext subst alpha beta)

instantiatePolyTy (PT alphas ty) = do
  subst <- freshenVars alphas
  return (applySubst subst ty)

instantiateCon :: Tag -> J Type
instantiateCon k = instantiatePolyTy (conTy k)

enumerateCons :: TyCon -> [Type] -> J [(Tag,[J Type])]
enumerateCons tc tc_arg_tys = forM (tyConTags tc) $ \k -> do
  ty <- instantiateCon k
  let (field_tys,res_ty) = splitFunTys ty
  unify (TyConApp tc tc_arg_tys, res_ty)
  return (k, map pure field_tys)

generaliseTy (J m) = J $ do
  (outer_names,_) <- get
  ty <- m
  (_names',subst) <- get
  let ty' = applySubst subst ty
  let one n = freeVars $ applySubst subst (TyVar n)
  let fvΓ = Set.unions (Set.map one outer_names)
  let generics = freeVars ty' `Set.difference` fvΓ
  return (PT (Set.toList generics) ty')
\end{code}
%endif

Computing least fixpoints is common practice in static program analysis.
However, some abstract domains employ quite different fixpoint strategies.
The abstract domain of the type analysis we define in this subsection is
an interesting example:
Type analysis --- specifically, \citeauthor{Milner:78}'s Algorithm~J ---
computes fixpoints by generating and solving a constraint system via
unification.
Furthermore, since the domain is familiar, it is a good one to study in the
context of denotational interpreters.

\Cref{fig:type-analysis} outlines the abstract domain |J Type| at which the
generic denotational interpreter can be instantiated to perform Type analysis.
We omit implementational details that are derivative of Milner's description of
Algorithm~J.
The full implementation can be found in the extract generated from this
document, but the provided code is sufficiently exemplary of the approach.

Type analysis |evalTy| infers the most general Hindley-Milner polytype of an expression, \eg
\[|evalTy (({-" \Let{i}{\Lam{x}{x}}{\Let{o}{\mathit{Some}(i)}{o}} "-})|
  = \perform{evalTy (read "let i = λx.x in let o = Some(i) in o")}.\]
The most general type can be \emph{polymorphic} when it universally quantifies
over \emph{generic} type variables such as $α_6$ above.
In general, such a |PolyType| is of the form $\forall \many{\alpha}.\ θ$,
where $θ$ ranges over a monomorphic |Type| that can be either a type variable
|TyVar α| (we use |θα| as meta variable for this form), a function type
|θ1 :->: θ2|, or a type constructor application |TyConApp|, where
|TyConApp OptionTyCon [θ1]| is printed as $\mathtt{option}~θ_1$.
The |Wrong| type indicates a type error and is printed as $\textbf{wrong}$.

Type |J| implements these effects by maintaining a unifying substitution and
a set of used names via the standard monad transformer |StateT|.
Unification failure is signalled by returning |Nothing| in the base monad
|Maybe|, and function |closedType| for handling |J| effects will return |Wrong|
when that happens:
\[|evalTy (({-" \Let{x}{\mathit{None}()}{x~x} "-}))|
  = \perform{evalTy (read "let x = None() in x x")}.\]
Throughout the analysis, the invariant is maintained that the |J Type|
summaries of let-bound variables in the interpreter environment |ρ| are of the
form |instantiatePolyTy σ| for a polytype |σ|, while lambda- and field-bound
variables are denoted by |return θ|, yielding the same monotype |θ| at all use
sites.
(Use of the term ``summary'' is justified because both |σ| and |θ| are data,
and it would be easy to defunctionalise |instantiatePolyTy σ| and |return θ|
to be data as well.)
Thus, let-bound denotations instantiate polytypes on-the-fly at occurrence
sites, just as in Algorithm~J.

The |Domain (J Type)| instance bears no surprises:
|stuck| terms are denoted by the monotype |Wrong| and the definition of |fun|
and |apply| are literal translations of Algorithm~J.

The generalisation machinery comes to bear in the implementation
of |bind|, which implements a combination of the $\mathit{fix}$ and $\mathit{let}$
cases in Algorithm~J, computing fixpoints by unification (|uniFix|).

\begin{toappendix}
\subsection{Control-flow Analysis}
\label{sec:0cfa}

\begin{figure}
\belowdisplayskip=0pt
\begin{code}
evalCFA e = runCFA (eval e emp); ^^ runCFA :: CD -> Labels
newtype Labels = Lbls (Set Label)
type CD = State Cache Labels
data Cache = Cache (Label :-> ConCache) (Label :-> FunCache)
type ConCache = (Tag, [Labels])
data FunCache = FC (Maybe (Labels, Labels)) (CD -> CD)

updConCache :: Label -> Tag -> [Labels] -> State Cache ()
updFunCache :: Label -> (CD -> CD) -> State Cache ()
cachedCall :: Labels -> Labels -> CD
cachedCons :: Labels -> State Cache (Tag :-> [Labels])

instance HasBind CD where{-" ... \iffalse "-}
  bind # rhs body = go bottom >>= body . return
    where
      go :: Labels -> CD
      go v = do
        cache <- get
        v' <- rhs (return v)
        cache' <- get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- rhs (return v'); if v' /= v'' then error "blah" else return v' } else go v'
{-" \fi "-}
instance Trace CD where step _ = id
instance Domain CD where
  stuck = return bottom
  fun _ ell f = do
    updFunCache ell f
    return (Lbls (Set.singleton ell))
  apply dv da = do
    v <- dv
    a <- da
    cachedCall v a
  con ell k ds = do
    lbls <- sequence ds
    updConCache ell k lbls
    return (Lbls (Set.singleton ell))
  select dv fs = do
    v <- dv
    tag2flds <- cachedCons v
    lub <$> sequence  [  f (map return (tag2flds ! k))
                      |  (k,f) <- Map.assocs fs, k ∈ dom tag2flds ]
\end{code}

%if style == newcode
\begin{code}
deriving instance Eq Labels
deriving instance Ord Labels
instance Lat Labels where
  bottom = Lbls Set.empty
  Lbls l ⊔ Lbls r = Lbls (Set.union l r)

instance Show Labels where
  showsPrec _ (Lbls s) =
    showString "\\{" . showSep (showString ", ") (map showString (Set.toList s)) . showString "\\}"

instance Eq FunCache where
  FC cache1 _ == FC cache2 _ = cache1 == cache2
instance Lat FunCache where
  bottom = FC Nothing (const (return bottom))
  FC cache1 f1 ⊔ FC cache2 f2 = FC cache' f'
    where
      f' d = do
        v <- d
        lv <- f1 (return v)
        rv <- f2 (return v)
        return (lv ⊔ rv)
      cache' = case (cache1,cache2) of
        (Nothing, Nothing)            -> Nothing
        (Just c1, Nothing)            -> Just c1
        (Nothing, Just c2)            -> Just c2
        (Just (in_1,out1), Just (in_2,out2))
          | in_1 ⊑ in_2, out1 ⊑ out2  -> Just (in_2, out2)
          | in_2 ⊑ in_1, out2 ⊑ out1  -> Just (in_1, out1)
          | otherwise                 -> error "uh oh"

instance Show FunCache where
  show (FC Nothing _)           = "[]"
  show (FC (Just (in_, out)) _) = "[" ++ show in_ ++ " \\mapsto " ++ show out ++ "]"

instance Eq Cache where
  c1 == c2 = cFuns c1 == cFuns c2 && cCons c1 == cCons c2

instance Lat Cache where
  bottom = Cache Map.empty Map.empty
  c1 ⊔ c2 = Cache (f cCons) (f cFuns)
    where
      f :: Lat fld => (Cache -> fld) -> fld
      f fld = fld c1 ⊔ fld c2

deriving instance Show Cache

runCFA m = evalState m (Cache bottom bottom)

-- | This instance is a huge hack, but it works.
-- If we were serious, we should have used the flat lattice over `Tag`.
instance Lat Tag where
  bottom = error "no bottom Tag"
  k1 ⊔ k2 = if k1 /= k2 then error "k1 /= k2" else k1

instance Lat a => Lat [a] where
  bottom = []
  [] ⊔ ys = ys
  xs ⊔ [] = xs
  (x:xs) ⊔ (y:ys) = x ⊔ y : xs ⊔ ys

cCons :: Cache -> Label :-> ConCache
cCons (Cache cons _) = cons

overCons :: ((Label :-> ConCache) -> (Label :-> ConCache)) -> Cache -> Cache
overCons f (Cache cons funs) = Cache (f cons) funs

cFuns :: Cache -> Label :-> FunCache
cFuns (Cache _ funs) = funs

overFuns :: ((Label :-> FunCache) -> (Label :-> FunCache)) -> Cache -> Cache
overFuns f (Cache cons funs) = Cache cons (f funs)

updConCache ell k vs = modify $ overCons $ \cons ->
  Map.singleton ell (k, vs) ⊔ cons

updFunCache ell f = modify $ overFuns $ \funs ->
  Map.singleton ell (FC Nothing f) ⊔ funs

cachedCall (Lbls ells) v = fmap lub $ forM (Set.toList ells) $ \ell -> do
  FC cache f <- gets (Map.findWithDefault bottom ell . cFuns)
  let call in_ out = do
        let in_' = in_ ⊔ v      com merge all Labels that reach the lambda var ell!
        modify $ overFuns (Map.insert ell (FC (Just (in_',out)) f))
        out' <- f (return in_')
        modify $ overFuns (Map.insert ell (FC (Just (in_',out')) f))
        return out'
  case cache of
    Just (in_,out)
      | v ⊑ in_   -> return out
      | otherwise -> call in_ out
    Nothing       -> call bottom bottom

cachedCons (Lbls ells) = do
  cons <- cCons <$> get
  return $ Map.fromListWith (⊔) [ cons ! ell | ell <- Set.toList ells, ell ∈ dom cons ]
\end{code}
%endif
\caption{Domain |CD| for 0CFA control-flow analysis}
\label{fig:cfa}
\end{figure}

Traditionally, control-flow analysis (CFA)~\citep{Shivers:91} is an important
instance of higher-order abstract interpreters~\citep{aam,adi}.
Although one of the main advantages of denotational interpreters is that
summary-based analyses can be derived as instances, this subsection demonstrates
that a call-strings-based CFA can be derived as an instance from the generic
denotational interpreter in \Cref{fig:eval} as well.

CFA overapproximates the set of syntactic values an expression evaluates to,
so as to narrow down the possible control-flow edges at application sites.
The resulting control-flow graph conservatively approximates the control-flow of
the whole program and can be used to apply classic intraprocedural analyses such
as interval analysis or constant propagation in an interprocedural setting.

\Cref{fig:cfa} implements the 0CFA variant of control-flow analysis~\citep{Shivers:91}.
For a given expression, it reports a set of \emph{program labels} --- textual
representations of positions in the program ---
that the expression might evaluate to:
\begin{align}|evalCFA (({-" \Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}} "-}))|
  = \perform{evalCFA (read "let i = λx.x in let j = λy.y in i j j")} \label{ex:cfa}\end{align}
Here, 0CFA infers that the example expression will evaluate to the lambda
expression bound to $j$.
This lambda is uniquely identified by the reported label $λy..$ per the unique
binder assumption in \Cref{sec:lang}.
Furthermore, the analysis determined that the expression cannot evaluate to the
lambda expression bound to $i$, hence its label $λx..$ is \emph{not} included
in the set.

By contrast, when $i$ is dynamically called both with $i$ and with $j$, the
result becomes approximate because 0CFA joins together the information from the
two call sites:
\[|evalCFA (({-" \Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~\highlight{i}~j}} "-}))|
  = \perform{evalCFA (read "let i = λx.x in let j = λy.y in i i j")}\]

Labels for constructor applications simply print their syntax, \eg
\begin{equation}\thickmuskip=4mu|evalCFA (({-" \Let{x}{\Let{y}{S(x)}{S(y)}}{\Case{x}{\{ Z() \to x; S(z) \to z \}}} "-}))|
  = \perform{evalCFA (read "let x = let y = S(x) in S(y) in case x of { Z() -> x; S(z) -> z }")}.\label{ex:cfa2} \end{equation}
Note that in this example, 0CFA discovers that $x$ evaluates to $S(y)$ and hence
is able to conclude that the $Z()$ branch of the case expression is dead.
In doing so, 0CFA rules out that the expression evaluates to $S(y)$,
reporting $S(x)$ as the only value of the expression.

In general, the label (\ie string) $S(y)$ does not uniquely determine a position
in the program because the expression may occur multiple times.
However, eliminating such common subexpressions is semantics-preserving, so
We argue that this poor man's notion of program labels is good enough for the
purpose of this demonstration.

To facilitate 0CFA as an instance of the generic denotational interpreter, we
need to slightly revise the |Domain| class to pass the syntactic label to |fun|
and |con|:
\begin{spec}
type Label = String
class Domain d where
  con  :: highlight Label -> Tag -> [d] -> d
  fun  :: Name -> highlight Label -> (d -> d) -> d
\end{spec}
\noindent
Constructing and forwarding labels appropriately in |eval| and adjusting
previous |Domain| instances is routine and hence omitted.

\Cref{fig:cfa} represents sets of labels with the type |Labels|, the
type of abstract values of the analysis.
The abstract domain |CD| of 0CFA is simply a stateful computation returning |Labels|.
To this end, we define |CD| in terms of the standard |State| monad to mutate a
|Cache|, an abstraction of the heap discussed next.

\medskip

Recall that each |Label| determines a syntactic value in the program.
The |Cache| maintains, for every labelled value encountered thus far, an
approximation of its action on |Labels|.

For example, the denotational interpreter evaluates the constructor application
$S(y)$ in the right-hand side of $x$ in \Cref{ex:cfa2} by calling
the |Domain| method |con|.
This call is implemented by updating the |ConCache| field under the label $S(y)$
so that it carries the constructor tag $S$ as well as the |Labels| that its
field $y$ evaluates to. In our example, $y$ evaluates to the set $\{S(x)\}$,
so the |ConCache| entry at label $S(y)$ is updated to $(S,[\{S(x)\}])$.
This information is then available when evaluating the $\mathbf{case}$ expression
in \Cref{ex:cfa2} with |select|, where the scrutinee $x$ returns $|v| \triangleq \{S(y)\}$.
Function |cachedCons| looks up for each label in |v| the respective |ConCache|
entry and merges these entries into an environment
|tag2flds :: Tag :-> [Labels]|, representing all the possible shapes the
scrutinee can take.
In our case, |tag2flds| is just a singleton environment $[S ↦ [\{S(x)\}]]$.
This environment is subsequently joined with the alternatives of the case expression.
The only alternative that matches is $S(z) \to z$, where $z$ is bound to $\{S(x)\}$
from the information in the |ConCache|.
The alternative $Z() \to x$ is dead because |v| does not contain a label $Z()$.

For another example involving the |FunCache|, consider the example \Cref{ex:cfa}.
When the lambda expression $\Lam{x}{x}$ in the right-hand side of $i$ is
evaluated through |fun|, it updates the |FunCache| at label $λx..$ with
the corresponding abstract transformer |(\x -> x) :: CD -> CD|, registering it
for call sites.
Later, the application site $i~j$ in \Cref{ex:cfa} is evaluated to a call to
the |Domain| method |apply| with the denotations of $i$ and $j$.
The denotation for $i$ is bound to |dv| and returns a set $|v| \triangleq \{λx..\}$, while
the denotation for $j$ is bound to |da| and returns a set $|a| \triangleq \{λy..\}$.
These sets are passed to |cachedCall| which iterates over the labels in the
callee |v|.
For each such label, it looks up the abstract transformer in |FunCache|, applies
it to the set of labels |a| (taking approximative measures described below) and
joins together the labels returned from each call.
In our example, there is just a single callee label $λx..$, the abstract transformer
of which is the identity function |(\x -> x) :: CD -> CD|.
Applying the identity transformer to the set of labels $\{λy..\}$ from the
denotation of the argument $j$ returns this same set; the result of the
application $i~j$.

The above description calls a function label's abstract transformer anew at
every call site.
This yields the exact control-flow semantics of the original control-flow
analysis work~\citep[Section 3.4]{Shivers:91}, which is potentially diverging.
The way 0CFA (and our implementation of it) becomes finite is by maintaining only
a single point approximation of each abstract transformer's graph ($k$-CFA would
maintain one point per contour).
This single point approximation can be seen as the transformer's summary, but
this summary is \emph{call-site sensitive}:
Since the single point must be applicable at all call sites, the function body
must be reanalysed as the inputs from call sites increase.
Maintaining the single point approximation is the purpose of the |Maybe (Labels,
Labels)| field of the |FunCache| and is a standard, if somewhat delicate hassle
in control-flow analyses.

Note that the given formulation of 0CFA is not modular; that is, the single point
approximation for a function |A.f| is not generally applicable at a call site
in module |B| such as |A.f B.x| because the labels that |B.x| evaluate to
might not be known when compiling module |A|.
\citet[Section 3.8.2]{Shivers:91} proposes a solution to this problem that
we chose not to implement for the simple proof of concept here.

%A function like $\Lam{x}{y}$ might be re-analysed multiple times with
%monotonically increasing environment due to fixpoint iteration in |bind|.
%Whenever that happens, the point that has been cached for that allocation
%site is cleared, because the function might have increased its result.
%Then re-evaluating the function at the next |cachedCall| is mandatory.

Note that a |CD| transitively (through |Cache|) recurses into |CD -> CD|,
rendering the encoding non-inductive due to the negative occurrence.
This highlights a common challenge with instances of CFA:
the obligation to prove that the analysis actually terminates on all inputs; an
obligation that we will gloss over in this short demonstration.

\subsection{Stateful Analysis and Annotations}
\label{sec:annotations}

\begin{figure}
\hfuzz=2em
\belowdisplayskip=0pt
\begin{code}
class Domain d => StaticDomain d where
  type Ann d   :: *
  extractAnn   :: Name -> d -> (d, Ann d)
  funS         :: Monad m => Name -> {-" \iffalse "-} Label -> {-" \fi "-} (m d -> m d) -> m d
  selectS      :: Monad m => m d -> (Tag :-> ([m d] -> m d)) -> m d
  bindS        :: Monad m => Name -> d -> (d -> m d) -> (d -> m d) -> m d

instance StaticDomain UD where
  type Ann UD = U
  extractAnn x (MkUT φ v) = (MkUT (Map.delete x φ) v, φ !? x)
  funS x # f = do
    MkUT φ v <- f (return (MkUT (singenv x U1) (Rep Uω)))
    return (MkUT (ext φ x U0) (UCons (φ !? x) v))
  selectS md mfs = do
    d <- md
    alts <- sequence  [  f (replicate (conArity k) (return (MkUT emp (Rep Uω))))
                      |  (k,f) <- Map.assocs mfs ]
    return (d >> lub alts)
  bindS _ init rhs body = kleeneFixAboveM init rhs >>= body

ifPoly(kleeneFixAboveM :: (Monad m, Lat a) => a -> (a -> m a) -> m a)

evalUsgAnn e ρ = runAnn (eval e (return << ρ)) :: (UD, Name :-> U)

data Refs s d = Refs (STRef s (Name :-> d)) (STRef s (Name :-> Ann d))
newtype AnnT s d a = AnnT (Refs s d -> ST s a); type AnnD s d = AnnT s d d
runAnn    :: (forall s. AnnD s d) -> (d, Name :-> Ann d)

ifPoly(instance Monad (AnnT s d) where ...)

instance Trace d => Trace (AnnD s d) where
  step ev (AnnT f) = AnnT (\refs -> step ev <$> f refs)

instance StaticDomain d => Domain (AnnD s d) where {-" ... \iffalse "-}
  stuck = return stuck
  fun x l f = funS x l f
  con l k ds = con l k <$> sequence ds
  apply f d = apply <$> f <*> d
  select md mfs = selectS md mfs {-" \fi "-}

readCache   :: Lat d => Name -> AnnD s d
writeCache  :: Name -> d -> AnnT s d ()
annotate    :: StaticDomain d => Name -> AnnD s d -> AnnD s d

instance (Lat d, StaticDomain d) => HasBind (AnnD s d) where
  bind x rhs body = do
    init <- readCache x
    let rhs' d1 = do d2 <- rhs (return d1); writeCache x d2; return d2
    annotate x (bindS x init rhs' (body . return))
\end{code}
%if style == newcode
\begin{code}
runAnn m = runST $ do
  r@(Refs _ anns) <- Refs <$> newSTRef emp <*> newSTRef emp
  d <- case m of AnnT f -> f r
  anns <- readSTRef anns
  return (d, anns)

deriving via ReaderT (Refs s d) (ST s) instance Functor (AnnT s d)
deriving via ReaderT (Refs s d) (ST s) instance Applicative (AnnT s d)
deriving via ReaderT (Refs s d) (ST s) instance Monad (AnnT s d)

readCache n = AnnT $ \(Refs cache _) -> do
  c <- readSTRef cache
  return (Map.findWithDefault bottom n c)

writeCache n d = AnnT $ \(Refs cache _) ->
  modifySTRef' cache $ \c -> ext c n d

annotate x ad = do
  d <- ad
  let (d', ann) = extractAnn x d
  AnnT $ \(Refs _ anns) -> modifySTRef' anns $ \a -> ext a x ann
  return d'

instance {-# OVERLAPS #-} Show (UD, Name :-> U) where
  show (d, anns) = show d ++ " \\leadsto " ++ show anns
\end{code}
%endif
\caption{Trace transformer |AnnT| for recording annotations and caching of fixpoints}
\label{fig:annotations}
\end{figure}

Thus far, the static analyses derived from the generic denotational interpreter
produce a single abstract denotation |d := eval e emp| for the program
expression |e|.
However, in practice static compiler analyses such as Demand Analysis usually
drive a subsequent optimisation, for which a single denotation for the entire
program is insufficient.
Rather, we need one for every sub-expression, or at least every binding.

If we are interested in analysis results for variables \emph{bound} in
|e|, then either the analysis must collect these results in |d|, or we must
redundantly re-run the analysis for subexpressions.

In this subsection we show how to lift a pure, \emph{single-result} analysis into a
\emph{stateful} analysis that gives results for every binder, such that
\begin{itemize}
  \item it collects analysis results for bound variables in a separate, global map, and
  \item it caches fixpoints in yet another global map, so that nested fixpoint
    iteration can be sped up by starting from a previous approximation.
\end{itemize}
It is a common pattern for analyses to be stateful in this
way~\citep{Sergey:14}; GHC's Demand Analysis is a good real-world example.
The following demonstration targets usage analysis, but the technique should be
easy to adapt for other analyses discussed in this section.

\subsubsection{The Need for Isolating Bound Variable Usage}

For a concrete example, let us compare the results of usage analysis
from \Cref{sec:usage-analysis} on the expression $\pe_1 \triangleq
\Let{i}{\Lam{x}{\Let{j}{\Lam{y}{y}}{j}}}{i~i~i}$ and its subexpression
$\pe_2 \triangleq \Let{j}{\Lam{y}{y}}{j}$:
\[\begin{array}{lcl}
|evalUsg (({-" \Let{i}{\Lam{x}{\Let{j}{\Lam{y}{y}}{j}}}{i~i~i} "-})) emp|
 & = & \perform{evalUsg (read "let i = λx. let j = λy.y in j in i i i") emp} \\
|evalUsg (({-" \Let{j}{\Lam{y}{y}}{j} "-})) emp|
 & = & \perform{evalUsg (read "let j = λy.y in j") emp}
\end{array}\]
The analysis reports a different usage |U1| for the bound variable $j$ in the
subexpression $\pe_2$ versus |Uω| in the containing expression $\pe_1$.
This is because in order for single-result usage analysis to report information
on \emph{bound} variable $j$ at all, it treats $j$ like a \emph{free} variable
of $i$, adding a use on $j$ for every call of $i$.
While this treatment reflects that multiple $\LookupT(j)$ events
will be observed when evaluating $\pe_1$, each event associates to a
\emph{different} activation (\ie heap entry) of the let binding $j$.
The result |U1| reported for $j$ in subexpression $\pe_2$ is more useful
because it reflects that every \emph{activation} of the binding
$j$ is looked up at most once over its lifetime, which is indeed the formal
property of interest in \Cref{sec:soundness}.

Rather than to re-run the analysis for every let binding such as $j$, we will
now demonstrate a way to write out an \emph{annotation} for $j$, just before
analysis leaves the $\mathbf{let}$ that binds $j$.
Annotations for bound variables constitute analysis state that will be
maintained separately from information on free variables.

\subsubsection{Maintaining Annotations by Implementing |StaticDomain|}

\Cref{fig:annotations} lifts the existing definition for single-result usage
analysis |evalUsg| into a stateful analysis |evalUsgAnn| that writes out usage
information on bound variables into a separate map.
Consider the result on the example expression $\pe_1$ from above, where the pair
$(d, \mathit{anns})$ returned by |evalUsgAnn| is printed as $d \leadsto \mathit{anns}$:
\[\thickmuskip=4mu|evalUsgAnn (({-" \Let{i}{\Lam{x}{\Let{j}{\Lam{y}{y}}{j}}}{i~i~i} "-})) emp|
 = \perform{evalUsgAnn (read "let i = λx. let j = λy.y in j in i i i") emp} \]
The annotations for both bound variables $i$ and $j$ are returned in an
annotation environment separate from the empty abstract free variable
environment |emp :: Uses| of the expression.
Furthermore, the use |U1| reported for $j$ is exactly as when analysing the
subexpression $\pe_2$ in isolation, as required.

Lifting the single-result analysis |evalUsg| defined on |UD| to a stateful
analysis |evalUsgAnn| requires very little extra code, implementing a type class instance |StaticDomain
UD|.
Before going into detail about how this lifting is implemented in terms of type
|AnnT|, let us review its type class interface.
The type class |StaticDomain| defines the associated type |Ann| of annotations
in the particular static domain, along with a function |extractAnn x d| for
extracting information on a let-bound |x| from the denotation |d|.
The instance for |UD| instantiates |Ann UD| to bound variable use |U|, and
|extractAnn x (MkUT φ v)| isolates the free variable use |φ ! x| as annotation.
The remaining type class methods |funS|, |selectS| and |bindS| are
simple monadic generalisations of their counterparts in |Domain| and |HasBind|.

The implementation of |StaticDomain| requires very little extra code to
maintain, because the original definitions of |fun|, |select| and |bind| can be
recovered in terms of the generalised definitions via the standard |Identity|
monad as follows, where |coerce| denotes a safe zero-cost coercion function
provided by GHC~\citep{Breitner:14}:
\begin{code}
ifPoly(newtype Identity a = Identity { runIdentity :: a })

fun' :: StaticDomain d => Name -> Label -> (d -> d) -> d
fun' x # f = runIdentity (funS x # (coerce f))
select' :: StaticDomain d => d -> (Tag :-> ([d] -> d)) -> d
select' d fs = runIdentity (selectS (Identity d) (coerce fs))
bind' :: (Lat d, StaticDomain d) => Name -> (d -> d) -> (d -> d) -> d
bind' x rhs body = runIdentity (bindS x bottom (coerce rhs) (coerce body))
\end{code}
Any reasonable instance of |StaticDomain| must satisfy the laws |fun = fun'|,
|select = select'| and |bind = bind'|.
(As can be seen in \Cref{fig:annotations} and above, we needed to slightly revise
the |HasBind| type class in order to pass the name |x| of the let-bound variable
to |bind| and |bindS|, similar as for |fun|.)

Let us now look at how |AnnT| extends the pure, single-result usage analysis
into a stateful one that maintains annotations.

\subsubsection{Trace Transformer |AnnT| for Stateful Analysis}

Every instance |StaticDomain d| induces an instance |Domain (AnnD s d)|,
where the type |AnnD s d| is another example of a \emph{trace transformer}:
It transforms the |Trace| instance on type |d| into a |Trace| instance for |AnnD
s d|. The abstract domain |AnnD| is defined in terms of the abstract trace
type |AnnT|, which is a standard |ST| monad utilising efficient and pure mutable
state threads~\citep{Launchbury:94}, stacked below a |Refs| environment that
carries the mutable ref cells.
A stateful analysis computation |forall s. AnnD s UD| is then run with |runAnn|,
initialising |Refs| with ref cells pointing to empty environments.
(The universal quantification over |s| in the type of |runAnn| ensures that no
mutable |STRef| from |Refs| escapes the functional state thread of the
underlying |ST| computation~\citep{Launchbury:94}.)

The induced instance |Domain (AnnD s d)| is implemented
by lifting operations |stuck|, |apply| and |con| into monadic |AnnT s d| context
and by calling |funS| and |selectS|.
Finally, the stateful nature of the domain |AnnD s d| is exploited in the
|HasBind (AnnD s d)| instance, in two ways:

\begin{itemize}
  \item
    The call to |annotate| writes out the annotation on the let-bound variable
    |x| that is extracted from the denotation returned by the call to |bindS|.
    The omitted definition of |annotate| is just a thin wrapper around
    |extractAnn| to store the extracted annotation in the |Name :-> Ann d|
    ref cell of |Refs|, the contents of which are returned from |runAnn|.
  \item
    The calls to |readCache| and |writeCache| read from and write to the
    |Name :-> d| ref cell of |Refs| in order to provide the initial value |init|
    for fixpoint iteration.
    To this end, |kleeneFix| is generalised to |kleeneFixAboveM init f| which
    iterates the monadic function |f| starting from |init| until a reductive
    point of |f| is found (\ie a |d| such that |f d ⊑ return d|).
    When fixpoint iteration is first started, there is no cached value, in which
    case |readCache| returns |bottom| to be used as the initial value, just as
    for the single-result analysis.
    However, after every iteration of |rhs|, the call to |writeCache| persists
    the current iterate, which will be the initial value of the fixpoint
    iteration for any future calls to |bind| for the same let binding |x|.
\end{itemize}
The caching technique is important because naïve fixpoint iteration in
single-result analysis can be exponentially slow for nested let bindings, such
as in
\[
  \Lam{z}{\Let{x_1}{(\Let{x_2}{...(\Let{x_n}{z}{x_n})...}{x_2})}{x_1}}.
\]
Naïvely, every let binding needs two iterations per one iteration of its
enclosing binding: the first iteration assuming |bottom| as the initial value
for $x_i$ and the next assuming the fixpoint |MkUT (singenv z U1) (Rep Uω)|.
Ultimately, $z$ is used in the denotation of $x_n$, ..., $x_1$, totalling to
$2^n$ iterations for $x_n$ during stateless analysis.

Stateful caching of the previous fixpoint improves this drastically.
The right-hand side of $x_n = z$ is only iterated $n+1$ times in total:
once with |bottom| as the initial value for $x_n$, once more to confirm the
fixpoint |MkUT (singenv z U1) (Rep Uω)| and then $n-1$ more times to confirm
the fixpoints of $x_{n-1}, ..., x_1$.

It is possible to improve the number of iterations for $x_n$ to a constant, by
employing classic chaotic iteration and worklist techniques.
These techniques require a decoupling of iteration order from the lexical
nesting imposed by the syntax tree, instead choosing the next iteratee by
examining the graph of data flow dependencies.
Crucially, such sophisticated and stateful data-flow frameworks can be developed
and improved without complicating the analysis domain, which is often very
complicated in its own right.

\subsection{Case Study: GHC's Demand Analyser}
\label{sec:demand-analysis}

To test how well our denotational interpreter framework scales to real-world
applications, we applied the design pattern to GHC's existing Demand Analyser
and will reproduce the salient points here.
GHC's Demand Analyser infers nested usage~\citep{Sergey:14},
strictness~\citep{SPJ:06} and boxity information.
These analysis results thus fuel a number of optimisations, such
as dead code elimination and unboxing through the worker/wrapper
transformation~\citep{Gill:09}, update avoidance~\citep{Gustavsson:98},
η-expansion and η-reduction, and inlining under lambdas, to name a few.

Concretely, the refactoring entailed
\begin{itemize}
  \item
    identifying which parts of the analyser need to be part of the |Domain| interface,
  \item
    writing an abstract denotational interpreter for GHC Core, the typed
    intermediate representation of GHC, thereby identifying
  \item
    validating the usefulness of this interpreter by instantiating it at the GHC
    Core-specific analogue of the concrete by-need domain |D (ByNeed T)|, and finally
  \item
    defining the abstract |Domain| instance for Demand Analysis, to replace
    its compositional analysis function on expressions by a call to the
    denotational interpreter.
\end{itemize}
The resulting compiler bootstraps and passes the testsuite.

\subsubsection{GHC Core}

\begin{figure}
\begin{spec}
data Expr
  =  Var       Id
  |  Lit       Literal
  |  App       Expr Expr
  |  Lam       Var Expr
  |  Let       Bind Expr
  |  Case      Expr Id Type Alt
  |  Cast      Expr Coercion
  |  Tick      Tickish Expr
  |  Type      Type
  |  Coercion  Coercion
data Var = Id ^^ ... | TyVar ^^ ... | CoVar ...
type Id = Var -- always a term-level Id
data Literal = LitNumber ^^ ... | LitFloat ^^ ... | LitString ...
type Alt = (AltCon, [Var], Expr)
data AltCon = LitAlt Literal | DataAlt DataCon | DEFAULT
data Bind = NonRec Id Expr | Rec [(Id, Expr)]
data Type      = ...
data Coercion  = ...
\end{spec}
\caption{GHC Core}
\label{fig:core}
\end{figure}

GHC Core implements a variant of the polymorphic lambda calculus System $F_ω$
called System $F_C$~\citep{Sulzmann:07}.
Its definition in GHC is given in \Cref{fig:core} and includes explicit
type applications as well as witnesses of type equality constraints called
\emph{coercions}.

GHC Core's |Expr| has a lot in common with the untyped object language |Exp|
introduced in \Cref{sec:lang}.
For example, there are constructors for |Var|, |App|, |Lam|, |Let| and |Case|.
There are a number of differences, however:
\begin{itemize}
  \item
    GHC Core allows non-variable arguments in applications.
    This has implications on the denotational interpreter, which must let-bind
    non-variable arguments to establish A-normal form on-the-fly.
%  \item
%    GHC Core is typed, so the |Id| carried by |Var| contains more information
%    than a simple |String|, such as the variable's type.
%    It is worth noting that |Id| is just a synonym for |Var|.
%    However whereas |Var| includes term, type and coercion variables, the type |Id|
%    is meant to denote runtime-relevant variables only, which excludes type
%    variables.
  \item
    There is no distinguished |ConApp| form. That is because data constructors
    are just special kinds of |Id|s and may be unsaturated; the interpreter
    must eta-expand such data constructor applications on-the-fly.
  \item
    |Case| alternatives allow matching on literals (|LitAlt|) as well as data
    constructors (|DataAlt|), and include a default alternative (|DEFAULT|) that
    matches any case not matched by other alternatives.
%    Default alternatives are important for implementing the primitive
%    |seq :: a -> b -> b|, where |seq x y| diverges when |x| does and otherwise
%    evaluates to |y|.
    Furthermore, after |Case| evaluates the scrutinee, its value is bound to
    a designated |Id| called the \emph{case binder} that scopes over all case
    alternatives.
  \item
    Beyond data constructors, there are other distinguished |Id|s without a
    local binding, such as ``global'' identifiers imported from a different
    module, class method seelctors and primitive operations defined by the
    runtime system.
  \item
    |Let| bindings are either explicitly non-recursive (|NonRec|) or a mutually
    recursive group with potentially many bindings (|Rec|).
  \item
    Not shown in \Cref{fig:core} is GHC's support for \emph{inline unfoldings}
    attached to let-bound |Id|s as well as \emph{rewrite rules} declared by
    \texttt{RULES} pragmas.
    Each give rise to additional right-hand sides which must be handled with
    conservative care.
    Mistreatment of these subtle constructs in the Demand Analyser has caused
    numerous bugs over the years.
\end{itemize}
Beyond these differences, GHC Core includes forms for embedding |Literal|s,
|Type|s and |Coercion|s in select expression forms.
Type abstraction and application use regular |Lam| and |App| constructors,
whereas rewriting an expression's type along a |Coercion| happens through |Cast|s.
The constructor |Tick| annotates debugging and profiling information and can be
ignored.

\subsubsection{A Semantic |Domain| for GHC Core}

\begin{figure}
\begin{spec}
data Event  =  Look Id | LookArg CoreExpr | Update
            |  App1 | App2 | Case1 | Case2 | Let1
class Trace d where step :: Event -> d -> d

class Domain d where
  stuck :: d
  lit :: Literal -> d
  global :: Id -> d
  classOp :: Id -> Class -> d
  primOp :: Id -> PrimOp -> d
  fun :: Id -> (d -> d) -> d
  con :: DataCon -> [d] -> d
  apply :: d -> (Bool, d) -> d
  select :: d -> CoreExpr -> Id -> [DAlt d] -> d
  erased :: d
  keepAlive :: [d] -> d -> d
type DAlt d = (AltCon, [Id], d -> [d] -> d)

data BindHint = BindArg Id | BindLet Bind
class HasBind d where
  bind :: BindHint -> [[d] -> d] -> ([d] -> d) -> d
\end{spec}
\caption{A |Domain| interface for GHC Core}
\label{fig:core-domain}
\end{figure}

\Cref{fig:core-domain} defines the semantic domain abstraction for which
we implemented both a concrete |ByNeed| instance as well as an abstract
instance for Demand Analysis.
Its design was inspired by the domain definition in \Cref{fig:eval}, but
ultimately driven by the hands-on desire to accommodate both |ByNeed| and Demand
Analysis as instances.

The |stuck|, |con|, |fun|, |apply| and |select| methods serve the exact same
purpose as in prior sections, generalised to deal with the Core expressions
they are modelled after.
Method |apply| receives an additional |Bool| to tell whether it is a
runtime-irrelevant type application.
Unsurprisingly, there is a method |lit| for embedding |Literal|s, similar to
|con|.
Demand Analysis assigns special meaning to primitive operations (|primOp|),
class method selectors (|classOp|) and imported |Id|s (|global|), so each
get their own |Domain| method.

Types and coercions are erased at runtime, represented by method |erased|.
Coercion expressions, inline unfoldings and rewrite |RULES| keep alive
their free variables (|keepAlive|).
%We will see that the |D (ByNeed T)| instance actually ignores |ds| completely,
%meaning that it is not possible to derive any meaningful correctness statement
%about |keepAlive|.

The |HasBind| type class accommodates both non-recursive as well as mutually
recursive let bindings.
The |BindHint| is used to communicate whether such a binding comes from
the on-the-fly ANF-isation pass of the interpreter (|BindArg|) or whether it was
a manifest let binding in the Core program (|BindLet|).

%For simplicity, we did not introduce new |Event| constructors for type
%application redexes because Demand Analysis ignores those anyway.

\subsubsection{The Glasgow Haskell Denotational Interpreter (GHDi)}

\begin{figure}
\begin{spec}
type D d = (Trace d, Domain d, HasBind d)
anfise      ::  D d => [Expr] -> (Name :-> d) -> ([d] -> d) -> d
evalConApp  ::  D d => DataCon -> [d] -> d

eval        ::  D d => Expr -> (Name :-> d) -> d
eval (Type _) ρ                 = erased
eval (Lit l) ρ                  = lit l
eval (Var x) ρ   | not special  = ρ ! x
                 | otherwise    = ...
eval (Lam x e) ρ                = fun x (\d -> step App2 (eval e (ext ρ x d)))
eval (e@App{}) ρ
   |  Var v <- f, Just dc <- isDataConWorkId_maybe v
   =  anfise as ρ (evalConApp dc)
   |  otherwise
   =  anfise (f:as) ρ $ \(df:das) ->
        go df (zipWith (\d a -> (d, isTypeArg a)) das as)
  where
    (f, as) = collectArgs e
    go df [] = df
    go df ((d,is_ty):ds) = go (step App1 $ apply df (is_ty,d)) ds
eval (Let b@(NonRec x rhs) body) ρ =
  bind (BindLet b)
       [\ds -> keepAliveUnfRules x ρ (eval rhs ρ)]
       (\ds -> step Let1 (eval body (ext ρ x (step (Lookup x) (only ds)))))
...
\end{spec}
\caption{A glimpse of the Glasgow Haskell Denotational Interpreter (GHDi)}
\label{fig:core-eval}
\end{figure}

\Cref{fig:core-eval} shows a slightly adjusted and abridged version of the
denotational interpreter.
The actual definition takes around 100 lines of Haskell.
Its highlights include erasure of types, a new case for literals, on-the-fly
ANF-isation in the application case and picking out data constructor application
from regular function application in order to η-expand accordingly in
|evalConApp|.
Whenever an ANF-ised argument is looked up, a |LookArg| event is emitted;
this is simply for a lack of a globally unique |Id|.
In the |Let| case, the call |keepAliveUnfRules| makes sure to keep alive
the free variables of inline unfoldings and rewrite rules attached to |x|.

The |Domain| and |HasBind| instance for the concrete semantics |D (ByNeed T)|
is routine.
The resulting denotational interpreter can execute GHC Core expressions.
To demonstrate this, we wrote a small REPL around it:
\begin{Verbatim}
$ ./ghdi $(ghc --print-libdir)
prompt> let f x = x*42 :: Int; {-# NOINLINE f #-} in even $ f 3
Above expression as (optimised) Core:
  join {
    f_sZe [InlPrag=NOINLINE, Dmd=1C(1,L)] :: Int -> Bool
    [LclId[JoinId(1)(Just [!])], Arity=1, Str=<1L>]
    f_sZe (x_aYj [OS=OneShot] :: Int)
      = case x_aYj of { I# x1_aHU ->
        case remInt# (*# x1_aHU 42#) 2# of {
          __DEFAULT -> False;
          0# -> True
        }
        } } in
  jump f_sZe (I# 3#)
Trace of denotational interpreter:
Let1->App1->Lookup(f_sZe)->Update->App2->Case1->
  LookupArg(I# 3#)->Update->Case2->Case1->App1->
  App1->App2->App2->LookupArg(*# x1_aHU 42#)->App1->App1->
  App2->App2->Update->Case2-><(True, [0↦_, 1↦_, 2↦_])>
\end{Verbatim}

\subsubsection{Demand Analysis as Denotational Interpreter}

\begin{figure}
\begin{spec}
type DmdT s v = AnalEnv -> SubDemand -> AnalM s (v, Uses)
type DmdVal = [Demand]
type DmdD s = DmdT s DmdVal

instance Trace (DmdD s) where
  step (Look x) d = \env sd -> do
    (v, φ) <- d env sd
    if isBoundAtTopLvl env x then ... else pure (v, φ + singenv x (C_11 :*: sd))
  step _ d = d
instance Domain (DmdD s) where ...
instance HasBind (DmdD s) where ...
\end{spec}
\caption{A rough outline of the semantic domain of Demand Analysis}
\label{fig:dmd-domain}
\end{figure}

\Cref{fig:dmd-domain} gives a rough sketch of the semantic domain definition for
Demand Analysis.
The abstract trace type |DmdT| produces some value |v| as well as a |Uses|,
just as for |UT| in \Cref{sec:usage-analysis}.
However, it does so in a rather deep nest of types:
\begin{itemize}
  \item
    |AnalM s| plays the role of |AnnT s| in \Cref{sec:annotations}, maintaining
    annotations and speeding up fixpoint iteration.
  \item
    The analysis result is \emph{indexed} by a |SubDemand|; a description of how
    deep the expression is to be evaluated.
    A |SubDemand| is best understood as an abstraction of evaluation contexts.
    The more precise this abstraction, the more accurate are the |Uses| returned
    for that expression.
  \item
    Furthermore, an |AnalEnv| carries global state such as optimisation flags,
    means for reducing types and further syntactic information about bindings,
    such as whether a variable is bound at the top-level.
\end{itemize}
An abstract domain defined as a function sounds antithetical to our mantra in
\Cref{sec:abstraction} that abstract domains are finitely represented.
However, Demand Analysis only ever maintains one particular point of the indexed
domain, that is, every expression is analysed under one particular |SubDemand|.
This |SubDemand| may increase during fixpoint iteration, though, causing another
round of analysis.
We apply the typical widening measures in |HasBind|, so in practice Demand
Analysis has not run into infinite loops for a couple of years.

Type |DmdVal| is the similar to |UValue|, except that it lists full |Demand|s
instead of flat usage cardinalities |U|.
Such a demand |n :*: sd| describes how often (|sd|) and how deep (|sd|) a
variable is used; it is an abstraction of its contexts of use.

The |Trace| instance is very similar to the one for |UD|, it is just a little
bit more complicated because of special code for top-level bindings and
the fact that bindings get annotated with demands instead of simple usage cardinalities.
The demand |C_11 :*: sd| describes a single, strict use of the variable in the
evaluation context described by sub-demand |sd|.

The resulting analysis is sufficient to bootstrap the compiler and passes the
testsuite.
However, the compiler performance takes a serious hit due to the implementation of
|bind :: BindHint -> [ [d] -> d ] -> ([d] -> d) -> d|.
The way fixpoint iteration updates one binding |d| in mutually recursive groups
|[d]| at a time is very inefficient for the linked list representation, also
because every |[d]| ultimately turn into as many updates of the |Name :-> d|
mapping.
It would be far preferable to operate on the |Name :-> d| environment directly.
Finding a good abstraction that achieves this without exposing the whole
environment is left for future work.
\end{toappendix}

\medskip
\noindent
It is nice that usage and type analysis fit into the same
framework as the call-by-need semantics.
Another important benefit is that otherwise monolithic correctness proofs can be
broken down into smaller, systematic and reusable steps, as we will see next.
