%options ghci -package containers -package transformers -i./abs-den/paper/hs:./abs-den/paper -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include lhs-preamble.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE LambdaCase #-}

module StaticAnalysis where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.List as List
import Exp
import Order
import Interpreter
\end{code}
%endif

\section{Static Analysis}
\label{sec:abstraction}

So far, the semantic domains I have proposed have all been \emph{infinite},
simply because the dynamic traces they express are potentially infinite as well.
However, by instantiating the generic denotational interpreter on
\cpageref{fig:eval} with a semantic domain in which every element is
\emph{finite data}, we can run the interpreter on the program statically, at
compile time, to yield a \emph{finite} abstraction of the dynamic behavior.
This gives us a \emph{static program analysis}.

We can get a wide range of static analyses, simply by choosing an appropriate semantic domain.
For example, I have successfully realised the following analyses as denotational interpreters:
\begin{itemize}
  \item
    \Cref{sec:usage-analysis} defines and explores in detail a
    summary-based \emph{usage analysis}, a generalisation of absence analysis
    from \Cref{sec:problem}.
    This analysis demonstrates that our framework is suitable to infer
    \emph{operational properties}, such as an upper bound on the number of
    variable lookups.

  \item
    \Cref{sec:type-analysis} defines a variant of \citeauthor{Milner:78}'s
    Algorithm J --- a \emph{type analysis} with let generalisation, inferring
    types such as $\forall α_3.\ \mathtt{option}\;(α_3 \rightarrow α_3)$.
    Polymorphic types act as summaries in the sense of the Introduction, and
    fixpoints are solved via unification.

  \item
    \Cref{sec:0cfa} defines 0CFA \emph{control-flow analysis}~\citep{Shivers:91}
    as an instance of our generic interpreter.
    The summaries are sets of labelled expressions that evaluation might return.
    These labels are given meaning in an abstract store.
    For a function label, the abstract store maintains a single point
    approximation of the function's abstract transformer.
%    As usual for vanilla 0CFA, the resulting stateful domain is \emph{not}
%    finite and thus non-modular.
%    \sg{I think this raises more questions than it answers.}

  \item
    I have refactored relevant parts of \emph{Demand Analysis} in the Glasgow
    Haskell Compiler into an abstract denotational interpreter as an artefact.
    The resulting compiler bootstraps and passes the testsuite.%
    \footnote{There is a small caveat: we did not try to optimise for compiler
    performance in our proof of concept and hence it regresses in a few
    compiler performance test cases.
    None of the runtime performance test cases regress and the inferred
    demand signatures stay unchanged.}
    Demand Analysis is the real-world implementation of the cardinality analysis
    work of \citet{Sergey:14}, generalising usage analysis from
    \Cref{sec:usage-analysis} and implementing strictness analysis as well.
    This is to demonstrate that my framework scales to real-world compilers.
%    In fact, the entire reason why I came up with this work is that I
%    needed a framework that would allow me to describe Demand Analysis!

\end{itemize}

\subsection{Usage Analysis}
\label{sec:usage-analysis}

In this section, I describe \emph{usage analysis} (\Cref{fig:usage-analysis}), a
static analysis that estimates an upper bound on the number of $\LookupT(\px)$
transitions, an \emph{operational property} that is not observable in
traditional denotational or big-step semantics.
It is one of the most important traits of my framework that it can be used to
infer such operational properties!

\subsubsection{Trace Abstraction in |Trace UT|}
\label{sec:usage-trace-abstraction}

\begin{figure}
\centering
\begin{minipage}{0.36\textwidth}
\setlength{\mathindent}{0em}
\hfuzz=1em
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
\hfuzz=2em
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
\caption{Usage |U| and usage trace |UT|}
\label{fig:usage-trace}
\begin{code}
evalUsg e ρ = eval e ρ :: UD

data UValue = UCons U UValue | Rep U
type UD = UT UValue

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

peel :: UValue -> (U, UValue)
peel (Rep u)      = (u, Rep u)
peel (UCons u v)  = (u, v)

(!?) :: Uses -> Name -> U
m !? x  | x ∈ dom m  = m ! x
        | otherwise  = U0

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

instance HasBind UD where
  bind # rhs body = body (kleeneFix rhs)
\end{code}
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
  show (UCons u v) = show u ++ " \\sumcons " ++ show v
\end{code}
%endif
\\[-1em]
\caption{Summary-based usage analysis}
\label{fig:usage-analysis}
\end{figure}

In order to recover usage analysis as an instance of my generic interpreter, we
must define its finitely represented semantic domain |UD|.
Often, the first step in doing so is to replace the potentially infinite traces
|T| in dynamic semantic domains such as |DName| with finite data such
as |UT| in \Cref{fig:usage-trace}.
A \emph{usage trace} |MkUT φ val :: UT v| is a pair of a value |val :: v|
and a finite map |φ :: Uses|, mapping variables to a \emph{usage} |U|.
The usage |φ !? x| assigned to |x| is meant to approximate the number of |Look x|
events; |U0| means ``at most 0 times'', |U1| means ``at most 1 times'',
and |Uω| means ``an unknown number of times''.
In this way, |UT| is an \emph{abstraction} of |T|: it squashes all |Look x|
events into a single entry |φ !? x :: U| and discards all other events.

Consider as an example the by-name trace evaluating the expression \\
\mbox{$\pe \triangleq \Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$}:
\[\thickmuskip=0mu\small\perform{evalName (read "let i = λx.x in let j = λy.y in i j j") emp}\]
\noindent
We would like to abstract this trace into |MkUT [i ↦ U1, j ↦ Uω] dots|.
One plausible way to achieve this is to replace every |Step (Look x) dots|
in the by-name trace with a call to |step (Look x) dots| from the |Trace UT|
instance in \Cref{fig:usage-trace}, quite similar to |foldr step| on lists.
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
%\slpj{I'm not sure that re-using |(+)| is a good plan.  I keep running off to look for |Num| instances.}

Following through on the |foldr step| idea to abstract a |T| into |UT|
amounts to what \citet{adi} call a \emph{collecting semantics} of the interpreter.
Such semantics-specific collecting variants are easily achievable for us as
well.
It is as simple as defining a |Monad| instance on |UT| mirroring trace
concatenation and then running our interpreter at, \eg $|D (ByName UT)| \cong
|UT (Value UT)|$ on expression $\pe$ from earlier:
\hfuzz=2em
\[
  |eval (({-"\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}"-})) emp| = \perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)}| :: D (ByName UT)|.
\]
\noindent
It is nice to explore whether the |Trace| instance encodes the desired
operational property in this way, but of little practical relevance because
this interpreter instance will diverge whenever the input expression diverges.
We fix this in the next subsection by introducing a finitely represented
|UValue| to replace |Value UT|.

\subsubsection{Value Abstraction |UValue| and Summarisation in |Domain UD|}
\label{sec:usage-analysis}

In this subsection, we complement the trace type |UT| from the previous
subsection with a corresponding semantic value type |UValue| to get the
finitely represented semantic domain |UD = UT UValue| in \Cref{fig:usage-analysis}, and thus a
\emph{static usage analysis} |evalUsg| when we instantiate |eval| at |UD|.

%If we want to assess usage cardinality statically, we have to find a more
%abstract, finite representation of |Value|.%
%\footnote{In particular, the negative recursive occurrence in
%|Fun :: (τ (highlight Value τ) -> ...) -> Value τ| is disqualifying.}

The definition of |UValue| is just a copy of $\varsigma ∈ \Summary$ in
\Cref{fig:absence} that lists argument usage |U| instead of $\Absence$ flags;
the entire intuition transfers.
For example, the |UValue| summarising $\Lam{y}{\Lam{z}{y}}$ is
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
\[
|evalUsg (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalUsg (read "let k = λy.λz.y in k x_1 x_2") (Map.fromList [("x_1", MkUT (singenv "x_1" U1) (Rep Uω)), ("x_2", MkUT (singenv "x_2" U1) (Rep Uω))])}, \]
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
\[
|evalUsg (({-" \Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~i~j}} "-})) emp|
 = \perform{evalUsg (read "let i = λx.x in let j = λy.y in i i j") emp} \]
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
=  case step App2 (eval (Var x) (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) of
     MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) (Rep Uω))
=  case MkUT (singenv x U1) (Rep Uω) of
     MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) (Rep Uω))
=  MkUT emp (UCons U1 (Rep Uω))
\end{spec}
The definition of |fun x| applies the lambda body to a \emph{proxy} |(MkUT (singenv x U1) (Rep Uω))|
to summarise how the body uses its argument by way of looking at how it uses |x|.%
\footnote{As before, the exact identity of |x| is exchangeable; we use it as a
De Bruijn level.}
Every use of |x|'s proxy will contribute a usage of |U1| on |x|, and multiple
uses in the lambda body would accumulate to a usage of |Uω|.
In this case there is only a single use of |x| and the final usage |φ !? x =
U1| from the lambda body will be prepended to the summarised value.
Occurrences of |x| unleash the uninformative top value (|Rep Uω|) from |x|'s
proxy for lack of knowing the actual argument at call sites.

The definition of |apply| to apply such summaries to an argument is nearly the
same as in \Cref{fig:absence}, except for the use of |+| instead of $⊔$ to
carry over |U1 + U1 = Uω|, and an explicit |peel| to view a |UValue| in terms
of $\sumcons$ (it is |Rep u == UCons u (Rep u)|).
The usage |u| thus pelt from the value determines how often the actual
argument was evaluated, and multiplying the uses of the argument |φ2| with |u|
accounts for that.

The example
\[|evalUsg (({-" \Let{z}{Z()}{\Case{S(z)}{S(n) → n}} "-})) emp|
 = \perform{evalUsg (read "let z = Z() in case S(z) of { S(n) -> n }") emp}\]
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

The third and last ingredient to recover a static analysis is the fixpoint
strategy in |HasBind UD|, to be used for recursive let bindings.

For the dynamic semantics in \Cref{sec:interp} we made liberal use of
\emph{guarded fixpoints}, that is, recursively defined values such as |let d =
rhs d in body d| in |HasBind DName| (\Cref{fig:trace-instances}).
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
The resulting definition of |HasBind| is safe for by-name and by-need semantics.
%\footnote{Never mind totality; why is the use of \emph{least} fixpoints even correct?
%The fact that we are approximating a safety property~\citep{Lamport:77} is
%important.
%We discuss this topic in \Cref{sec:safety-extension}.}

\subsection{Strictness Analysis}
\label{sec:str-analysis}

\begin{figure}
\centering
\begin{minipage}{0.36\textwidth}
\setlength{\mathindent}{0em}
\hfuzz=1em
\begin{code}
data S = S1 | S0
type Strs = Name :-> S
class SVec a where
  (+!)  :: a -> a -> a
  (*!)  :: S -> a -> a
instance SVec S where {-" ... \iffalse "-}
  S0 +! S0 = S0
  _  +! _  = S1
  S0 *! _ = S0
  S1 *! s = s {-" \fi "-}
instance SVec Strs where {-" ... \iffalse "-}
  (+!) = Map.unionWith (+!)
  u *! m = Map.map (u *!) m
{-" \fi "-}
\end{code}
\end{minipage}%
\begin{minipage}{0.6\textwidth}
\hfuzz=2em
\begin{code}
data ST v = MkST Strs v
instance Trace (ST v) where
  step (Look x)  (MkST φ v)  = MkST (singenv x S1 +! φ) v
  step _         τ           = τ
instance Monad ST where
  return a = MkST emp a
  MkST φ1 a >>= k = let MkST φ2 b = k a in MkST (φ1+!φ2) b
\end{code}
%if style == newcode
\begin{code}
instance Extract ST where getValue (MkST _ v) = v
\end{code}
%endif
\end{minipage}
\caption{Strictness |S| and strictness trace |ST|}
\label{fig:str-trace}
\begin{code}
evalStr e ρ = eval e ρ :: SD

data SValue = Div | SCons S SValue | Unk
type SD = ST SValue

instance Domain SD where
  stuck                                  = bottom
  fun x {-" \iffalse "-}_{-" \fi "-} f   = case f (MkST (singenv x S1) Unk) of
    MkST φ v -> MkST (ext φ x S0) (SCons (φ !?? x) v)
  apply (MkST φ1 v1) (MkST φ2 _)         = case peelS v1 of
    (s, v2) -> MkST (φ1 +! s*!φ2) v2
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = foldl apply (MkST emp Unk) ds
  select d fs                            =
    d >> lub  [  f (replicate (conArity k) (MkST emp Unk))
              |  (k,f) <- assocs fs ]

peelS :: SValue -> (S, SValue)
peelS Div          = (S1, Div)
peelS (SCons s v)  = (s, v)
peelS Unk          = (S0, Unk)

(!??) :: Strs -> Name -> S
m !?? x  | x ∈ dom m  = m ! x
         | otherwise  = S0

instance Lat S where {-" ... \iffalse "-}
  bottom = S1
  S1  ⊔  S1  = S1
  _   ⊔  _   = S0
{-" \fi "-}
ifPoly (instance Lat Strs where ...)
instance Lat SValue where {-" ... \iffalse "-}
  bottom = Div
  Div ⊔ v = v
  v ⊔ Div = v
  Unk ⊔ _ = Unk
  _ ⊔ Unk = Unk
  SCons s1 v1 ⊔ SCons s2 v2 = SCons (s1 ⊔ s2) (v1 ⊔ v2)
{-" \fi "-}
instance Lat SD where {-" ... \iffalse "-}
  bottom = MkST bottom bottom
  MkST _ Div ⊔ MkST φ2 v2 = MkST φ2 v2
  MkST φ1 v1 ⊔ MkST _ Div = MkST φ1 v1
  MkST φ1 v1 ⊔ MkST φ2 v2 = MkST (φ1 ⊔ φ2) (v1 ⊔ v2)
{-" \fi "-}

instance HasBind SD where
  bind # rhs body = body (kleeneFix rhs)
\end{code}
%if style == newcode
\begin{code}
deriving instance Eq S
deriving instance Functor ST

instance Eq SD where
  MkST _ Div == MkST _ Div = True
  MkST _ Div == _ = False
  _ == MkST _ Div = False
  MkST φ1 v1 == MkST φ2 v2 = φ1 == φ2 && v1 == v2

instance Eq SValue where
  Div    == Div    = True
  Unk    == Unk    = True
  v1     == v2     = peelS v1 == peelS v2

instance Show S where
  show S0 = "\\concolor{\\mathsf{S_0}}"
  show S1 = "\\concolor{\\mathsf{S_1}}"

infixl 6 +!
infixl 7 *!

instance Show SD where
  show (MkST φ v) = "\\langle " ++ mapping ++ show v ++ " \\rangle"
    where
      mapping | Div <- v  = ""
              | otherwise = show (Map.filter (/= S0) φ) ++ ", "

instance Applicative ST where
  pure a = MkST emp a
  (<*>) = ap

instance Show SValue where
  show Div = "\\conid{Div}"
  show Unk = "\\conid{Unk}"
  show (SCons s v) = show s ++ " \\sumcons " ++ show v
\end{code}
%endif
\\[-1em]
\caption{Strictness analysis}
\label{fig:str-analysis}
\end{figure}

Whereas usage analysis infers \emph{upper} bounds on evaluation cardinality,
\emph{strictness analysis}~\citep{Mycroft:80}, defined in
\Cref{fig:str-analysis}, infers \emph{lower} bounds on evaluation cardinality.
A variable is used \emph{strictly} when it is looked up at least once; otherwise
it is used \emph{lazily}.
Implementations of lazy languages such as GHC call strict functions by-value
instead of by-need, enabling further optimisations such as passing arguments
unboxed.
For the example expression from \Cref{sec:problem}, strictness analysis reports
the following
\[
|evalStr (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalStr (read "let k = λy.λz.y in k x_1 x_2") (Map.fromList [("x_1", MkUT (singenv "x_1" S1) Unk), ("x_2", MkUT (singenv "x_2" S1) Unk)])}, \]
indicating that $k$
analysing the example expression from \Cref{sec:problem}.
For example,

%Strictness analysis operates very similarly to usage analysis; so similar in
%fact that both analyses could be interleaved into a unified \emph{cardinality
%analysis}, expressing both lower and upper bounds on cardinality as an interval.

Strictness analysis operates very similarly to usage analysis.
The most important change is the |Lat S| instance, which is defined by the total
order |S1 ⊏ S0|.
The overloaded addition operator is defined as meet (|(+) = (⊓)|) and scalar
multiplication is defined as join (|(*) = (⊔)|.
These operations lift pointwise to finite maps |φ :: Strs|, which map free
variables to their strictness |S|.
For example, |S0 * singenv x S1 + S1 * singenv y S1 = singenv x S0 + singenv y S1 = singenv y S1|.

Another important difference is with the semantics of the |Div| value, which
denotes a diverging computation.
Such computations are

In \Cref{fig:str-analysis}, I omit code that is sufficiently similar to usage
analysis in \Cref{fig:usage-analysis}.
Where previously we wrote |U0|, we now write |S0|; |U1| maps to |S1| and
any occurrences of |Rep Uω| such as in |fun| map to |Unk|.

\[|evalStr (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalStr (read "let k = λy.λz.y in k x_1 x_2") (Map.fromList [("x_1", MkST (singenv "x_1" S1) Unk), ("x_2", MkST (singenv "x_2" S1) Unk)])} \]

\[|evalStr (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalStr (read "let k = λy.λz.y in let j = j in case Z() of {Z() -> k; S(n) -> j}") (Map.fromList [("x_1", MkST (singenv "x_1" S1) Unk), ("x_2", MkST (singenv "x_2" S1) Unk)])} \]

\subsection{Boxity Analysis}
\label{sec:boxity-analysis}

\begin{figure}
\centering
\begin{minipage}{0.36\textwidth}
\hfuzz=1em
\begin{code}
data B = D | N
type Boxs = Name :-> B
\end{code}
\end{minipage}%
\begin{minipage}{0.6\textwidth}
\hfuzz=2em
\begin{code}
data BT v = MkBT Boxs Boxs v
instance Trace (BT v) where step _ = id
instance Monad BT where
  return a = MkBT emp emp a
  MkBT φ1 _ a >>= k = let MkBT φ2 φ2n b = k a in MkBT (φ1 ⊔ φ2) φ2n b

needBox :: BT v -> BT v
needBox (MkBT φ φn v) = MkBT (φ ⊔ φn) emp v
\end{code}
%if style == newcode
\begin{code}
instance Extract BT where getValue (MkBT _ _ v) = v
\end{code}
%endif
\end{minipage}
\caption{Boxity |B| and boxity trace |BT|}
\label{fig:boxity-trace}
\begin{code}
evalBox e ρ = eval e ρ :: BD

data BValue = BCons B BValue | BRep B
type BD = BT BValue

instance Domain BD where
  stuck                                  = bottom
  fun x {-" \iffalse "-}_{-" \fi "-} f   = case needBox (f (MkBT emp (singenv x N) (BRep N))) of
    MkBT φ _ v -> MkBT (ext φ x D) emp (BCons (φ !??? x) v)
  apply df (MkBT φ φn _)          = needBox df >>= \v1 -> case peelB v1 of
    (D, v2) -> MkBT φ        emp v2
    (N, v2) -> MkBT (φ ⊔ φn) emp v2
  con {-" \iffalse "-}_{-" \fi "-} _ ds  =
    BRep N <$ mapM_ needBox ds
  select d fs                      =
    d >> lub  [  f (replicate (conArity k) (MkBT emp emp (BRep N)))
              |  (k,f) <- assocs fs ]

peelB :: BValue -> (B, BValue)
peelB (BRep b)     = (b, BRep b)
peelB (BCons b v)  = (b, v)

(!???) :: Boxs -> Name -> B
m !??? x  | x ∈ dom m  = m ! x
          | otherwise  = D

instance Lat B where {-" ... \iffalse "-}
  bottom = D
  D  ⊔  D  = D
  _  ⊔  _  = N
{-" \fi "-}
ifPoly (instance Lat Strs where ...)
instance Lat BValue where {-" ... \iffalse "-}
  bottom = (BRep D)
  BRep b1 ⊔ BRep b2 = BRep (b1 ⊔ b2)
  BRep b1 ⊔ v = BCons b1 (BRep b1) ⊔ v
  v ⊔ BRep b2 = v ⊔ BCons b2 (BRep b2)
  BCons b1 v1 ⊔ BCons b2 v2 = BCons (b1 ⊔ b2) (v1 ⊔ v2)
{-" \fi "-}
instance Lat BD where {-" ... \iffalse "-}
  bottom = MkBT bottom bottom bottom
  MkBT φ1 φ1n v1 ⊔ MkBT φ2 φ2n v2 = MkBT (φ1 ⊔ φ2) (φ1n ⊔ φ2n) (v1 ⊔ v2)
{-" \fi "-}

instance HasBind BD where
  bind x rhs body = body (kleeneFix (use . rhs))
    where use (MkBT φ φn v) = MkBT φ (singenv x N) v
\end{code}
%if style == newcode
\begin{code}
deriving instance Eq B
deriving instance Eq a => Eq (BT a)
deriving instance Functor BT

instance Eq BValue where
  BRep b1 == BRep b2 = b1 == b2
  v1      == v2      = peelB v1 == peelB v2

instance Show B where
  show D = "\\concolor{\\mathsf{D}}"
  show N = "\\concolor{\\mathsf{N}}"

instance Show v => Show (BT v) where
  show (MkBT φ φn v) = "\\langle " ++ show (Map.filterWithKey cool φ) ++ ", " ++ show (Map.filterWithKey cool φn) ++ ", " ++ show v ++ " \\rangle"
    where
     cool _       D = False
     cool ('?':_) _ = False
     cool _       _ = True

instance Applicative BT where
  pure a = MkBT emp emp a
  (<*>) = ap

instance Show BValue where
  show (BRep b)    = "\\conid{Rep}\\;" ++ show b
  show (BCons b v) = show b ++ " \\sumcons " ++ show v
\end{code}
%endif
\\[-1em]
\caption{Boxity analysis}
\label{fig:boxity-analysis}
\end{figure}


\[|evalBox (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalBox (read "let k = λy.λz.y in k x_1 x_2") (Map.fromList [("x_1", MkBT emp (singenv "x_1" N) (BRep N)), ("x_2", MkBT emp (singenv "x_2" N) (BRep N))])} \]

\[|evalBox (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalBox (read "let k = λy.λz.y in let j = j in case Z() of {Z() -> k; S(n) -> j}") (Map.fromList [("x_1", MkBT emp (singenv "x_1" N) (BRep N)), ("x_2", MkBT emp (singenv "x_2" N) (BRep N))])} \]

\[|evalBox (({-" \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2} "-})) ρe|
 = \perform{evalBox (read "let m = let n = Z() in Some(n) in let get = λo. case o of { None() -> Z(); Some(n) -> n } in get") emp} \]

\[|evalBox (read "let plus = ...") emp|
 = \perform{evalBox (read "let plus = λa.λb. case a of { Z() -> b; S(m) -> S(plus m b) } in plus") emp} \]

\[|evalBox (read "let zeros = ...") emp|
 = \perform{evalBox (read "let zeros = Pair(Z(),zeros) in case zeros of { Pair(x,xs) -> xs }") emp} \]

\[|evalBox (read "let zero = ...") emp|
 = \perform{evalBox (read "let zero = Z() in case zero of { Z() -> Z() }") emp} \]

\subsection{Type Analysis: Algorithm J}
\label{sec:type-analysis}

\begin{figure}
\centering
\setlength{\mathindent}{0em}
\begin{code}
data TyCon = BoolTyCon | NatTyCon | OptionTyCon | PairTyCon
data Type = Type :->: Type | TyConApp TyCon [Type] | TyVar Name | Wrong
data PolyType = PT [Name] Type

type Subst = Name :-> Type
type Constraint = (Type, Type)
newtype J a = J (StateT (Set Name,Subst) Maybe a)
unify              :: Constraint -> J ()
freshTyVar         :: J Type
instantiatePolyTy  :: PolyType -> J Type
generaliseTy       :: J Type -> J PolyType
closedType         :: J Type -> PolyType {-" \iffalse "-}
closedType d = runJ (generaliseTy d)
{-" \fi "-}

evalTy e = closedType (eval e emp) :: PolyType

instance Trace (J v) where step _ = id
instance Domain (J Type) where
  stuck = return Wrong
  fun _ {-" \iffalse "-}_{-" \fi "-} f = do
    θα  <- freshTyVar
    θ   <- f (return θα)
    return (θα :->: θ)
  con {-" \iffalse "-}_{-" \fi "-} k ds = {-" ... \iffalse "-} do
    con_app_ty <- instantiateCon k
    arg_tys <- sequence ds
    res_ty <- freshTyVar
    unify (con_app_ty, foldr (:->:) res_ty arg_tys)
    return res_ty {-" \fi "-}
  apply v a = do
    θ1  <- v
    θ2  <- a
    θα  <- freshTyVar
    unify (θ1, θ2 :->: θα)
    return θα
  select dv fs = {-" ... \iffalse "-} case Map.assocs fs of
    []            -> stuck
    fs@((k,_):_)  -> do
      con_ty <- dv
      res_ty <- snd . splitFunTys <$> instantiateCon k
      let TyConApp tc tc_args = res_ty
      unify (con_ty, res_ty)
      ks_tys <- enumerateCons tc tc_args
      tys <- forM ks_tys $ \(k,tys) ->
        case List.find (\(k',_) -> k' == k) fs of
          Just (_,f) -> f tys
          _          -> stuck
      case tys of
        []      -> stuck
        ty:tys' -> traverse (\ty' -> unify (ty,ty')) tys' >> return ty
{-" \fi "-}
instance HasBind (J Type) where
  bind # rhs body = do
    σ <- generaliseTy $ do
      θα  <- freshTyVar
      θ   <- rhs (return θα)
      unify (θα, θ)
      return θα
    body (instantiatePolyTy σ)

\end{code}
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
\caption{Type analysis with let generalisation (Algorithm J)}
\label{fig:type-analysis}
\end{figure}

Computing least fixpoints is common practice in static program analysis.
However, some abstract domains employ quite different fixpoint strategies.
The abstract domain of the type analysis I define in this subsection is
an interesting example:
Type analysis --- specifically, \citeauthor{Milner:78}'s Algorithm J ---
computes fixpoints by generating and solving a constraint system via
unification.

\Cref{fig:type-analysis} outlines the abstract domain |J Type| at which the
generic denotational interpreter can be instantiated to perform Type analysis.
I omit implementational details that are derivative of Milner's description of
Algorithm J.
The full implementation can be found in the extract generated from this
document\sg{TODO: Which extract? Where?}, but the provided code is sufficiently
exemplary of the approach.

Type analysis |evalTy| infers most general polymorphic types |PolyType| of the
form $\forall \many{\alpha}.\ θ$ for an expression, where $θ$ ranges over a
monomorphic |Type| that can be either a type variable |TyVar α| (I will use
|θα| as meta variable for this form), a function type |θ1 :->: θ2|, or a
type constructor application |TyConApp|, where |TyConApp OptionTyCon [θ1]| is
printed as $\mathtt{option}~θ_1$.
The |Wrong| type indicates a type error and is printed as $\textbf{wrong}$.

Key to the analysis is its abstract trace type |J|, the name of which refers to the ambient
effects of Milner's Algorithm J, offering means to invoke unification (|unify|),
fresh name generation (|freshTyVar|, |instantiatePolyTy|) and let
generalisation (|generaliseTy|).
My type |J| implements these effects by maintaining two pieces of state:
\begin{enumerate}
  \item
    a consistent set of type constraints as a unifying substitution |Subst|.
  \item
    the set of used types as a |Set Name|.
    This is to supply fresh names in |freshTyVar|
    and to instantiate a polytype $\forall α. α \to α$ to a monotype $α_1
    \to α_1$ for fresh $α_1$ as done by |instantiatePolyTy|, but also to
    identify the type variables which are \emph{generic}~\citep{Milner:78} in
    the ambient type context and hence may be generalised by |generaliseTy|.
\end{enumerate}
Unification failure is signalled by returning |Nothing| in the base monad
|Maybe|, and function |closedType| for handling |J| effects will return |Wrong|
when that happens.

The operational detail offered by |Trace| is ignored by |J|, but the |Domain|
and |HasBind| instances for the abstract semantic domain |J Type| are quite
interesting.
Throughout the analysis, the invariant is maintained that the |J Type| denotation
of let-bound variables in the interpreter environment |ρ| is of the form
|instantiatePolyTy σ| for a polytype |σ|, while lambda- and field-bound
variables are denoted by |return θ|, yielding the same monotype |θ| at all use
sites.
Thus, let-bound denotations instantiate polytypes on-the-fly at occurrence
sites, just as in Algorithm J.

As expected, |stuck| terms are denoted by the monotype |Wrong|.
The definition of |fun| resembles the abstraction rule of Algorithm J,
in that it draws a fresh variable type |θα :: Type| (of the form |TyVar α|)
to stand for the type of the argument.
This type is passed as a monotype |return θα| to the body denotation
|f|, where it will be added to the environment (\cf \Cref{fig:eval}) in order to
compute the result type |θ| of the function body.
The type for the whole function is then |θα :->: θ|.
The definition for |apply| is a literal translation of Algorithm J as well.
The cases for |con| and |select| are omitted as their implementation follows
a similar routine.

The generalisation and instantiation machinery comes to bear in the implementation
of |bind|, which implements a combination of the $\mathit{fix}$ and $\mathit{let}$
cases in Algorithm J, computing fixpoints by unification.

The recursive knot is tied in the |do| block passed to |generaliseTy|.
It works by calling the iteratee |rhs| with a fresh
unification variable type |θα|, for example $α_1$.
The result of this call in turn is a monotype |θ|,
for example $\mathtt{option}\;(α_3 \rightarrow α_3)$ for \emph{generic}
$α_3$, meaning that $α_3$ is a fresh name introduced in the right-hand side.
Then |θα| is unified with |θ|, substituting $α_1$ with
$\mathtt{option}\;(α_3 \rightarrow α_3)$.
This concludes the implementation of Milner's $\mathit{fix}$ case.

For Milner's $\mathit{let}$ case, the type |θα| is
generalised to $\forall α_3.\ \mathtt{option}\;(α_3 \rightarrow α_3)$
by universally quantifying the generic variable $α_3$.
It is easy for |generaliseTy| to deduce that $α_3$ must be generic \wrt the
right-hand side, because $α_3$ does not occur in the set of used |Name|s prior
to the call to |rhs|.
The generalised polytype |σ| is then instantiated afresh via |instantiatePolyTy
σ| at every use site of |x| in the |body|, implementing polymorphic
instantiation.

\begin{table}
\centering
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |evalTy e| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{i~i~i~i~i~i}$                  & $\perform{evalTy (read "let i = λx.x in i i i i i i")}$ \\
(2) & $\Lam{x}{\Let{y}{x}{y~x}}$                          & $\perform{evalTy (read "λx. let y = x in y x")}$ \\
(3) & $\Let{i}{\Lam{x}{x}}{\Let{o}{\mathit{Some}(i)}{o}}$ & $\perform{evalTy (read "let i = λx.x in let o = Some(i) in o")}$ \\
(4) & $\Let{x}{x}{x}$                                     & $\perform{evalTy (read "let x = x in x")}$ \\
\bottomrule
\end{tabular}
\caption{Examples for type analysis.}
\label{fig:type-examples}
\end{table}

\paragraph{Examples.}
Let us conclude with some examples in \Cref{fig:type-examples}.
Example (1) demonstrates repeated instantiation and generalisation.
Example (2) shows that let generalisation does not accidentally generalise the
type of $y$; note that the type of $y$ is not generic in the ambient typing
context of the RHS of $\mathbf{let}~x = \wild$.
Example (3) demonstrates data types and the characteristic
approximation of higher-rank types such as $\mathtt{option}~(\forall α_6.\
α_6 \to α_6)$ in Algorithm J, and example (4) shows that type inference for
diverging programs works as expected.

\begin{comment}
\begin{figure}
\begin{code}
data Pow a = P (Set a); type CValue = Pow Label
type ConCache = (Tag, [CValue]); data FunCache = FC (Maybe (CValue, CValue)) (CD -> CD)
data Cache = Cache (Label :-> ConCache) (Label :-> FunCache)
data CT a = CT (State Cache a); type CD = CT CValue; runCFA :: CD -> CValue

updFunCache :: Label -> (CD -> CD) -> CT (); cachedCall :: Label -> CValue -> CD

instance HasBind CD where{-" ... \iffalse "-}
  bind # rhs body = go bottom >>= body . return
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- rhs (return v)
        cache' <- CT get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- rhs (return v'); if v' /= v'' then error "blah" else return v' } else go v'
{-" \fi "-}; instance Trace (CT v) where step _ = id
instance Domain CD where
  fun _ ell f = do updFunCache ell f; return (P (Set.singleton ell))
  apply dv da = dv >>= \(P ells) -> da >>= \a -> lub <$> traverse (\ell -> cachedCall ell a) (Set.toList ells)
  {-" ... \iffalse "-}
  stuck = return bottom
  con ell k ds = do vs <- sequence ds; updConCache ell k vs; return (P (Set.singleton ell))
  select dv fs = do
    P ells <- dv
    cache <- CT get
    vals <- sequence [ f (map return vs) | ell <- Set.toList ells, Just (k',vs) <- [Map.lookup ell (cCons cache)]
                     , (k,f) <- Map.assocs fs, k == k' ]
    return (lub vals)
{-" \fi "-}
\end{code}

%if style == newcode
\begin{code}
deriving instance Eq a => Eq (Pow a)
deriving instance Ord a => Ord (Pow a)

instance Show (CValue) where
  showsPrec _ (P s) =
    showString "\\{" . showSep (showString ", ") (map showString (Set.toList s)) . showString "\\}"

instance Ord a => Lat (Pow a) where
  bottom = P Set.empty
  P l ⊔ P r = P (Set.union l r)

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
      f fld = fld c1 ⊔ fld c2

deriving instance Show Cache

unCT :: CT a -> State Cache a
unCT (CT m) = m

runCFA (CT m) = evalState m (Cache bottom bottom)

deriving instance Functor CT

instance Applicative CT where
  pure = CT . pure
  (<*>) = ap

instance Monad CT where
  CT m >>= k = CT (m >>= unCT . k)

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

updConCache :: Label -> Tag -> [CValue] -> CT ()
updConCache ell k vs = CT $ modify $ overCons $ \cons ->
  Map.singleton ell (k, vs) ⊔ cons

updFunCache ell f = CT $ modify $ overFuns $ \funs ->
  Map.singleton ell (FC Nothing f) ⊔ funs

cachedCall ell v = CT $ do
  FC cache f <- gets (Map.findWithDefault bottom ell . cFuns)
  let call in_ out = do
        let in_' = in_ ⊔ v      com merge all Labels that reach the lambda var ell!
        modify $ overFuns (Map.insert ell (FC (Just (in_',out)) f))
        out' <- unCT (f (return in_'))
        modify $ overFuns (Map.insert ell (FC (Just (in_',out')) f))
        return out'
  case cache of
    Just (in_,out)
      | v ⊑ in_   -> return out
      | otherwise -> call in_ out
    Nothing       -> call bottom bottom
\end{code}
%endif
\vspace{-1.5em}
\caption{0CFA}
\label{fig:cfa}
\end{figure}

\subsection{Control-flow Analysis}
\label{sec:0cfa}

In our last example, we will discuss a classic benchmark of abstract
higher-order interpreters: Control-flow analysis (CFA).
CFA calculates an approximation of which values an expression might evaluate to,
so as to narrow down the possible control-flow edges at application sites.
The resulting control-flow graph conservatively approximates the control-flow of
the whole program and can be used to apply classic intraprocedural analyses such
as interval analysis in a higher-order setting.

To facilitate CFA, we have to revise the |Domain| class to pass down a
\emph{label} from allocation sites, which is to serve as the syntactic proxy of
the value's control-flow node:
\begin{spec}
type Label = String
class Domain d where
  con  :: {-" \highlight{ "-}Label -> {-" {}} "-} Tag -> [d] -> d
  fun  :: Name -> {-" \highlight{ "-}Label -> {-" {}} "-} (d -> d) -> d
\end{spec}
\noindent
We omit how to forward labels appropriately in |eval| and how to adjust
|Domain| instances.

\Cref{fig:cfa} gives a rough outline of how we use this extension to define a 0CFA:%
\footnote{As before, the extract of this document contains the full, executable
definition.}
An abstract |CValue| is the usual set of |Label|s standing in for a syntactic
value.
The trace abstraction |CT| maintains as state a |Cache| that approximates the
shape of values at a particular |Label|, an abstraction of the heap.
For constructor values, the shape is simply a pair of the |Tag| and |CValue|s
for the fields.
For a lambda value, the shape is its abstract control-flow transformer, of
type |CD -> CD| (populated by |updFunCache|), plus a single point |(v1,v2)| of
its graph ($k$-CFA would have one point per contour), serving as the transformer's
summary.

At call sites in |apply|, we will iterate over each function label and attempt a
|cachedCall|.
In doing so, we look up the label's transformer and sees if the single point
is applicable for the incoming value |v|, \eg if |v ⊑ v1|, and if so return the
cached result |v2| straight away.
Otherwise, the transformer stored for the label is evaluated at |v| and the
result is cached as the new summary.
An allocation site might be re-analysed multiple times with monotonically increasing
environment due to fixpoint iteration in |bind|.
Whenever that happens, the point that has been cached for that allocation
site is cleared, because the function might have increased its result.
Then re-evaluating the function at the next |cachedCall| is mandatory.

Note that a |CD| transitively (through |Cache|) recurses into |CD -> CD|, thus
introducing vicious cycles in negative position, rendering the encoding
non-inductive.
This highlights a common challenge with instances of CFA: The obligation to
prove that the analysis actually terminates on all inputs; an obligation that we
will gloss over in this work.

\begin{table}
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |runCFA (eval e emp)| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i j") emp}$ \\
(2) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$ & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i i j") emp}$ \\
(3) & $\Let{ω}{\Lam{x}{x~x}}{ω~ω}$                      & $\perform{runCFA $ eval (read "let ω = λx. x x in ω ω") emp}$ \\
(4) & $\Let{x}{\Let{y}{S(x)}{S(y)}}{x}$                 & $\perform{runCFA $ eval (read "let x = let y = S(x) in S(y) in x") emp}$ \\
\bottomrule
\end{tabular}
\caption{Examples for control-flow analysis.}
\label{fig:cfa-examples}
\end{table}

\subsubsection*{Examples}
The first two examples of \Cref{fig:cfa-examples} demonstrate a precise and an
imprecise result, respectively. The latter is due to the fact that both |i| and
|j| flow into |x|.
Examples (3) and (4) show that the |HasBind| instance guarantees termination for
diverging programs and cyclic data.
\end{comment}

\begin{comment}
\subsection{Bonus: Higher-order Cardinality Analysis}

In the style of \citet{Sergey:14}.
\sg{Flesh out, move to Appendix or remove. I left this section in for Ilya to
have a look. |call 2| means ``assume an evaluation context that applies 2
arguments'', |anyCtx| means ``evaluate in any evaluation context'' (top).}

\begin{tabular}{clll}
\toprule
\#  & |f|      & |e|                                                                    & |f e| \\
\midrule
(1) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$                      & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j j"}$ \\
(2) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$                        & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j"}$ \\
(3) & |call 2| & $\Let{i}{\Lam{x}{x}}{i}$                                               & $\perform{call 2 "let i = λx.x in i"}$ \\
(4) & |call 2| & $\Let{\mathit{const}}{\Lam{x}{\Lam{y}{y}}}{\mathit{const}}$            & $\perform{call 2 "let const = λx.λy.y in const"}$ \\
(5) & |call 2| & $\Let{f}{\Lam{a}{\Lam{g}{\Let{t}{g~a}{t~t}}}}{\mathit{f}}$ & $\scriptstyle \perform{call 2 "let f = λa. λg. let t = g a in t t in f"}$ \\
%(6) & |anyCtx| & $\Let{z}{Z()}{\Let{o}{S(z)}{\Let{\mathit{plus}}{\Lam{a}{\Lam{b}{...S(\mathit{plus}~(a-1)~b)...}}}{\mathit{plus}~z~o}}}$
%               & $\perform{anyCtx "let z = Z() in let o = S(z) in let plus = λa.λb. case a of { Z() -> b; S(n) -> let plusn = plus n b in S(plusn) } in plus z o"}$ \\
\bottomrule
\end{tabular}
\end{comment}

It is nice to define dynamic semantics and static analyses in the same
framework, but another important benefit is that correctness proofs become
simpler, as we will see next.
