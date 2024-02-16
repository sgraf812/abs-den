%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures
% Need the -XPartialTypeSignatures for the CbNeed example, for some weird reason
%include custom.fmt
%if style == newcode
\begin{code}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Interpreter where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Text.Show (showListWith)
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State
import Exp

instance {-# OVERLAPPING #-} Show (Maybe (Value τ)) where
  show Nothing = "\\bot"
  show (Just a) = "\\mathtt{Just}(" ++ show a ++ ")"
instance {-# OVERLAPPING #-} Show (Identity (Value (ByName Identity))) where
  show (Identity a) = "\\langle " ++ show a ++ "\\rangle "
instance Show Event where
  show (Lookup x) = "\\LookupT(" ++ x ++ ")"
  show App1 = "\\AppIT"
  show App2 = "\\AppET"
  show Case1 = "\\CaseIT"
  show Case2 = "\\CaseET"
  show Let0 = "\\LetOT"
  show Let1 = "\\LetIT"
  show Update = "\\UpdateT"
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret a) = "\\langle "++show a++"\\rangle "
instance {-# OVERLAPPING #-} Show a => Show (T (Maybe a)) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret Nothing)  = "..."
  show (Ret (Just a)) = "\\langle "++show a++"\\rangle "
instance Show (Value τ) where
  show (Fun _) = "\\lambda"
  show (Con k _) = "Con(" ++ show k ++ ")"
  show Stuck = "\\lightning"
instance (Show (τ v)) => Show (ByName τ v) where
  show (ByName τ) = show τ
instance Show (ByNeed τ a) where
  show _ = "\\wild"
instance (Show (τ v)) => Show (ByValue τ v) where
  show (ByValue τ) = show τ
instance (Show (τ v)) => Show (ByVInit τ v) where
  show (ByVInit _) = "\\wild"
instance (Show a, forall a. Show a => Show (τ a)) => Show (Fork (ParT τ) a) where
  show Empty = "Empty"
  show (Single a) = show a
  show (Fork l r) = "Fork(" ++ show l ++ "," ++ show r ++ ")"
instance (Show a, forall a. Show a => Show (m a)) => Show (ParT m a) where
  show (ParT m) = show m
instance {-# OVERLAPPING #-} (Show v) => Show (Addr :-> v) where
  showsPrec _ = showListWith (\(k,v) -> shows k . showString "\\!\\! \\mapsto \\!\\! " . shows v) . Map.toList
instance {-# OVERLAPPING #-} (Show v) => Show (Name :-> v) where
  showsPrec _ = showListWith (\(k,v) -> showString "\\mathit{" . showString k . showString "} \\! \\mapsto \\! " . shows v) . Map.toList

takeT :: Int -> T a -> T (Maybe a)
takeT 0 _ = return Nothing
takeT _ (Ret a) = return (Just a)
takeT n (Step e t) = Step e (takeT (n-1) t)

takeName :: Int -> ByName T a -> T (Maybe a)
takeName n (ByName τ) = takeT n τ
\end{code}
%endif

\section{A Denotational Interpreter}
\label{sec:interp}

In this section, we present the main contribution of this work, namely a
generic \emph{denotational interpreter}%
\footnote{This term was coined by \citet{Might:10}.
We find it fitting, because a denotational interpreter is both a
\emph{denotational semantics}~\citep{ScottStrachey:71} as well as a total
\emph{definitional interpreter}~\citep{Reynolds:72}.}
for a functional language which we can instantiate with different semantic
domains.
The choice of semantic domain determines the \emph{evaluation strategy}
(call-by-name, call-by-value, call-by-need) and the degree to which
\emph{operational detail} can be observed.
Yet different semantic domains give rise to useful \emph{summary-based} static
analyses such as usage analysis in \Cref{sec:abstraction}, all from the same
interpreter skeleton.
Our generic denotational interpreter simplifies the soundness proofs of derived
static analyses because it modularly decomposes into a large preservation proof
(as in \Cref{sec:problem}), to be done once per semantics, and a comparatively
small proof involving the analysis domain.
\sg{I tried to improve, but fear it is even more inscrutible than before. Alternative:}
Our generic denotational interpreter simplifies the soundness proofs of derived
static analyses because the proof only involves the operations of the analysis
domain rather than their composition in the interpreter and how they relate to
the concrete semantics.
%Proving a static analysis correct \wrt a dynamic semantics merely needs to prove
%statements about the respective semantic domains, rather than the shared
%skeleton (\cf \Cref{sec:soundness}), which is a drastic simplification compared
%to hand-rolling a preservation-style proof as outlined in \Cref{sec:problem}
\sven{This sentence is hard to understand without context. I suppose the point is: Our generic denotational simplifies the soundness proofs of derived static analyses, as the proofs require no reasoning about the genric interpreter, only about its instances.}

Denotational interpreters can be implemented in any higher-order language such as OCaml, Scheme or Java with explicit thunks, but we picked Haskell for convenience.%
\footnote{We extract from this document a runnable Haskell file which we add as a Supplement, containing the complete definitions. Furthermore, the (terminating) interpreter outputs are directly generated from this extract.}

\begin{figure}
\begin{minipage}{0.49\textwidth}
\begin{spec}
data Exp
  =  Var Name | Let Name Exp Exp
  |  Lam Name Exp | App Exp Name
  |  ConApp Tag [Name] | Case Exp Alts
type Name = String
type Alts = Tag :-> ([Name],Exp)
data Tag = ...; conArity :: Tag -> Int
\end{spec}
\caption{Syntax}
\label{fig:syntax}
\end{minipage}%
\begin{minipage}{0.51\textwidth}
\begin{code}
type (:->) = Map; emp :: Ord k => k :-> v
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
exts :: Ord k  => (k :-> v) -> [k] -> [v]
               -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
(∈) :: Ord k => k -> Set k -> Bool
(<<) :: (b -> c) -> (a :-> b) -> (a :-> c)
assocs :: (k :-> v) -> [(k,v)]
\end{code}
%if style == newcode
\begin{code}
emp = Map.empty
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl' (uncurry . ext) ρ (zip xs ds)
(<<) = Map.map
infixr 9 <<
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
assocs = Map.assocs
\end{code}
%endif
\caption{Environments}
\label{fig:map}
\end{minipage}
\end{figure}

\subsection{Semantic Domain} \label{sec:dna}

Just as traditional denotational semantics, denotational interpreters
assign meaning to programs in some \emph{semantic domain}.
Traditionally, the semantic domain |D| comprises \emph{semantic values} such as
base values (integers, strings, etc.) and functions |D -> D|.
One of the main features of these semantic domains is that they lack
\emph{operational}, or, \emph{intensional detail} that is unnecessary to
assigning each observationally distinct expression a distinct meaning.
For example, it is not possible to observe evaluation cardinality, which
is the whole point of analyses such as usage analysis.

A distinctive feature of our work is that our semantic domains are instead
\emph{traces} that describe the \emph{steps} taken by an abstract machine, and
that \emph{end} in semantic values.
It is possible to describe evaluation cardinality as a property of the traces
thus generated, as required for a correctness proof of usage analysis.
We choose |DName|, defined below, as the first example of such a semantic domain,
because it is simple and illustrative of the approach.
Instantiated at |DName|, our generic interpreter will produce precisely the
traces of the by-name variant of the Krivine machine in \Cref{fig:lk-semantics}.
%In \Cref{sec:evaluation-strategies} we will give semantic domains for by-value
%and by-need semantics as well, and in \Cref{sec:abstraction} we obtain static
%analyses as instances\sven{This is off topic. Right now the reader wants to see
%the definition of |DName| and understand it. I would move this sentence to the
%end of Sec 4.1.}.

We can define the semantic domain |DName| for a call-by-name variant of our language as follows:%
\footnote{For a realistic implementation, we would define |D| as a data type to
keep type class resolution decidable and non-overlapping. We will however stick
to a |type| synonym in this presentation in order to elide noisy wrapping and
unwrapping of constructors.}

\begin{minipage}{0.62\textwidth}
\begin{code}
type D τ = τ (Value τ);   type DName = D T
data T v = Step Event (T v) | Ret v
data Event  =  Lookup Name | Update | App1 | App2
            |  Let0 | Let1 | Case1 | Case2
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{code}
\end{minipage}
\begin{minipage}{0.38\textwidth}
\begin{spec}
instance Monad T where
  return v = Ret v
  Ret v >>= k = k v
  Step e τ >>= k = Step e (τ >>= k)
\end{spec}
%if style == newcode
\begin{code}
instance Functor T where
  fmap f (Ret a) = Ret (f a)
  fmap f (Step e t) = Step e (fmap f t)
instance Applicative T where
  pure = Ret
  (<*>) = ap
instance Monad T where
  Ret v >>= k = k v
  Step e τ >>= k = Step e (τ >>= k)
\end{code}
%endif
\end{minipage}
\noindent
A trace |T| either returns a value (|Ret|) or makes a small-step transition (|Step|).
Each step |Step ev rest| is decorated with an event |ev|, which describes what happpens in that step.
For example, event |Lookup x| describes the lookup of variable |x :: Name| in the environment.
Note that the choice of |Event| is use-case (\ie analysis) specific and suggests
a spectrum of intensionality, with |data Event = Unit| on the more abstract end
of the spectrum and arbitrary syntactic detail attached to each of |Event|'s
constructors at the intensional end of the spectrum.%
\footnote{If our language had facilities for input/output and more general
side-effects, we could have started from a more elaborate trace construction
such as (guarded) interaction trees~\citep{interaction-trees,gitrees}.}

A trace in |DName = T (Value T)| eventually terminates with a |Value| that is
either stuck (|Stuck|), a function waiting to be applied to a domain value
(|Fun|), or a constructor constructor application giving the denotations of its
fields (|Con|).
%|Value| is thus just a standard denotational encoding of its syntactic counterpart |Lam|/|ConApp|, devoid of any syntax. \slpj{I don't know what that sentence adds or even means. Omit?}
%\sg{I clarified, mentioining |Lam|/|ConApp|. This point is one of the main distinctions between operational semantics and denotational semantics.}
%\slpj{I still don't know what ``devoid of syntax'' means.  Omit?}
We postpone worries about well-definedness and totality of this encoding to
\Cref{sec:totality}.

\begin{figure}
\begin{minipage}{0.55\textwidth}
\begin{code}
eval  ::  (Trace d, Domain d, HasBind d)
      =>  Exp -> (Name :-> d) -> d
eval e ρ = case e of
  Var x  | x ∈ dom ρ  -> ρ ! x
         | otherwise  -> stuck
  Lam x body -> fun x {-" \iffalse "-}(label e){-" \fi "-} $ \d ->
    step App2 (eval body ((ext ρ x d)))
  App e x  | x ∈ dom ρ  -> step App1 $
               apply (eval e ρ) (ρ ! x)
           | otherwise  -> stuck
  Let x e1 e2 -> bind
    (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
    (\d1 -> step Let1 (eval e2 (ext ρ x (step (Lookup x) d1))))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> con {-" \iffalse "-}(label e){-" \fi "-} k (map (ρ !) xs)
    | otherwise
    -> stuck
  Case e alts -> step Case1 $
    select (eval e ρ) (cont << alts)
    where
       cont (xs, er) ds  |  length xs == length ds
                         =  step Case2 (eval er (exts ρ xs ds))
                         |  otherwise
                         =  stuck
\end{code}
\end{minipage}%
\begin{minipage}{0.44\textwidth}
\begin{code}
class Trace d where
  step :: Event -> d -> d

class Domain d where
  stuck :: d
  fun :: Name -> {-" \iffalse "-}Label -> {-" \fi "-}(d -> d) -> d
  apply :: d -> d -> d
  con :: {-" \iffalse "-}Label -> {-" \fi "-}Tag -> [d] -> d
  select :: d -> (Tag :-> ([d] -> d)) ->  d

class HasBind d where
  bind :: (d -> d) -> (d -> d) -> d
\end{code}
\\[-2.5em]
\subcaption{Interface of traces and values}
  \label{fig:trace-classes}
\begin{code}
instance Trace (T v) where
  step = Step

instance Monad τ => Domain (D τ) where
  stuck = return Stuck
  fun _ {-" \iffalse "-}_{-" \fi "-} f = return (Fun f)
  apply  d a = d >>= \v -> case v of
    Fun f -> f a; _ -> stuck
  con {-" \iffalse "-}_{-" \fi "-} k ds = return (Con k ds)
  select dv alts = dv >>= \v -> case v of
    Con k ds | k ∈ dom alts  -> (alts ! k) ds
    _                        -> stuck

ifPoly (instance HasBind DName where
  bind rhs body = body (let d = rhs d in d)
\end{code}
\\[-2.5em]
\subcaption{Concrete by-name semantics for |DName|}
  \label{fig:trace-instances}
\end{minipage}%
\\[-0.5em]
\caption{Abstract Denotational Interpreter}
  \label{fig:eval}
\end{figure}

\subsection{The Interpreter}

Traditionally, a denotational semantics is expressed as a mathematical function,
often written |dsem e ρ|, to give an expression |e :: Exp| a meaning, or
\emph{denotation}, in terms of some semantic domain |D|.
The environment |ρ :: Name :-> D| gives meaning to the free variables of |e|,
by mapping each free variable to its denotation in |D|.
We sketch the Haskell encoding of |Exp| in \Cref{fig:syntax} and the API of
environments and sets in \Cref{fig:map}.
For concise notation, we will use a small number of infix operators: |(:->)| as
a synonym for finite |Map|s, with |m ! x| for looking up |x| in |m|, |ext m x
d| for updates, |assocs m| for a list of key-value pairs in |m|, |f << m| for
mapping |f| over every value in |m|, |dom m| for the set of keys present in the
map, and |(`elem`)| for membership tests in that set.

Our denotational interpreter |eval :: Exp -> (Name :-> DName) -> DName| can
have a similar type as |dsem|.
However, to derive both dynamic semantics and static analysis as instances of the same
generic interpreter |eval|, we need to vary the type of its semantic domain,
which is naturally expressed using type-class overloading, thus:
\[
|eval  ::  (Trace d, Domain d, HasBind d) =>  Exp -> (Name :-> d) -> d|
\]
We have parameterised the semantic domain |d| over three type classes |Trace|, |Domain| and |HasBind|, whose signatures are given in \Cref{fig:trace-classes}.%
\footnote{One can think of these type classes as a fold-like final encoding~\citep{Carette:07} of a domain. However, the significance is in the \emph{decomposition} of the domain, not the choice of encoding.}
Each of the three type classes offer knobs that we will tweak to derive
different evaluation strategies as well as static analyses.

\Cref{fig:eval} gives the complete definition of |eval| together with instances for domain |DName| that we introduced in \Cref{sec:dna}.
Together this is enough to actually run the denotational interpreter to produce traces.
We use |read :: String -> Exp| as a parsing function, and a |Show| instance for
|D τ| that displays traces.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:

< ghci> eval (read "let i = λx.x in i i") emp :: DName
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$,
\\[\belowdisplayskip]
\noindent
where $\langle\lambda\rangle$
\sven{Is it possible to spell out what the lambda is? Its just $\langle λx.x \rangle$, correct? I know that it its not possible in Haskell, but maybe just here in the paper.}
means that the trace ends in a |Fun| value.
We cannot in general print |DName|s or |Fun|ctions thereof, but in this case the result would be $\langle \Lam{x}{x} \rangle$.
\sg{Is this clarifying sentence helpful? I don't really think so...}
This is in direct correspondence to the earlier call-by-name small-step trace
\labelcref{ex:trace} in \Cref{sec:op-sem}.

The definition of |eval|, given in \Cref{fig:eval}, is by structural recursion over the input expression.
For example, to get the denotation of |Lam x body|, we must recursively invoke |eval| on |body|, extending the environment to bind |x| to its denotation.
We wrap that body denotation in |step App2|, to prefix the trace of |body| with an |App2| event whenever the function is invoked, where |step| is a method of class |Trace|.
Finally, we use |fun| to build the returned denotation; the details necessarily depend on the |Domain|, so |fun| is a method of class |Domain|.
While the lambda-bound |x::Name| passed to |fun| is ignored in in the
|Domain DName| instance of the concrete by-name semantics, it is useful for
abstract domains such as that of usage analysis (\Cref{sec:abstraction}).
The other cases follow a similar pattern; they each do some work, before handing
off to type class methods to do the domain-specific work.

The |HasBind| type class defines a particular \emph{evaluation strategy}, as we shall see in
\Cref{sec:evaluation-strategies}.
The |bind| method of |HasBind| is used to give meaning to recursive let
bindings:
it takes two functionals
for building the denotation of the right-hand side and that of the let body,
given a denotation for the right-hand side.
The concrete implementation for |bind| given in \Cref{fig:trace-instances}
computes a |d| such that |d = rhs d| and passes the recursively-defined |d| to
|body|.%
\footnote{Such a |d| correponds to the \emph{guarded fixpoint} of |rhs|.
Strict languages can define this fixpoint as |d () = rhs (d ())|.}
Doing so yields a call-by-name evaluation strategy, because the trace |d|
will be unfolded at every occurrence of |x| in the right-hand side |e1|.
We will shortly see examples of eager evaluation strategies that will yield from
|d| inside |bind| instead of calling |body| immediately.

We conclude this subsection with a few examples.
First we demonstrate that our interpreter is \emph{productive}:
we can observe prefixes of diverging traces without risking a looping
interpreter.
To observe prefixes, we use a function |takeT :: Int -> T v -> T (Maybe v)|:
|takeT n τ| returns the first |n| steps of |τ| and replaces the final value
with |Nothing| (printed as $...$) if it goes on for longer.

< ghci> takeT 5 $ eval (read "let x = x in x") emp :: T (Maybe (Value T))
$\perform{takeName 5 $ eval (read "let x = x in x") emp :: T (Maybe (Value (ByName T)))}$

< ghci> takeT 9 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe (Value T))
$\perform{takeName 9 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe (Value (ByName T)))}$
\\[\belowdisplayskip]
\noindent

The reason |eval| is productive is due to the coinductive nature of |T|'s
definition in Haskell.%
\footnote{In a strict language, we need to introduce a thunk in
the definition of |Step|, \eg, @Step of event * (unit -> 'a t)@.}
Productivity requires that the monadic bind operator |(>>=)| for |T|
guards the recursion, as in the delay monad of \citet{Capretta:05}.

Data constructor values are printed as $Con(K)$, where $K$ indicates the
|Tag|.
Data types allow for interesting ways (type errors) to get |Stuck| (\ie, the
\textbf{wrong} value of \citet{Milner:78}), printed as $\lightning$:

< ghci> eval (read "let zro = Z() in let one = S(zro) in case one of { S(z) -> z }") emp :: DName
$\perform{eval (read "let zro = Z() in let one = S(zro) in case one of { S(zz) -> zz }") emp :: D (ByName T)}$

< ghci> eval (read "let zro = Z() in zro zro") emp :: DName
$\perform{eval (read "let zro = Z() in zro zro") emp :: D (ByName T)}$

\subsection{More Evaluation Strategies}
\label{sec:evaluation-strategies}

\sven{Start with the motivation for this section:
In this section, we derive the evaluation strategies call-by-name, call-by-need, call-by-value, clearvoyant call-by-value, ... \emph{from the same generic denotational interpreter}. This has the following benefits over traditional approaches that describe evaluation strategies with separate interpreters:
\begin{itemize}
\item Unified understanding: It is easier to understand how different evaluation strategies relate to each other if they are derived from the same generic interpreter
\item Shared Meta Theory: Proofs about the generic denotational interpreter carry over to different evaluation strategies more easily
\item Unified Program Transformations: Program transformations such as optimizations and automated refactorings can be proven correct over multiple evaluation strategies simulaneously.
\item ...
\end{itemize}}

By varying the |HasBind| instance of our type |D|, we can endow our language
|Exp| with different evaluation strategies.
Following a similar approach as~\citet{adi}, we maximise reuse by instantiating
the same |D| at different wrappers of |T|, rather than reinventing |Value| and |T|.

\begin{figure}
\begin{spec}
data ByName τ v = ByName { unByName :: τ v }
instance Monad τ => Monad (ByName τ) where ...
instance Trace (τ v) => Trace (ByName τ v) where ...
instance HasBind (D (ByName τ)) where ...
\end{spec}
%if style == newcode
\begin{code}
newtype ByName τ v = ByName { unByName :: (τ v) }
  deriving newtype (Functor,Applicative,Monad)

instance Trace (τ v) => Trace (ByName τ v) where
  step e = ByName . step e . unByName

instance HasBind (D (ByName τ)) where
  bind rhs body = body (fix rhs)
\end{code}%
%endif
\\[-1em]
\caption{Redefinition of call-by-name semantics from \Cref{fig:trace-instances}}
\label{fig:by-name}
\end{figure}

\subsubsection{Call-by-name}

We redefine\sven{Redefinitions are very confusing, because readers may miss them. Why don't we present this as the original definition of |DName| to begin with?} by-name semantics via the |ByName| \emph{trace transformer}
in \Cref{fig:by-name}\sven{Figure 6 does not contain any new information. Literally all implementations are omitted. I would remove Figure 6 to save space.},%
\footnote{The Supplement defines these datatypes as |newtype|s.\sven{So why do you define them as |data| types here? Just define them as |newtype|s here and omit this footnote.}}
so called because |ByName τ| inherits its |Monad| and |Trace|
instance from |τ| (busywork we omit) and reminiscent of \citet{Darais:15}.
Our old |DName| can be recovered as |D (ByName T)|.

\begin{figure}
\begin{code}
-- \sven{Why do you show the Event type again? Doesn't it stay the same throughout the evaluation strategies? If this is the case, I would just omit it here.}
ifPoly(data ByValue τ v = ByValue { unByValue :: τ v }; data Event = ... | Let0)
-- \sven{If you don't include any details in the |Monad| and |Trace| instances, I would just omit them, because as is they don't provide any new information.}
ifPoly(instance Monad τ => Monad (ByValue τ) where ...)
instance Trace (τ v) => Trace (ByValue τ v) where {-" ... \iffalse "-}
  step e (ByValue τ) = ByValue (step e τ) {-" \fi "-}

-- \sven{Function |extract| gets the value of a trace. So maybe |getValue| is a better name? Also it's definition is trivial, so maybe its code can be omitted entirely.}
class Extract τ where extract :: τ v -> v
instance Extract T where extract (Ret v) = v; extract (Step _ τ) = extract τ

instance (Trace (D (ByValue τ)), Monad τ, Extract τ) => HasBind (D (ByValue τ)) where
  bind rhs body = step Let0 (d >>=  \v1 -> body (return v1)) -- \sven{Why not use do notation?}
                                   -- \sven{Maybe we could use a combinator like |fix| to make it clearer that we are computing a fixpoint here.}
                                   where  d = rhs (return v)         :: D (ByValue τ)
                                          v = extract (unByValue d)  :: Value (ByValue τ)
\end{code}
%if style == newcode
\begin{code}
newtype ByValue τ v = ByValue { unByValue :: τ v }
  deriving (Functor,Applicative,Monad)
\end{code}
%endif
\\[-1em]
\caption{Call-by-value }
\label{fig:by-value}
\end{figure}

\subsubsection{Call-by-value}

Call-by-value eagerly evaluates a let-bound RHS and then substitutes its
\emph{value}, rather than the reduction trace that led to the value, into every
use site. %\slpj{I could not follow this sentence.} \sg{Better?}

The call-by-value evaluation strategy is implemented with the |ByValue| trace transformer shown in \Cref{fig:by-value}.
Function |bind| first yields a |Let0| event, indicating in the
trace that the right-hand side of a |let| is evaluated first.
Then monadic bind |v <- d; body (return v1)| yields steps from |d|
(discussed shortly) until its value |v1 :: Value (ByValue τ)| is reached, which
is then passed |return|ed (\ie, wrapped in |Ret|) to the let |body|.
Note that the steps in |d| are yielded \emph{eagerly}, and only once, rather
than duplicating the trace at every use site in |body|, as the by-name form
|body d| would.

The |d :: D (ByValue τ)| denotes the recursive semantics of the right-hand side
and is defined by mutual recursion with |v :: Value (ByValue τ)|.
Consider the case |τ = T|; then |return = Ret| and the |d = rhs (Ret v)| for
the value |v| at the end of the trace |d|.
The purpose of the type class instance method |extract :: T v -> v| applied to |d| is supposed
to run down |d| and return the  |v|.%
\footnote{The keen reader may have noted that we could use |Extract| to define a
|MonadFix| instance for deterministic |τ|.}

Since nothing about |extract| is particularly special to |T|, it lives in its
own type class |Extract| so that we get a |HasBind| instance for different
types of |Trace|s, such as more abstract ones in \Cref{sec:abstraction}.

Let us trace $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$ for call-by-value:

< ghci> eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)
$\perform{eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)}$
\\[\belowdisplayskip]
\noindent
The beta reduction of $(\Lam{y}{\Lam{x}{x}})~i$ now happens once within the
$\LetOT$/$\LetIT$ bracket; the two subsequent $\LookupT$ events immediately halt
with a value.

Alas, this model of call-by-value does not yield a total interpreter!
Consider the case when the right-hand side accesses its value before yielding
one, \eg,

< ghci> takeT 5 $ eval (read "let x = x in x x") emp :: ByValue T (Maybe (Value (ByValue T)))
$\LetOT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\LetIT\xhookrightarrow{\hspace{1.1ex}}\AppIT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\texttt{\textasciicircum{}CInterrupted}$
\\[\belowdisplayskip]
\noindent
This loops forever unproductively, rendering the interpreter unfit as a
denotational semantics.
We will discuss a remedy in the form of lazy initialisation in
\Cref{sec:lazy-init}.

\begin{figure}
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
-- \sven{This is just the state monad. So why not define it by |newtype ByNeed τ v = ByNeed (State (Heap (ByNeed τ)) v)|. Then you could also omit the definitions of |get| and |put|.}
ifCodeElse(newtype ByNeed τ v)(data ByNeed τ v) = ByNeed { unByNeed :: Heap (ByNeed τ) -> τ (v, Heap (ByNeed τ)) }

getN  :: Monad τ => ByNeed τ (Heap (ByNeed τ));         getN    = ByNeed (\ μ -> return (μ, μ))
putN  :: Monad τ => Heap (ByNeed τ) -> ByNeed τ (); ^^  putN μ  = ByNeed (\ _ -> return ((), μ))
ifPoly(instance Monad τ => Monad (ByNeed τ) where ...)

instance (forall v. Trace (τ v)) => Trace (ByNeed τ v) where step e m = ByNeed (step e . unByNeed m)

fetchN :: Monad τ => Addr -> D (ByNeed τ); fetchN a = getN >>= \μ -> μ ! a

memoN :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memoN a d = d >>= \v -> ByNeed (upd v)
  where  upd Stuck  μ = return (Stuck :: Value (ByNeed τ), μ)
         upd v      μ = step Update (return (v, ext μ a (memoN a (return v))))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByNeed τ)) where
  bind rhs body = do  μ <- getN
                      let a = nextFree μ
                      putN (ext μ a (memoN a (rhs (fetchN a))))
                      body (fetchN a)
\end{code}
%if style == newcode
\begin{code}
nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

deriving via StateT (Heap (ByNeed τ)) τ instance Functor τ  => Functor (ByNeed τ)
deriving via StateT (Heap (ByNeed τ)) τ instance Monad τ    => Applicative (ByNeed τ)
deriving via StateT (Heap (ByNeed τ)) τ instance Monad τ    => Monad (ByNeed τ)
\end{code}
%endif
\\[-1em]
\caption{Call-by-need}
\label{fig:by-need}
\end{figure}

\subsubsection{Call-by-need}

The trace transformer |ByNeed| in \Cref{fig:by-need} defines a call-by-need
evaluation strategy by introducing a stateful heap and memoisation to |τ|
by embedding a standard state transformer monad,%
\footnote{Indeed, we derive its monad instance |via StateT (Heap (ByNeed τ))
τ|~\citep{Blondal:18}.}
whose key operations |getN| and |putN| are given in \Cref{fig:by-need}.

\sven{The storyline of this subsection can be improved.
Currently, in the following paragraph it is unclear what you are getting at.
I propose the following storyline:
\begin{enumerate}
\item Explain what the goal is you want to achieve: Define denotation for call-by-need languages
\item Explain the problems you run into when doing this naively: When defining the denotation of an expression as a trace this does not work because ...
\item Explain how you solved the problem: Therefore, we design the denotation as a stateful function returning a trace. This stateful function is the result of solving the recurisve equation $|(Heap θ -> τ (Value θ, Heap θ))| \cong |D θ|$.
\item Explain the details of your solution (explain fig 8).
\end{enumerate}}

|ByNeed τ| is best thought of as an answer to the request ``give me a |θ| such
that |D θ| models stateful computations in |D θ|''.
More formally, |θ := ByNeed τ| satisfies the recursion equation
$|(Heap θ -> τ (Value θ, Heap θ))| \cong |D θ|$ via |ByNeed| and its inverse
|unByNeed|\sven{You use this as a motivation for your definition of the denotation of call-by-value languages. But to me it is unclear what insight this provides. What can the reader learn from that the denotation is the solution to this recursive equation?}.

So the denotation of an expression is no longer a trace, but rather a
\emph{stateful function returning a trace}, where the carried state
|Heap (ByNeed τ)| implements the heap in which call-by-need thunks are
allocated.
The |Trace| instance of |ByNeed τ| simply forwards to that of |τ| (\ie, often
|T|), pointwise over heaps.
Doing so needs a |Trace| instance for |τ (Value (ByNeed τ), Heap (ByNeed τ))|, but we
found it more succinct to use a quantified constraint |(forall v. Trace (τ
v))|, that is, we require a |Trace (τ v)| instance for every choice of |v|\sven{This sentence seems like an implementation detail. Is this really worth discussing?}.
Given that |τ| must also be a |Monad|, that is not an onerous requirement.

The key part is again the implementation of |HasBind| for |D (ByNeed τ)|,
because that is the only place where thunks are allocated.
The implemention of |bind| designates a fresh heap address |a|
to hold the denotation of the right-hand side.
Both |rhs| and |body| are called with |fetchN a|, a denotation that looks up |a|
in the heap and runs it.
If we were to omit the |memo a| action explained next, we would thus have
recovered another form of call-by-name semantics based on mutable state instead
of guarded fixpoints such as in |ByName| and |ByValue|\sven{I don't understand what we learn from this sentence that advances the storyline. The goal of this section is to understand |ByNeed| and not |ByName| or |ByValue|}.
The whole purpose of the |memo a d| combinator then is to \emph{memoise} the
computation of |d| the first time we run the computation, via |fetchN a| in the
|Var| case of |eval|.
So |memo a d| yields from |d| until it has reached a value, and then |upd|ates
the heap after an additional |Update| step.
Repeated access to the same variable will run the replacement |memo a (return
v)|, which immediately yields |v| after performing a |step Update| that does
nothing.%
\footnote{More serious semantics would omit updates after the first
evaluation as an \emph{optimisation}, \ie, update with |ext μ a (return v)|,
but doing so complicates relating the semantics to \Cref{fig:lk-semantics},
where omission of update frames for values behaves differently.
For now, our goal is not to formalise this optimisation, but rather to show
adequacy \wrt an established semantics.}

Although the code is carefully written, it is worth stressing how
compact and expressive it is.  We were able to move from traces to stateful traces
just by wrapping traces |T| in a state transformer |ByNeed|, without modifying
the main |eval| function at all\sven{You need to better describe why this is a benefit of this approach: Traditionally, different evaluation strategies were described with separate interpreters. This has the following downsides ... Here we derive all these evaluation strategies from \emph{the same interpreter} by instantiating it differently. From this we gain ...}\sven{This needs to be moved to the top of the section 4.3 because it motivates the section}.%
\footnote{It is worth noting that nothing in our approach is particularly specific to |Exp| or
|Value|!
We have built similar interpreters for PCF, where the @rec@, @let@ and
non-atomic argument constructs can simply reuse |bind| to recover a
call-by-need semantics.
The |Event| type needs semantics- and use-case-specific adjustment, though.}

Here is an example evaluating $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$, starting
in an empty heap:

< ghci> unByNeed (eval (read "let i = (λy.λx.x) i in i i") emp) emp :: T (Value _, Heap _)
$\perform{unByNeed (eval (read "let i = (λy.λx.x) i in i i") emp) emp :: T (Value (ByNeed T), Heap _)}$
\\[\belowdisplayskip]
\noindent
This trace is in clear correspondence to the earlier by-need LK trace
\labelcref{ex:trace2}.
We can observe memoisation at play:
Between the first bracket of $\LookupT$ and $\UpdateT$ events, the heap entry
for $i$ goes through a beta reduction before producing a value.
This work is cached, so that the second $\LookupT$ bracket does not do any beta
reduction.

\begin{figure}
\begin{code}
ifCodeElse(newtype ByVInit τ v)(data ByVInit τ v) = ByVInit { unByVInit :: Heap (ByVInit τ) -> τ (v, Heap (ByVInit τ)) }
instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByVInit τ)) where
  bind rhs body = do  μ <- getV
                      let a = nextFree μ
                      putV (ext μ a stuck)
                      step Let0 (memoV a (rhs (fetchV a))) >>= body . return
\end{code}
%if style == newcode
\begin{code}
deriving via StateT (Heap (ByVInit τ)) τ instance Functor τ  => Functor (ByVInit τ)
deriving via StateT (Heap (ByVInit τ)) τ instance Monad τ    => Applicative (ByVInit τ)
deriving via StateT (Heap (ByVInit τ)) τ instance Monad τ    => Monad (ByVInit τ)

getV :: Monad τ => ByVInit τ (Heap (ByVInit τ))
getV = ByVInit (\ μ -> return (μ, μ))
putV :: Monad τ => Heap (ByVInit τ) -> ByVInit τ ()
putV μ = ByVInit (\ _ -> return ((), μ))

instance (forall v. Trace (τ v)) => Trace (ByVInit τ v) where step e m = ByVInit (step e . unByVInit m)

fetchV :: Monad τ => Addr -> D (ByVInit τ)
fetchV a = getV >>= \μ -> μ ! a

memoV :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByVInit τ) -> D (ByVInit τ)
memoV a d = d >>= \v -> ByVInit (upd v)
  where  upd Stuck  μ = return (Stuck :: Value (ByVInit τ), μ)
         upd v      μ = return (v, ext μ a (memoV a (return v)))
\end{code}
%endif
\\[-1em]
\caption{Call-by-value with lazy initialisation}
\label{fig:by-value-init}
\end{figure}

\subsubsection{Lazy Initialisation and Black-holing}
\label{sec:lazy-init}

\sven{Why do you discuss this after call-by-need? The storyline would be more cohesive if this subsection would appear directly after call-by-value.}
Recall that our simple |ByValue| transformer above yields a potentially looping
interpreter.
Typical strict languages work around this issue in either of two ways:
They enforce termination of the RHS statically (OCaml, ML), or they use
\emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
We recover a total interpreter using the semantics in \citet{Nakata:10},
building on the same encoding as |ByNeed| and initialising the heap with a
\emph{black hole}~\citep{stg} |stuck| in |bind| as in \Cref{fig:by-value-init}.

< ghci> unByVInit (eval (read "let x = x in x x") emp) emp :: T (Value _, Heap _)
$\perform{unByVInit (eval (read "let x = x in x x") emp) emp :: T (Value (ByVInit T), Heap (ByVInit T))}$


\begin{figure}
\begin{spec}
data Fork f a = Empty | Single a | Fork (f a) (f a); data ParT m a = ParT (m (Fork (ParT m) a))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty); l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant (ParT τ a)
runClair :: D (Clairvoyant T) -> T (Value (Clairvoyant T))

instance (Extract τ, Monad τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind rhs body = Clairvoyant (skip <|> let') >>= body
    where  skip = return (Clairvoyant empty)
           let' = fmap return $ step Let0 $ ... ^^ fix ... rhs ... extract ...
\end{spec}
%if style == newcode
\begin{code}
data Fork f a = Empty | Single !a | Fork (f a) (f a)
  deriving Functor

newtype ParT τ a = ParT { unParT :: τ (Fork (ParT τ) a) }
  deriving Functor

instance Monad τ => Applicative (ParT τ) where
  pure a = ParT (pure (Single a))
  (<*>) = ap
instance Monad τ => Monad (ParT τ) where
  ParT mas >>= k = ParT $ mas >>= \case
    Empty -> pure Empty
    Single a -> unParT (k a)
    Fork l r -> pure (Fork (l >>= k) (r >>= k))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty)
  l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant { unClair :: ParT τ a }
  deriving newtype (Functor,Applicative,Monad)

instance (forall v. Trace (τ v)) => Trace (Clairvoyant τ v) where
  step e (Clairvoyant (ParT mforks)) = Clairvoyant $ ParT $ step e mforks

leftT :: Monad τ => ParT τ a -> ParT τ a
leftT (ParT τ) = ParT $ τ >>= \case
  Fork l _ -> unParT l
  _ -> undefined

rightT :: Monad τ => ParT τ a -> ParT τ a
rightT (ParT τ) = ParT $ τ >>= \case
  Fork _ r -> unParT r
  _ -> undefined

parFix :: (Extract τ, Monad τ) => (Fork (ParT τ) a -> ParT τ a) -> ParT τ a
parFix f = ParT $ fix (unParT . f . extract) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork _ _ -> pure (Fork (parFix (leftT . f)) (parFix (rightT . f)))

instance (Extract τ, Monad τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind rhs body = Clairvoyant (skip <|> let') >>= body
    where
      skip = return (Clairvoyant empty)
      let' = fmap return $ unClair $ step Let0 $ Clairvoyant $ parFix $ unClair . rhs . Clairvoyant . ParT . return

headParT :: (Monad τ, Extract τ) => ParT τ v -> τ (Maybe v)
headParT τ = go τ
  where
    go :: (Monad τ, Extract τ) => ParT τ v -> τ (Maybe v)
    go (ParT τ) = τ >>= \case
      Empty    -> pure Nothing
      Single a -> pure (Just a)
      Fork l r -> case extract (go l) of
        Nothing -> go r
        Just _  -> go l

runClair :: (Monad τ, Extract τ) => D (Clairvoyant τ) -> τ (Value (Clairvoyant τ))
runClair (Clairvoyant m) = headParT m >>= \case
  Nothing -> error "There should have been at least one Clairvoyant trace"
  Just t  -> pure t
\end{code}
%endif
\\[-1em]
\caption{Clairvoyant Call-by-value}
\label{fig:clairvoyant-by-value}
\end{figure}

\subsubsection{Clairvoyant Call-by-value}

Clairvoyant call-by-value~\citep{HackettHutton:19} is an approach to
call-by-need semantics that exploits non-determinism and a cost model to absolve
of the heap.
We can instantiate our interpreter to generate the shortest clairvoyant
call-by-value trace as well, as sketched out in \Cref{fig:clairvoyant-by-value}.
Doing so yields an evaluation strategy that either skips or speculates let
bindings, depending on whether or not the binding is needed:

< ghci> runClair $ eval (read "let f = λx.x in let g = λy.f in g") emp :: T (Value (Clairvoyant T))
$\perform{runClair $ eval (read "let f = λx.x in let g = λy.f in g") emp :: T (Value (Clairvoyant T))}$

< ghci> runClair $ eval (read "let f = λx.x in let g = λy.f in g g") emp :: T (Value (Clairvoyant T))
$\perform{runClair $ eval (read "let f = λx.x in let g = λy.f in g g") emp :: T (Value (Clairvoyant T))}$
\\[\belowdisplayskip]
\noindent
The first example discards $f$, but the second needs it, so the trace starts
with an additional $\LetOT$ event.
Similar to |ByValue|, the interpreter is not total so it is unfit as a
denotational semantics without a complicated domain theoretic judgment.
Furthermore, the decision whether or not a $\LetOT$ is needed can be delayed for
an infinite amount of time, as exemplified by

< ghci> runClair $ eval (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))
%$\perform{runClair $ eval (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))}$
\texttt{\textasciicircum{}CInterrupted}
\\[\belowdisplayskip]
\noindent
The program diverges without producing even a prefix of a trace because the
binding for $i$ might be needed at an unknown point in the future
(a \emph{liveness property} and hence impossible to verify at runtime).
This renders Clairvoyant call-by-value inadequate for verifying properties of
infinite executions.

\subsection{More Trace Types}
\label{sec:more-trace-types}

\sven{I don't this section. What problem does this solve?}

Our simple trace type |T| has served us well so far, allowing us to study a
variety of total denotational interpreters for all major evaluation strategies
(\eg, |ByName|, |ByNeed|, |ByVInit|).
It is of course possible in Haskell to abandon totality, discard all events and
use plain |data Identity a = Identity a| as the trace type accompanied by the
definition |instance Trace Identity where step _ = id|.
The resulting interpreter diverges whenever the defined program diverges, as is
typical for partial definitional interpreters:

%if style == newcode
\begin{code}
instance Trace (Identity v) where step _ = id
\end{code}
%endif

< ghci> eval (read "let i = λx.x in i i") emp :: D (ByName Identity)
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName Identity)}$

< ghci> eval (read "let x = x in x") emp :: D (ByName Identity)
%$\perform{eval (read "let x = x in x") emp :: D (ByName Identity)}$
\texttt{\textasciicircum{}CInterrupted}
\\[\belowdisplayskip]
\noindent
