%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures
% Need the -XPartialTypeSignatures for the CbNeed example, for some weird reason
%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints -Wno-unused-matches #-}
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
  show (Look x) = "\\LookupT(" ++ x ++ ")"
  show App1 = "\\AppIT"
  show App2 = "\\AppET"
  show Case1 = "\\CaseIT"
  show Case2 = "\\CaseET"
  show Let0 = "\\LetOT"
  show Let1 = "\\LetIT"
  show Upd = "\\UpdateT"
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret a) = "\\langle "++show a++"\\rangle "
instance {-# OVERLAPPING #-} Show a => Show (T (Maybe a)) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret Nothing)  = "..."
  show (Ret (Just a)) = "\\langle "++show a++"\\rangle "
instance Show (Value τ) where
  show (Fun _) = "\\lambda"
  show (Con k _) = "\\mathit{Con}(" ++ show k ++ ")"
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

In this section, we present a generic \emph{denotational interpreter}%
\footnote{This term was coined by \citet{Might:10}. We find it fitting,
because a denotational interpreter is both a \emph{denotational
semantics}~\citep{ScottStrachey:71} as well as a total \emph{definitional
interpreter}~\citep{Reynolds:72}.}
for a functional language which we instantiate with different semantic domains.
The choice of semantic domain determines the \emph{evaluation strategy}
(call-by-name, call-by-value, call-by-need) and the degree to which
\emph{operational detail} can be observed.
Yet different semantic domains give rise to useful \emph{summary-based} static
analyses such as usage analysis in \Cref{sec:abstraction}.
The major contribution of our framework is that the derived summary-based
analyses may observe operational detail in an intuitive and semantically
meaningful way.
Adhering to our design pattern pays off in that it enables sharing of soundness
proofs, thus drastically simplifying the soundness proof obligation per derived
analysis (\Cref{sec:soundness}).

Denotational interpreters can be implemented in any higher-order language such as OCaml, Scheme or Java with explicit thunks, but we picked Haskell for convenience.%
\footnote{We extract from this document runnable Haskell files which we add as a Supplement, containing the complete definitions. Furthermore, the (terminating) interpreter outputs are directly generated from this extract.}

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
singenv x d = Map.singleton x d
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
is the whole point of analyses such as usage analysis (\Cref{sec:abstraction}).

A distinctive feature of our work is that our semantic domains are instead
\emph{traces} that describe the \emph{steps} taken by an abstract machine, and
that \emph{end} in semantic values.
It is possible to describe usage cardinality as a property of the traces
thus generated, as required for a soundness proof of usage analysis.
We choose |DName|, defined below, as the first example of such a semantic domain,
because it is simple and illustrative of the approach.
Instantiated at |DName|, our generic interpreter will produce precisely the
traces of the by-\textbf{\textrm{na}}me variant of the Krivine machine in
\Cref{fig:lk-semantics}.%
\footnote{For a realistic implementation, we would define |D| as a |newtype| to
keep type class resolution decidable and non-overlapping. We will however stick
to a |type| synonym in this presentation in order to elide noisy wrapping and
unwrapping of constructors.}

\begin{minipage}{0.62\textwidth}
\begin{code}
type D τ = τ (Value τ);   type DName = D T
data T v = Step Event (T v) | Ret v
ifPoly(data Event  =  Look Name | Upd | App1 | App2
                   |  Let1 | Case1 | Case2)
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
data Event  =  Look Name | Upd | App1 | App2
            |  Let0 | Let1 | Case1 | Case2
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
Each step |Step ev rest| is decorated with an event |ev|, which describes what happens in that step.
For example, event |Look x| describes the lookup of variable |x :: Name| in the environment.
Note that the choice of |Event| is use-case (\ie analysis) specific and suggests
a spectrum of intensionality, with |data Event = Unit| on the more abstract end
of the spectrum and arbitrary syntactic detail attached to each of |Event|'s
constructors at the intensional end of the spectrum.%
\footnote{If our language had facilities for input/output and more general
side-effects, we could have started from a more elaborate trace construction
such as (guarded) interaction trees~\citep{interaction-trees,gitrees}.}

A trace in |DName = T (Value T)| eventually terminates with a |Value| that is
either stuck (|Stuck|), a function waiting to be applied to a domain value
(|Fun|), or a constructor application giving the denotations of its
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
  Let x e1 e2 -> bind {-" \iffalse "-}x{-" \fi "-}
    (\d1 -> eval e1 (ext ρ x (step (Look x) d1)))
    (\d1 -> step Let1 (eval e2 (ext ρ x (step (Look x) d1))))
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
  bind :: {-" \iffalse "-}Name -> {-" \fi "-}(d -> d) -> (d -> d) -> d
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
  bind # rhs body = let d = rhs d in body d
\end{code}
\\[-2.5em]
\subcaption{Concrete by-name semantics for |DName|}
  \label{fig:trace-instances}
\end{minipage}%
\\[-0.5em]
\caption{Denotational Interpreter}
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
a synonym for finite |Map|s, with |m ! x| for looking up |x| in |m|, |emp| for
the empty map, |ext m x d| for updates, |assocs m| for a list of key-value pairs
in |m|, |f << m| for mapping |f| over every value in |m|, |dom m| for the set of
keys present in the map, and |(`elem`)| for membership tests in that set.

Our denotational interpreter |eval :: Exp -> (Name :-> DName) -> DName| can
have a similar type as |dsem|.
However, to derive both dynamic semantics and static analysis as instances of the same
generic interpreter |eval|, we need to vary the type of its semantic domain,
which is naturally expressed using type class overloading, thus:
\[
|eval  ::  (Trace d, Domain d, HasBind d) =>  Exp -> (Name :-> d) -> d|.
\]
We have parameterised the semantic domain |d| over three type classes |Trace|, |Domain| and |HasBind|, whose signatures are given in \Cref{fig:trace-classes}.
%\footnote{One can think of these type classes as a fold-like final encoding~\citep{Carette:07} of a domain. However, the significance is in the \emph{decomposition} of the domain, not the choice of encoding.}
Each of the three type classes offer knobs that we will tweak to derive
different evaluation strategies as well as static analyses.

\Cref{fig:eval} gives the complete definition of |eval| together with instances for domain |DName| that we introduced in \Cref{sec:dna}.
Together this is enough to actually run the denotational interpreter to produce traces.
We use |read :: String -> Exp| as a parsing function and a |Show| instance for
|D τ| that displays traces.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:

< ghci> eval (read "let i = λx.x in i i") emp :: DName
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$,
\\[\belowdisplayskip]
\noindent
where $\langle\lambda\rangle$
%\sven{Is it possible to spell out what the lambda is? Its just $\langle λx.x \rangle$, correct? I know that it its not possible in Haskell, but maybe just here in the paper.}
means that the trace ends in a |Fun| value.
We cannot print |DName| or |Fun|ctions thereof, but in this case the result would be the value $\Lam{x}{x}$.
%\sg{Is this clarifying sentence helpful? I don't really think so...}
This is in direct correspondence to the earlier call-by-name small-step trace
\labelcref{ex:trace} in \Cref{sec:op-sem}.

The definition of |eval|, given in \Cref{fig:eval}, is by structural recursion over the input expression.
For example, to get the denotation of |Lam x body|, we must recursively invoke |eval| on |body|, extending the environment to bind |x| to its denotation.
We wrap that body denotation in |step App2|, to prefix the trace of |body| with an |App2| event whenever the function is invoked, where |step| is a method of class |Trace|.
Finally, we use |fun| to build the returned denotation; the details necessarily depend on the |Domain|, so |fun| is a method of class |Domain|.
While the lambda-bound |x::Name| passed to |fun| is ignored in the
|Domain DName| instance of the concrete by-name semantics, it is useful for
abstract domains such as that of usage analysis (\Cref{sec:abstraction}).
(We refrain from passing field binders or other syntactic tokens in |select|
and let binders in |bind| as well, because the analyses considered do not need
them.)
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
\footnote{Such a |d| corresponds to the \emph{guarded fixpoint} of |rhs|.
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
the definition of |Step|, \eg @Step of event * (unit -> 'a t)@.}
Productivity requires that the monadic bind operator |(>>=)| for |T|
guards the recursion, as in the delay monad of \citet{Capretta:05}.

Data constructor values are printed as $Con(K)$, where $K$ indicates the
|Tag|.
Data types allow for interesting ways (type errors) to get |Stuck| (\ie the
\textbf{wrong} value of \citet{Milner:78}), printed as $\lightning$:

< ghci> eval (read "let zro = Z() in let one = S(zro) in case one of { S(z) -> z }") emp :: DName
$\perform{eval (read "let zro = Z() in let one = S(zro) in case one of { S(zz) -> zz }") emp :: D (ByName T)}$

< ghci> eval (read "let zro = Z() in zro zro") emp :: DName
$\perform{eval (read "let zro = Z() in zro zro") emp :: D (ByName T)}$

\subsection{More Evaluation Strategies}
\label{sec:evaluation-strategies}

%\sven{Start with the motivation for this section:
%In this section, we derive the evaluation strategies call-by-name, call-by-need, call-by-value, clearvoyant call-by-value, ... \emph{from the same generic denotational interpreter}. This has the following benefits over traditional approaches that describe evaluation strategies with separate interpreters:
%\begin{itemize}
%\item Unified understanding: It is easier to understand how different evaluation strategies relate to each other if they are derived from the same generic interpreter
%\item Shared Meta Theory: Proofs about the generic denotational interpreter carry over to different evaluation strategies more easily
%\item Unified Program Transformations: Program transformations such as optimizations and automated refactorings can be proven correct over multiple evaluation strategies simulaneously.
%\item ...
%\end{itemize}}
%\sg{See slack; Let's motivate Unified Understanding and leave the rest. (See below.)
%Sadly, no time nor space to substantiate those claims.}

By varying the |HasBind| instance of our type |D|, we can endow our language
|Exp| with different evaluation strategies.
The appeal of that is, firstly, that it is possible to do so without changing
the interpreter definition, supporting the claim that the denotational
interpreter design pattern is equally suited to model lazy as well as strict
semantics.
More importantly, in order to prove usage analysis sound \wrt by-need evaluation
in \Cref{sec:soundness}, we need to define a semantic domain for call-by-need!
It turns out that the interpreter thus derived is the --- to our knowledge ---
first provably adequate denotational semantics for call-by-need (\Cref{sec:adequacy}).

Although the main body discusses only by-name and by-need semantics,
we provide instances for call-by-value as well as clairvoyant
semantics~\citep{HackettHutton:19} in \Cref{sec:more-eval-strat} as well.

\subsubsection{Call-by-name}

Following a similar approach as~\citet{adi}, we maximise reuse by instantiating
the same |D| at different wrappers of |T|, rather than reinventing |Value| and |T|.
Hence we redefine
%\sven{Redefinitions are very confusing, because readers may miss them. Why don't we present this as the original definition of |DName| to begin with?}
%\sg{I'm hesitant because the reader then is exposed early to a deep stack
%of type synonyms/newtypes. We would need to write |ByName T (Maybe (Value
%(ByName T)))| in a couple of places; seems a bit too much faff.}
by-name semantics via the following |ByName| newtype wrapper:
\begin{code}
evalName e ρ = eval e ρ :: D (ByName T)
newtype ByName τ v = ByName { unByName :: τ v } deriving (Monad, Trace)
instance HasBind (D (ByName τ)) where bind # rhs body = let d = rhs d in body d
\end{code}
%if style == newcode
\begin{code}
deriving newtype instance Functor τ => Functor (ByName τ)
deriving newtype instance Applicative τ => Applicative (ByName τ)
\end{code}
%endif
%\sven{Figure 6 does not contain any new information. Literally all implementations are omitted. I would remove Figure 6 to save space.}
%\sg{Doubtful that doing so saves much space, and the implications |Trace τ => Trace (ByName τ)| and |Monad τ => ByName τ| are still useful.}
We call |ByName τ| a \emph{trace transformer} because it inherits its |Monad|
and |Trace| instance from |τ|, in reminiscence to Galois transformers~\citep{Darais:15}.
The old |DName| can be recovered as |D (ByName T)| and we refer to its
interpreter instance as |evalName e ρ|.

\subsubsection{Call-by-need}
\label{sec:by-need-instance}

\begin{figure}
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
newtype ByNeed τ v = ByNeed { unByNeed :: Heap (ByNeed τ) -> τ (v, Heap (ByNeed τ)) }

type DNeed = D (ByNeed T); type ValueNeed = Value (ByNeed T); type HeapNeed = Heap (ByNeed T)
evalNeed e ρ μ = unByNeed (eval e ρ :: DNeed) μ

getN  :: Monad τ => ByNeed τ (Heap (ByNeed τ));         getN    = ByNeed (\ μ -> return (μ, μ))
putN  :: Monad τ => Heap (ByNeed τ) -> ByNeed τ (); ^^  putN μ  = ByNeed (\ _ -> return ((), μ))
ifPoly(instance Monad τ => Monad (ByNeed τ) where ...)

instance (forall v. Trace (τ v)) => Trace (ByNeed τ v) where step e m = ByNeed (step e . unByNeed m)

fetchN :: Monad τ => Addr -> D (ByNeed τ); fetchN a = getN >>= \μ -> μ ! a

memoN :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memoN a d = d >>= \v -> ByNeed (upd v)
  where  upd Stuck  μ = return (Stuck :: Value (ByNeed τ), μ)
         upd v      μ = step Upd (return (v, ext μ a (memoN a (return v))))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByNeed τ)) where
  bind # rhs body = do  μ <- getN
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

The use of a stateful heap is essential to the call-by-need evaluation strategy
in order to enable memoisation.
So how do we vary |θ| such that |D θ| accommodates state?
We certainly cannot perform the heap update by updating entries in |ρ|,
because those entries are immutable once inserted, and we do not want to change
the generic interpreter.
That rules out $|θ| \cong |T|$ (as for |ByName T|), because then repeated
occurrences of the variable |x| must yield the same trace |ρ ! x|.
However, the whole point of memoisation is that every evaluation of |x| after
the first one leads to a potentially different, shorter trace.
This implies we have to \emph{paramaterise} every occurrence of |x| over the
current heap |μ| at the time of evaluation, and every evaluation of |x| must
subsequently update this heap with its value, so that the next evaluation
of |x| returns the value directly.
In other words, we need a representation $|D θ| \cong |Heap -> T (Value θ,
Heap)|$.

Our trace transformer |ByNeed| in \Cref{fig:by-need} solves this type equation
via |θ := ByNeed T|.
It embeds a standard state transformer monad,
%\footnote{Indeed, we derive its monad instance |via StateT (Heap (ByNeed τ))
%τ|~\citep{Blondal:18}.}
whose key operations |getN| and |putN| are given in \Cref{fig:by-need}.

So the denotation of an expression is no longer a trace, but rather a
\emph{stateful function returning a trace} with state |Heap (ByNeed τ)| in
which to allocate call-by-need thunks.
The |Trace| instance of |ByNeed τ| simply forwards to that of |τ| (\ie often
|T|), pointwise over heaps.
Doing so needs a |Trace| instance for |τ (Value (ByNeed τ), Heap (ByNeed τ))|, but we
found it more succinct to use a quantified constraint |(forall v. Trace (τ
v))|, that is, we require a |Trace (τ v)| instance for every choice of |v|.
Given that |τ| must also be a |Monad|, that is not an onerous requirement.

The key part is again the implementation of |HasBind| for |D (ByNeed τ)|,
because that is the only place where thunks are allocated.
The implementation of |bind| designates a fresh heap address |a|
to hold the denotation of the right-hand side.
Both |rhs| and |body| are called with |fetchN a|, a denotation that looks up |a|
in the heap and runs it.
If we were to omit the |memo a| action explained next, we would thus have
recovered another form of call-by-name semantics based on mutable state instead
of guarded fixpoints such as in |ByName| and |ByValue|.
The whole purpose of the |memo a d| combinator then is to \emph{memoise} the
computation of |d| the first time we run the computation, via |fetchN a| in the
|Var| case of |evalNeed2|.
So |memo a d| yields from |d| until it has reached a value, and then |upd|ates
the heap after an additional |Upd| step.
Repeated access to the same variable will run the replacement |memo a (return
v)|, which immediately yields |v| after performing a |step Upd| that does
nothing.%
\footnote{More serious semantics would omit updates after the first
evaluation as an \emph{optimisation}, \ie update with |ext μ a (return v)|,
but doing so complicates relating the semantics to \Cref{fig:lk-semantics},
where omission of update frames for values behaves differently.
For now, our goal is not to formalise this optimisation, but rather to show
adequacy \wrt an established semantics.}

Although the code is carefully written, it is worth stressing how
compact and expressive it is.
We were able to move from traces to stateful traces just by wrapping traces |T|
in a state transformer |ByNeed|, without modifying the main |eval| function at
all.
In doing so, we provide the simplest encoding of a denotational by-need semantics
that we know of.%
%\footnote{It is worth noting that nothing in our approach is particularly specific to |Exp| or
%|Value|!
%We have built similar interpreters for PCF, where the @rec@, @let@ and
%non-atomic argument constructs can simply reuse |bind| to recover a
%call-by-need semantics.
%The |Event| type needs semantics- and use-case-specific adjustment, though.}

Here is an example evaluating $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$, starting
in an empty \hypertarget{ex:eval-need-trace2}{heap}:

< ghci> evalNeed (read "let i = (λy.λx.x) i in i i") emp emp :: T (Value _, Heap _)
$\perform{evalNeed (read "let i = (λy.λx.x) i in i i") emp emp :: T (Value _, Heap _)}$
\\[\belowdisplayskip]
\noindent
This trace is in clear correspondence to the earlier by-need LK trace
\labelcref{ex:trace2}.
We can observe memoisation at play:
Between the first bracket of $\LookupT$ and $\UpdateT$ events, the heap entry
for $i$ goes through a beta reduction before producing a value.
This work is cached, so that the second $\LookupT$ bracket does not do any beta
reduction.

\begin{toappendix}
\label{sec:more-eval-strat}

To show that our denotational interpreter pattern equally well applies to
by-value evaluation strategies, we introduce three more concrete semantic domain
instances for call-by-value in this section.
The first one is a plain old by-value encoding the representation of which is
isomorphic to |D T|, just like for |DName|.
However, this instance is partial for the original recursive |Let| construct.
Our second instance augments call-by-value with a lazy initialisation
technique~\citep{Nakata:06} involving a mutable heap, thus sharing its
representation with |D (ByNeed T)|.
The third and final by-value domain models clairvoyant
call-by-value~\citep{HackettHutton:19}, which unfortunately proves to be partial
as well.

\subsection{Call-by-value}

\begin{figure}
\begin{code}
evalValue e ρ = eval e ρ :: D (ByValue T)

newtype ByValue τ v = ByValue { unByValue :: τ v }
ifPoly(instance Monad τ => Monad (ByValue τ) where ...)
instance Trace (τ v) => Trace (ByValue τ v) where {-" ... \iffalse "-}
  step e (ByValue τ) = ByValue (step e τ) {-" \fi "-}

class Extract τ where getValue :: τ v -> v
instance Extract T where getValue (Ret v) = v; getValue (Step _ τ) = getValue τ

instance (Trace (D (ByValue τ)), Monad τ, Extract τ) => HasBind (D (ByValue τ)) where
  bind # rhs body = step Let0 (do  let  d = rhs (return v)          :: D (ByValue τ)
                                        v = getValue (unByValue d)  :: Value (ByValue τ)
                                   v1 <- d; body (return v1))
\end{code}
%if style == newcode
\begin{code}
deriving instance Functor τ     => Functor (ByValue τ)
deriving instance Applicative τ => Applicative (ByValue τ)
deriving instance Monad τ       => Monad (ByValue τ)
\end{code}
%endif
\\[-1em]
\caption{Call-by-value }
\label{fig:by-value}
\end{figure}

Call-by-value eagerly evaluates a let-bound RHS and then substitutes its
\emph{value}, rather than the reduction trace that led to the value, into every
use site.

The call-by-value evaluation strategy is implemented with the |ByValue| trace transformer shown in \Cref{fig:by-value}.
Function |bind| defines a denotation |d :: D (ByValue τ)| of the right-hand
side by mutual recursion with |v :: Value (ByValue τ)| that we will discuss
shortly.

As its first action, |bind| yields a brand-new |Let0| event that we assume was
added to the definition of |Event|, announcing in the trace that the right-hand
side of a |Let| is to be evaluated.
Then monadic bind |v1 <- d; body (return v1)| yields steps from the right-hand
side |d| until its value |v1 :: Value (ByValue τ)| is reached, which is then
passed |return|ed (\ie wrapped in |Ret|) to the let |body|.
Note that the steps in |d| are yielded \emph{eagerly}, and only once, rather
than duplicating the trace at every use site in |body|, as the by-name form
|body d| would.

To understand the recursive definition of the denotation of the right-hand side |d|
and its value |v|,
consider the case |τ = T|.
Then |return = Ret| and we get |d = rhs (Ret v)| for the value |v| at the end of
the trace |d|, as computed by the type class instance method |getValue :: T v ->
v|.
%\footnote{The keen reader may have noted that we could use |Extract| to define a
%|MonadFix| instance for deterministic |τ|.}
The effect of |Ret (getValue (unByValue d))| is that of stripping all |Step|s from |d|.%
%\footnote{We could have defined |d| as one big guarded fixpoint |fix (rhs .
%return . getValue . unByValue)|, but some co-authors prefer to see the expanded
%form.}
%\sg{Is |let d = rhs (strip d); strip = return . getValue . unByValue in ...|
%perhaps a more intuitive decomposition than |d|/|v|? Simon?}

Since nothing about |getValue| is particularly special to |T|, it lives in its
own type class |Extract| so that we get a |HasBind| instance for different
types of |Trace|s, such as more abstract ones in \Cref{sec:abstraction}.

Let us trace $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$ for call-by-value:

< ghci> evalValue (read "let i = (λy.λx.x) i in i i") emp
$\perform{evalValue (read "let i = (λy.λx.x) i in i i") emp}$
\\[\belowdisplayskip]
\noindent
The beta reduction of $(\Lam{y}{\Lam{x}{x}})~i$ now happens once within the
$\LetOT$/$\LetIT$ bracket; the two subsequent $\LookupT$ events immediately halt
with a value.

Alas, this model of call-by-value does not yield a total interpreter!
Consider the case when the right-hand side accesses its value before yielding
one, \eg

< ghci> takeT 5 $ evalValue (read "let x = x in x x") emp
$\LetOT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\LetIT\xhookrightarrow{\hspace{1.1ex}}\AppIT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\texttt{\textasciicircum{}CInterrupted}$
\\[\belowdisplayskip]
\noindent
This loops forever unproductively, rendering the interpreter unfit as a
denotational semantics.

\begin{figure}
\begin{code}
evalVInit e ρ μ = unByVInit (eval e ρ :: D (ByVInit T)) μ

newtype ByVInit τ v = ByVInit { unByVInit :: Heap (ByVInit τ) -> τ (v, Heap (ByVInit τ)) }
instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByVInit τ)) where
  bind # rhs body = do  μ <- getV
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

\subsection{Lazy Initialisation and Black-holing}
\label{sec:lazy-init}

%\sven{Why do you discuss this after call-by-need? The storyline would be more cohesive if this subsection would appear directly after call-by-value.}
Recall that our simple |ByValue| transformer above yields a potentially looping
interpreter.
Typical strict languages work around this issue in either of two ways:
They enforce termination of the RHS statically (OCaml, ML), or they use
\emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
We recover a total interpreter using the semantics in \citet{Nakata:10},
building on the same encoding as |ByNeed| and initialising the heap with a
\emph{black hole}~\citep{stg} |stuck| in |bind| as in \Cref{fig:by-value-init}.

< ghci> evalVInit (read "let x = x in x x") emp emp :: T (Value _, Heap _)
$\perform{evalVInit (read "let x = x in x x") emp emp :: T (Value _, Heap _)}$


\begin{figure}
\begin{spec}
evalClair e ρ = runClair $ eval e ρ :: T (Value (Clairvoyant T))

data Fork f a = Empty | Single a | Fork (f a) (f a); data ParT m a = ParT (m (Fork (ParT m) a))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty); l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant (ParT τ a)
runClair :: D (Clairvoyant T) -> T (Value (Clairvoyant T))

instance (Extract τ, Monad τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind # rhs body = Clairvoyant (skip <|> let') >>= body
    where  skip = return (Clairvoyant empty)
           let' = fmap return $ step Let0 $ ... ^^ fix ... rhs ... getValue ...
\end{spec}
%if style == newcode
\begin{code}
evalClair e ρ = runClair $ eval e ρ :: T (Value (Clairvoyant T))

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
parFix f = ParT $ fix (unParT . f . getValue) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork _ _ -> pure (Fork (parFix (leftT . f)) (parFix (rightT . f)))

instance (Extract τ, Monad τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind _ rhs body = Clairvoyant (skip <|> let') >>= body
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
      Fork l r -> case getValue (go l) of
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

\subsection{Clairvoyant Call-by-value}
\label{sec:clair}

Clairvoyant call-by-value~\citep{HackettHutton:19} is an alternative to
call-by-need semantics that exploits non-determinism and a cost model to absolve
of the heap.
We can instantiate our interpreter to generate the shortest clairvoyant
call-by-value trace as well, as sketched out in \Cref{fig:clairvoyant-by-value}.
Doing so yields an evaluation strategy that either skips or speculates let
bindings, depending on whether or not the binding is needed:

< ghci> evalClair (read "let f = λx.x in let g = λy.f in g") emp :: T (Value (Clairvoyant T))
$\perform{evalClair (read "let f = λx.x in let g = λy.f in g") emp :: T (Value (Clairvoyant T))}$

< ghci> evalClair (read "let f = λx.x in let g = λy.f in g g") emp :: T (Value (Clairvoyant T))
$\perform{evalClair (read "let f = λx.x in let g = λy.f in g g") emp :: T (Value (Clairvoyant T))}$
\\[\belowdisplayskip]
\noindent
The first example discards $f$, but the second needs it, so the trace starts
with an additional $\LetOT$ event.
Similar to |ByValue|, the interpreter is not total so it is unfit as a
denotational semantics without a complicated domain theoretic judgment.
Furthermore, the decision whether or not a $\LetOT$ step is needed can be
delayed for an infinite amount of time, as exemplified by

< ghci> evalClair (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))
%$\perform{evalClair (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))}$
\texttt{\textasciicircum{}CInterrupted}
\\[\belowdisplayskip]
\noindent
The program diverges without producing even a prefix of a trace because the
binding for $i$ might be needed at an unknown point in the future
(a \emph{liveness property} and hence impossible to verify at runtime).
This renders Clairvoyant call-by-value inadequate for verifying properties of
infinite executions.
\end{toappendix}

The examples so far suggest that |evalNeed2| agrees with the LK machine on
\emph{many} programs.
The next section proves that |evalNeed2| agrees with the LK machine on
\emph{all} programs, including ones that diverge.
