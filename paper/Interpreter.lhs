%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures
% Need the -XPartialTypeSignatures for the CbNeed example, for some weird reason
%include custom.fmt
%if style == newcode
\begin{code}
{-# LANGUAGE DerivingStrategies #-}
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
--   show (collect -> (es, a)) = case es of
--     [] -> "\\langle "++show a++"\\rangle "
--     _  -> "\\smallstep" ++ showListWith shows es [] ++ "\\langle "++show a++"\\rangle "
-- collect (Step e (collect -> (es,a))) = (e:es,a)
-- collect (Ret a)                      = ([],a)
instance Show (Value τ) where
  show (Fun _) = "\\lambda"
  show (Con k _) = "Con(" ++ show k ++ ",...)"
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

Now we get to the main contribution of this work, namely
a \emph{compositional semantics} for a functional language, the semantic
domain of which can express sufficient \emph{operational detail} such that a
\emph{summary-based} static analysis such as usage analysis can be derived as an
\emph{abstract interpretation}.
Following~\citet{Might:10}, we call this semantics a \emph{Denotational
Interpreter} because it qualifies both as a denotational
semantics~\citep{ScottStrachey:71} as well as a total definitional
interpreter~\citep{Reynolds:72}.
Such an interpreter can be implemented in any higher-order language such as
OCaml, Scheme or Java with explicit thunks,
% @fun () -> _@
but we picked Haskell
for convenience.%
\footnote{We extract from this document a runnable Haskell file which we add as
a Supplement, containing the complete definitions.
Furthermore, the (terminating) interpreter outputs are directly generated from
this extract.}

Recall that a denotational semantics is expressed as a mathematical
function |eval :: Exp -> (Name :-> D) -> D|.
The expression |eval e ρ| takes an expression |e| and returns its meaning, or \emph{denotation}, in
some \emph{semantic domain} |D|.
The environment |ρ| gives meaning to the free variables of |e|, by mapping each free variable to
its denotation in |D|.
We sketch the Haskell encoding of syntax in \Cref{fig:syntax} and the API of
environments and sets in \Cref{fig:map}.

\begin{figure}
\begin{minipage}{0.49\textwidth}
\begin{spec}
type Name = String
data Tag = ...; conArity :: Tag -> Int
data Exp
  =  Var Name | Let Name Exp Exp
  |  Lam Name Exp | App Exp Name
  |  ConApp Tag [Name] | Case Exp Alts
type Alts = Tag :-> ([Name],Exp)
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
\end{code}
%endif
\caption{Environments}
\label{fig:map}
\end{minipage}
\end{figure}

\subsection{Semantic Domain} \label{sec:dna}

In traditional denotational semantics, the semantic domain |D| is typically
an algebraic domain, embedding \emph{semantic values} such as base values
(integers, strings, etc) and functions |D -> D|.
A distinctive feature of this paper is that \emph{our semantic domain are traces}
that describe, in as much or as little detail as desired, the execution of an
abstract machine, and that \emph{end} in these semantic values.
For example, we can choose a semantic domain |DName|, so that |eval|
will produce precisely the traces of the by-name variant of the Krivine machine in
\Cref{fig:lk-semantics}!
In \Cref{sec:evaluation-strategies} we will give semantic domains for by-value
and by-need semantics as well, and in \Cref{sec:abstractions} we obtain static
analyses as instances.

Here are the data type declarations for |DName|, the by-name variant:

\begin{minipage}{0.65\textwidth}
%if style == newcode
\begin{code}
type D τ = τ (Value τ)
data T a = Step Event (T a) | Ret a
data Event  =  Lookup Name | Update | App1 | App2
            |  Let1 | Case1 | Case2 | Let0
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{code}
%endif
\begin{spec}
type DName = T Value
data T a = Step Event (T a) | Ret a
data Event  =  Lookup Name | Update | App1 | App2
            |  Let1 | Case1 | Case2
data Value = Stuck | Fun (DName -> DName) | Con Tag [DName]
\end{spec}
\end{minipage}
\begin{minipage}{0.35\textwidth}
\begin{spec}
instance Monad T where
  return a = Ret a
  Ret a >>= k = k a
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
  Ret a >>= k = k a
  Step e τ >>= k = Step e (τ >>= k)
\end{code}
%endif
\end{minipage}
\noindent
A trace |T| can either |Ret|urn or it can make a |Step|, indicating that the
program makes another small-step transition before reaching a terminal state.
So every value in |DName| corresponds to a \emph{program trace} |T| that ends with a
concrete, semantic |Value|.

We have embellished each |Step| with an |Event|, which describes what happpens
in that |Step|; for example, a |Lookup| event describes a lookup in environment, and
we further decorate it with the |Name| of the let-bound variable.
The reason for this decision will become clear in \Cref{sec:abstractions};
\slpj{What decision?}
just note that the choice of |Event| suggests a spectrum of intensionality,
with |data Event = Unit| corresponding to the ``delay monad'' popularised by
\citet{Capretta:05} on the more abstract end of the spectrum and arbitrary
syntactic detail attached to each of |Event|'s constructors at the intensional
end of the spectrum.
If our language had facilities for input/output and more general side-effects,
we could have started from a more elaborate construction such as (guarded)
interaction trees~\citep{interaction-trees,gitrees}.

The coinductive nature of |T|'s definition in Haskell is crucial to our
approach\footnote{In a strict language, we would have introduced a thunk in
the definition of |Step|, \eg, @Step of event * (unit -> 'a t)@.
}, because diverging traces can be expressed as an infinite, but productive,
nesting of |Step|s.
The |Monad| instance of |T| implements the monadic bind operator |(>>=)| by
forwarding |Step|s, thus guarding the recursion~\citep{Capretta:05}.

A domain element |DName| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |DName| to yield another
|DName|, or a |Con|structor application giving the denotations of its fields.
|Value| is thus just a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We postpone worries about well-definedness and totality to \Cref{sec:adequacy}.)

\begin{figure}
\begin{minipage}{0.55\textwidth}
\begin{code}
eval  ::  (Trace d, Domain d, HasBind d)
      =>  Exp -> (Name :-> d) -> d
eval e ρ = case e of
  Var x  | x ∈ dom ρ  -> ρ ! x
         | otherwise  -> stuck
  Lam x body -> fun {-" \iffalse "-}(label e){-" \fi "-} $ \d ->
    step App2 (eval body ((ext ρ x d)))
  App e x  | x ∈ dom ρ  -> step App1 $
               apply (eval e ρ) (ρ ! x)
           | otherwise  -> stuck
  Let x e1 e2 -> bind {-" \iffalse "-}x{-" \fi "-}
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
  fun :: {-" \iffalse "-}Label -> {-" \fi "-}(d -> d) -> d
  apply :: d -> d -> d
  con :: {-" \iffalse "-}Label -> {-" \fi "-}Tag -> [d] -> d
  select :: d -> (Tag :-> ([d] -> d)) ->  d

class HasBind d where
  bind :: {-" \iffalse "-}Name -> {-" \fi "-}(d -> d) -> (d -> d) -> d
\end{code}
\subcaption{Interface of traces and values}
  \label{fig:trace-classes}
\begin{code}
instance Trace (T v) where
  step = Step

instance ifCodeElse (Monad τ => Domain (D τ)) (Domain DName) where
  stuck = return Stuck
  fun {-" \iffalse "-}_{-" \fi "-} f = return (Fun f)
  apply  d a = d >>= \case
    Fun f -> f a; _ -> stuck
  con {-" \iffalse "-}_{-" \fi "-} k ds = return (Con k ds)
  select dv alts = dv >>= \case
    Con k ds | k ∈ dom alts  -> (alts ! k) ds
    _                        -> stuck

ifPoly (instance HasBind DName where
  bind rhs body = body (fix rhs))
\end{code}
\subcaption{Concrete by-name semantics for |DName|}
  \label{fig:trace-instances}
\end{minipage}%
\caption{Abstract Denotational Interpreter}
  \label{fig:eval}
\end{figure}

\subsection{The Interpreter}

It is clear that we want to vary the semantic domain quite a bit, so it
is natural to use type-class overloading to abstract over the semantic
function |eval| over the particular domain, thus:
\[
|eval  ::  (Trace d, Domain d, HasBind d) =>  Exp -> (Map Name d) -> d|
\]
We have parameterised the semantic domain |d| over three type classes,
classes |Trace|, |Domain| and |HasBind|, whose signatures are given in
\Cref{fig:trace-classes}.%
\footnote{One can think of these type classes as a final fold-like final
encoding~\citep{Carette:07} of a domain.
However, the significance is in \emph{what} is encoded, not in how.}
Each of the three type classes offer knobs that we will tweak individually in
later Sections.

\Cref{fig:eval} gives the complete definition of |eval|. \slpj{What is |<<|???}
It also gives
type-classes instances for the particular domain |DName| that we introduced
in \Cref{sec:dna}\slpj{Some instances are for |DName|, oathers for |Trace|.  Boo!!}.   Together this enough to actually run the denotational
interpreter to produce traces.
% The domain |DName| is encoded as an algebraic datatype, \ie, an \emph{initial}
% encoding.
% The interpreter |eval| in \Cref{fig:eval}, however, maps into a fold-like
%\emph{final encoding}~\citep{Carette:07} of a domain, \slpj{I don't understand the significance
%of this initia/final stufff.  Do we need it?}
%in terms of the three type
%classes |Trace|, |Domain| and |HasBind| depicted in \Cref{fig:trace-classes}.
%Thus, it is not the final \emph{structure} of the interpreter that is novel so
%much as the \emph{decomposition} of its semantic domain.
%
%Traces |T| and denotations |DName| are instances of these type classes via
% \Cref{fig:trace-instances}.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:%
\footnote{We use |read :: String -> Exp| as a parsing function.}

< ghci> eval (read "let i = λx.x in i i") emp :: DName
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$
\\[\belowdisplayskip]
\noindent
This trace is in direct correspondence to the call-by-name small-step trace \slpj{What "call-by-name small-step trace"? backward reference please}
\[\begin{array}{c}
  \arraycolsep2pt
  \begin{array}{clclcl}
             \multicolumn{2}{l}{(\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF)} & \smallstep[\LetIT] & (i~i, ρ_1, μ, \StopF)
             & \smallstep[\AppIT] & (i, ρ_1, μ, \ApplyF(\pa_1) \pushF \StopF)
             \\
  \smallstep[\LookupT] & (\Lam{x}{x}, ρ_1, μ, \ApplyF(\pa_1) \pushF \StopF) & \smallstep[\AppET] & (x, ρ_2, μ, \StopF) & \smallstep[\LookupT] & (\Lam{x}{x}, ρ_1, μ, \StopF)
  \end{array} \\
  \\[-0.5em]
  \quad \text{where} \quad \begin{array}{lll}
    ρ_1 = [i ↦ \pa_1] & ρ_2 = [i ↦ \pa_1, x ↦ \pa_1] & μ = [\pa_1 ↦ (ρ_1,\Lam{x}{x})]. \\
  \end{array}
\end{array}\]
\noindent
The definition of |eval| is easy to read.  For example, consider the |Lam| case.  To get the denotation of
|Lam x body|, we must recursively invoke |eval| on |body|, extending the environment to bind |x| to its
denotation.  We wrap that body in |step App2|, where |step :: Event -> d -> d|, to prefix the trace of |body| with
an |App2| event whenever the function is invoked.  Finally,
we use the type-class method |fun :: (d -> d) -> d| to build the returned denotation;
the details are bound to depend on |d|.

The other cases follow a similar pattern; they each do some work, before handing off to the
type-class methods for all the domain-specific functions.
As we shall see, we can re-use this single definition of |eval| with a variety of
different trace types to instantiate the semantics domain |d|.

The |HasBind| type class is particularly significant,
because it fixes a particular \emph{evaluation strategy}, as we shall see in
\Cref{sec:evaluation-strategies}.
The |bind| method of |HasBind| is used to give meaning to recursive let
bindings:
% fixpoint combinator |fix :: (a -> a) -> a|, but
it takes two functionals
for building the denotation of the right-hand side and that of the let body,
given a denotation for the right-hand side.
The concrete implementation for |DName| given in \Cref{fig:trace-instances} simply
hands over the fixpoint of the right-hand side to the body, yielding a
call-by-name evaluation strategy.
We will shortly see examples of eager evaluation strategies that will yield from
|fix rhs| inside |bind| instead of calling |body| immediately.

\slpj{I am doubtful that this paragraph adds anything.}
While the |step| method of |Trace| is exactly the final encoding of |Step|,
|Domain| is a bit of a mixture between |Value| and |DName = T Value| \slpj{I have no idea what this means}.
The method names of |Domain| bear resemblance to |Value|:
There are ``injections'' |fun|, |con| and |stuck| as well as ``eliminators''
|apply| and |select|.
The \emph{types} are wrong \slpj{what types}, though, with |DName| occurring where we would expect
|Value|.
We will revisit this curious generalisation in \Cref{sec:abstractions} where we
consider abstract interpretations that \emph{summarise} a |DName| in different waysa
depending on the |Domain| instance.  \slpj{Very obscure paragraph, no information conveyed.}

We conclude this Subsection with a few examples, starting with two programs that
diverge. The lazy |step| implementation allows us to observe finite prefixes of
the trace:\slpj{Need to give signature for |takeT| and explain}

< ghci> takeT 3 $ eval (read "let x = x in x") emp :: T (Maybe Value)
$\perform{takeName 3 $ eval (read "let x = x in x") emp :: T (Maybe (Value (ByName T)))}$

< ghci> takeT 3 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe Value)
$\perform{takeName 3 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe (Value (ByName T)))}$
\\[\belowdisplayskip]
\noindent
And data types work as well, allowing for interesting ways (type errors) to get
stuck:

< ghci> eval (read "let zero = Z() in let one = S(zero) in case one of { S(z) -> z }") emp :: DName
$\perform{eval (read "let zero = Z() in let one = S(zero) in case one of { S(zz) -> zz }") emp :: D (ByName T)}$

< ghci> eval (read "let zero = Z() in zero zero") emp :: DName
$\perform{eval (read "let zero = Z() in zero zero") emp :: D (ByName T)}$

\begin{figure}
\begin{spec}
data ByName τ v = ByName (τ v)
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
  bind _ rhs body = body (fix rhs)
\end{code}%
%endif
\caption{Redefinition of call-by-name semantics from \Cref{fig:trace-instances}}
\label{fig:by-name}
\end{figure}

\begin{figure}
\begin{spec}
-- State transformers (standard Haskell)
--   (StateT s m a) transforms monad m, by adding state s
get     :: Monad m => StateT s m s
modify  :: Monad m => (s -> s) -> StateT s m ()

-- The ByNeed trace transformer
data ByNeed τ v = ByNeed (StateT (Heap (ByNeed τ)) τ v)
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
runByNeed :: ByNeed τ a -> τ (a, Heap (ByNeed τ))
instance Monad τ => Monad (ByNeed τ) where ...
instance Trace (τ v) => Trace (ByNeed τ v) where ...

fetch :: Monad τ => Addr -> D (ByNeed τ); fetch a = ByNeed get >>= \μ -> μ ! a

memo :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memo a d = d >>= ByNeed . StateT . upd
  where  upd Stuck  μ = return (Stuck :: Value (ByNeed τ), μ)
         upd v      μ = step Update (return (v, ext μ a (memo a (return v))))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByNeed τ)) where
  bind rhs body = do  a <- ByNeed $ do { μ <- get; nextFree μ }
                      ByNeed $ modify (\μ -> ext μ a (memo a (rhs (fetch a))))
                      body (fetch a)
\end{spec}
%if style == newcode
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr

nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

newtype ByNeed τ v = ByNeed { unByNeed :: StateT (Heap (ByNeed τ)) τ v }
  deriving newtype (Functor,Applicative,Monad)

runByNeed :: ByNeed τ a -> τ (a, Heap (ByNeed τ))
runByNeed (ByNeed (StateT m)) = m emp

instance (forall v. Trace (τ v)) => Trace (ByNeed τ v) where
  step e (ByNeed (StateT m)) = ByNeed $ StateT $ \μ -> step e (m μ)

fetch :: Monad τ => Addr -> D (ByNeed τ)
fetch a = ByNeed get >>= \μ -> μ ! a

memo :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memo a d = d >>= ByNeed . StateT . upd
  where upd Stuck  μ = return (Stuck :: Value (ByNeed τ), μ)
        upd v      μ = step Update (return (v, ext μ a (memo a (return v))))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByNeed τ)) where
  bind _ rhs body = do  a <- nextFree <$> ByNeed get
                        ByNeed $ modify (\μ -> ext μ a (memo a (rhs (fetch a))))
                        body (fetch a)
\end{code}
%endif
\caption{Call-by-need}
\label{fig:by-need}
\end{figure}

\subsection{More Evaluation Strategies}
\label{sec:evaluation-strategies}

\slpj{What is |(!)| in Fig 7?  WHat is the arrow |:->|?}

By varying the |HasBind| instance of our type |DName|, we can endow our language
|Exp| with different evaluation strategies.
With a bit of generalisation, variations become as simple as switching out a
monad transformer, a common phenomenon in abstract definitional
interpreters~\citep{adi}.
In particular, we parameterise the definition of |DName| and |Value| over the particular
trace type |T|:%
\footnote{For a realistic implementation, we suggest to define |D| as a data
type to keep type class resolution decidable and non-overlapping.
We will however stick to a |type| synonym in this presentation in order to elide
noisy wrapping and unwrapping of constructors.}
\slpj{Is there really much wrapping and unwrapping? Other than in the monad instance.}
\begin{spec}
type D τ = τ (Value τ)
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
instance Monad τ => Domain (D τ) where ...
\end{spec}
\slpj{I wonder if we can just start with this generalisation directly.}

\noindent
\subsubsection{Call-by-name}

We redefine by-name semantics via the |ByName| \emph{trace transformer}
in \Cref{fig:by-name}%
\footnote{The Supplement defines these datatypes as |newtype|s.},
so called because |ByName τ| inherits its |Monad| and |Trace|
instance from |τ| (busywork we omit).
Our old |DName| can be recovered as |D (ByName T)|.

\slpj{Can we not recover by-name from |D T|?  That would be simpler}

\subsubsection{Call-by-need}

To get call-by-need, we use the semantic domain |D (ByNeed T)| (\Cref{fig:by-need}).
We can see that
\[
\begin{array}{ll}
|D (ByNeed T)| & \cong |ByNeed T (Value (ByNeed T)) | \\
  & \cong |StateT (Heap (ByNeed T)) T (Value (ByNeed T))|
\end{array}
\]
where |StateT| is the standard state transformer monad, whose key operations |get| and |modify| are
given in \Cref{fig:by-need}. So the denotation of
an expression is no longer a trace, but rather a \emph{stateful trace} in which the
carried state |Heap (ByNeed T)| implements the heap in which call-by-need thunks are
allocated.
The key part is the |HasBind| instance for |D (ByNeed T)|, which implements |letrec|,
the only place that a thunk is allocated in our little language.
The implementation of |bind| has three steps.
First uses the state monad to
allocates a fresh heap address |a|; we use |μ :: Heap (ByNeed T)| as the name of the heap.
Second, it uses |modify| to bind the address
|a| to something (itself a stateful trace) that we will look at next.
Finally it applies |body| to |(fetch a :: D (ByNeed T))|, a little
computation that looks up the address |a| in the current state of the heap, and
runs it.

In the second step we bind |a| to a stateful trace of type |D (ByNeed T)|.
The first time we run that computation (in the case for |Var|)
we want to evaluate the argument,
and update the heap to bind |a| to the value thus computed; this the essence of
lazy evaluation. \slpj{Need a bit more; I don't yet grok memo.}

% The trace transformer |ByNeed| in \Cref{fig:by-need} mixes in a call-by-need
% evaluation strategy by introducing a heap and memoisation to |τ|.
% Interestingly, |ByNeed T| denotes a \emph{stateful function returning a trace},
% thus it is the first time we compute with something different than a |T|.
% The |bind| implementation for |ByNeed| traces will tie the recursive knot with
% a |D| that |fetch|es the bound action from a heap, under an address |a| that is
% not taken yet in the current heap |μ|.
% This newly heap-bound |D| in turn evaluates |rhs|, the result of which is
% |memo|ised in an |Update| step, so that the heap-bound |D| is replaced by
% one that immediately |return|s the value.
% We will prove this semantics adequate \wrt to the LK transition system in
% \Cref{fig:lk-semantics} in \Cref{sec:adequacy}.

%\todo{Mention that we could also have tested this result, with a type like
%|type ValidateT τ = StateT σ τ|, where the |step| action crashes if the |Event|
%does not match the currently applicable LK transition for $σ$.}

Although the code is carefully written, it is worth stressing how
compact and expressive it is.  We were able to move from traces to stateful traces
just by wrapping traces |T| in a state transformer |StateT|, without modifying
the main |eval| function at all.
Furthermore, nothing in our approach is particularly specific to |Exp| or
|Value|!
We have built similar interpreters for PCF, where the @rec@, @let@ and
non-atomic argument constructs can simply reuse |bind| to recover a
call-by-need semantics.
(The |Event| type needs semantics- and use-case-specific adjustment, though.)

Here is an example evaluating $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$:

< ghci> runByNeed $ eval (read "let i = (λy.λx.x) i in i i") emp :: T (Value (ByNeed T), Heap _)
$\perform{runByNeed $ eval (read "let i = (λy.λx.x) i in i i") emp :: T (Value (ByNeed T), Heap _)}$
\\[\belowdisplayskip]
\noindent
We can observe memoisation at play:
Between the first bracket of $\LookupT$ and $\UpdateT$ events, the heap entry
for $i$ goes through a beta reduction before producing a value.
This work is cached, so that the second $\LookupT$ bracket does not do any beta
reduction.

Finally note that it would be very simple to suppress $\UpdateT$ events for
already evaluated heap bindings by tweaking |upd| to omit the |memo| wrapper,
\eg, |upd v μ = return (v, ext μ a (return v))|.
We decided against that because it obscures the simple correspondence to the LK
transition system.

\begin{figure}
\begin{spec}
instance MonadFix T where
  mfix f = fst $ fix (\(τ, v) -> go (f v)) where  go (Step e τ) | (τ', v) <- go τ  = (Step e τ', v)
                                                  go (Ret v)                       = (Ret v, v)

data ByValue τ v = ByValue { unByValue :: τ v }; data Event = ... | Let0

instance (Trace (D (ByValue τ)), MonadFix τ) => HasBind (D (ByValue τ)) where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = step Let0 (ByValue (mfix (unByValue . rhs . return))) >>= body . return
\end{spec}
%if style == newcode
\begin{code}
instance MonadFix T where
  mfix f = fst $ fix (go . f . snd) where  go (Step e τ) | (τ', v) <- go τ  = (Step e τ', v)
                                           go (Ret v)                       = (Ret v, v)

newtype ByValue τ v = ByValue { unByValue :: τ v }
  deriving (Functor,Applicative,Monad)
instance Trace (τ v) => Trace (ByValue τ v) where
  step e (ByValue τ) = ByValue (step e τ)

instance (Trace (D (ByValue τ)), MonadFix τ) => HasBind (D (ByValue τ)) where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = step Let0 (ByValue (mfix (unByValue . rhs . return))) >>= body . return
\end{code}
%endif
\caption{Call-by-value}
\label{fig:by-value}
\end{figure}

\begin{figure}
\begin{spec}
data ByVInit τ v = ByVInit (StateT (Heap (ByVInit τ)) τ v)
runByVInit :: Monad τ => ByVInit τ a -> τ (a, Heap (ByVInit τ))
instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByVInit τ)) where
  bind _ rhs body = do  a <- nextFree <$> ByVInit get
                        ByVInit $ modify (\μ -> ext μ a stuck)
                        step Let0 (memo a (rhs (fetch a))) >>= body . return
\end{spec}
%if style == newcode
\begin{code}
newtype ByVInit τ v = ByVInit (StateT (Heap (ByVInit τ)) τ v)
  deriving (Functor,Applicative,Monad)

runByVInit :: Monad τ => ByVInit τ a -> τ (a, Heap (ByVInit τ))
runByVInit (ByVInit m) = runStateT m emp

instance (forall v. Trace (τ v)) => Trace (ByVInit τ v) where
  step e (ByVInit (StateT m)) = ByVInit $ StateT $ \μ -> step e (m μ)

fetch' :: Monad τ => Addr -> D (ByVInit τ)
fetch' a = ByVInit get >>= \μ -> μ ! a

memo' :: forall τ. (Monad τ, forall v. Trace (τ v)) => Addr -> D (ByVInit τ) -> D (ByVInit τ)
memo' a d = d >>= ByVInit . StateT . upd
  where upd Stuck  μ = return (Stuck :: Value (ByVInit τ), μ)
        upd v      μ = return (v, ext μ a (return v))

instance (Monad τ, forall v. Trace (τ v)) => HasBind (D (ByVInit τ)) where
  bind _ rhs body = do  a <- nextFree <$> ByVInit get
                        ByVInit $ modify (\μ -> ext μ a stuck)
                        step Let0 (memo' a (rhs (fetch' a))) >>= body . return
\end{code}
%endif
\caption{Call-by-value with lazy initialisation}
\label{fig:by-value-init}
\end{figure}

\subsubsection{Call-by-value}

By defining a |MonadFix| instance for |T| and defining |bind| in terms
of this instance, we can give a by-value semantics to |Exp|, as shown in
\Cref{fig:by-value}.
\slpj{Gah!  Now I have to understand MonadFix!  Can't we just give a |HasBind| instance directly?
Indeed, isn't by-value a bit easier than by-need?  Your super-compact definitions just look like line noise to me.}
Let us unpack the definition of |bind|.
As its first action, it yields a brand new |Let0| event, indicating in the
trace that focus descends into the right-hand side of a |let|.
The definition of |mfix| on |T| then takes over;
producing a trace |τ| which ends in a |Ret v| after finitely many steps.
The value |v| is then passed to the argument |f| of |bind|, wrapped in a
|return|.
This procedure works as long as |f| does not scrutinise |v| before producing
the |Ret| constructor.
The effect is that the trace |τ| is yielded \emph{while executing |mfix|}, and
the value |v| is then passed |return|ed to |body|.
Notably, |body (step Let0 ...)| would have different semantics, deferring the
effect of evaluating |rhs| to its fixpoint at use sites; hence the
|(>>= body . return)| idiom that forces the effects (\eg, yields the trace) of
its argument eagerly.
Subsequent evaluations of |return v| will not have to yield the |Step|s of |τ|
again.

Let us trace $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$ for call-by-value:

< ghci> eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)
$\perform{eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)}$
\\[\belowdisplayskip]
\noindent
The beta reduction of $(\Lam{y}{\Lam{x}{x}})~i$ now happens once within the
$\LetOT$/$\LetIT$ bracket; the two subsequent $\LookupT$ events immediately halt
with a value.

\subsubsection{Lazy Initialisation and Black-holing}

Alas, this model of call-by-value does not yield a total interpreter!
Consider the case when the right-hand side accesses its value before yielding
one, \eg,

< ghci> takeT 5 $ eval (read "let x = x in x x") emp :: ByValue T (Maybe (Value (ByValue T)))
$\LetOT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\LetIT\xhookrightarrow{\hspace{1.1ex}}\AppIT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\texttt{\textasciicircum{}CInterrupted}$
\\[\belowdisplayskip]
\noindent
This loops forever unproductively, rendering the interpreter unfit as a
denotational semantics.
Typical strict languages work around this issue in either of two ways:
They enforce termination of the RHS statically (OCaml, ML), or they use
\emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
We could recover a total interpreter using the semantics in \citet{Nakata:10},
reusing the implementation from |ByNeed| and initialising the heap
with a \emph{black hole}~\citep{stg} |stuck| in |bind| as in
\Cref{fig:by-value-init}.

< ghci> runByVInit $ eval (read "let x = x in x x") emp :: T (Value (ByVInit T), Heap (ByVInit T))
$\perform{runByVInit $ eval (read "let x = x in x x") emp :: T (Value (ByVInit T), Heap (ByVInit T))}$


\begin{figure}
\begin{spec}
data Fork f a = Empty | Single a | Fork (f a) (f a); data ParT m a = ParT (m (Fork (ParT m) a))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty); l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant (ParT τ a)
runClair :: D (Clairvoyant T) -> T (Value (Clairvoyant T))

instance (MonadFix τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = Clairvoyant (skip <|> let') >>= body
    where  skip = return (Clairvoyant empty)
           let' = fmap return $ step Let0 $ ... ^^ mfix ... rhs . return ...
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

parFix :: MonadFix τ => (Fork (ParT τ) a -> ParT τ a) -> ParT τ a
parFix f = ParT $ mfix (unParT . f) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork _ _ -> pure (Fork (parFix (leftT . f)) (parFix (rightT . f)))

instance (MonadFix τ, forall v. Trace (τ v)) => HasBind (D (Clairvoyant τ)) where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = Clairvoyant (skip <|> let') >>= body
    where
      skip = return (Clairvoyant empty)
      let' = fmap return $ unClair $ step Let0 $ Clairvoyant $ parFix $ unClair . rhs . Clairvoyant . ParT . return

-- This is VERY weird
class Monad m => MonadRecord m where
  recordIfJust :: m (Maybe a) -> Maybe (m a)

instance MonadRecord T where
  recordIfJust (Ret Nothing) = Nothing
  recordIfJust (Ret (Just a)) = Just (Ret a)
  recordIfJust (Step e t) = Step e <$> (recordIfJust t)

headParT :: MonadRecord m => ParT m a -> m (Maybe a)
headParT m = go m
  where
    go :: MonadRecord m => ParT m a -> m (Maybe a)
    go (ParT m) = m >>= \case
      Empty    -> pure Nothing
      Single a -> pure (Just a)
      Fork l r -> case recordIfJust (go l) of
        Nothing -> go r
        Just m  -> Just <$> m

runClair :: MonadRecord τ => D (Clairvoyant τ) -> τ (Value (Clairvoyant τ))
runClair (Clairvoyant m) = headParT m >>= \case
  Nothing -> error "There should have been at least one Clairvoyant trace"
  Just t  -> pure t
\end{code}
%endif
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
A total description of the \emph{dynamic semantics} of a language requires a
coinductive domain.
For \emph{static analysis} we need to find good abstractions that approximate
the dynamics in an inductive domain.
We will now consider examples of such abstract, inductive domains.
