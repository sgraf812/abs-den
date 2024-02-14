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
\emph{summary-based} static analysis such as usage analysis in
\Cref{sec:abstraction} can be derived as an \emph{abstract interpretation}.
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
For concise notation, we will use a small number of infix operators:
|(:->)| as a synonym for finite |Map|s, with |m ! x| for
looking up |x| in |m|, |ext m x d| for updates, |f << m| for mapping |f| over
every element of |m|, |assocs m| for turning |m| into a list of key-value pairs,
|dom m| for returning the set of keys present in the map, and |(`elem`)| for
membership tests in that set. \slpj{can we use a noisier notation like $a \mapsto b$}
\sg{Noisier notation for what? You mean something like $[a ↦ v] ∈ m$?
I suppose that could be syntactic sugar for |Just v <- Map.lookup x m|, yes.
But that won't help for uses such as |all (`elem` dom ρ) xs|, so I'm not convinced
its useful to introduce yet another way to access maps.}
\slpj{No: I mean the notation for the \emph{type constructor}.  As you have it, it's
an arrow that looks very very like ordinary function arrow.  In actual Haskell I might
write `type a :-> b = Map a b`, so that the tyep constructor `:->` is more visually
different to `->`.  If I was writing the paper I'd definitely use `Map`, but I yield to you on that!}

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

In traditional denotational semantics, the semantic domain |D| comprises
\emph{semantic values} such as base values (integers, strings, etc.) and
functions |D -> D|.
A distinctive feature of our work is that our semantic domain are instead
\emph{traces}
that describe
% , in as much or as little detail as desired,
the \emph{steps} taken
by an abstract machine, and that \emph{end} in these semantic values.
For example, we can choose a semantic domain |DName|, so that |eval|
will produce precisely the traces of the by-name variant of the Krivine machine in
\Cref{fig:lk-semantics}.
In \Cref{sec:evaluation-strategies} we will give semantic domains for by-value
and by-need semantics as well, and in \Cref{sec:abstraction} we obtain static
analyses as instances.

We can define the semantic domain |DName| for a call-by-name variant
of our language as follows:%
\footnote{For a realistic implementation, we would define |D| as a data
type to keep type class resolution decidable and non-overlapping.
We will however stick to a |type| synonym in this presentation in order to elide
noisy wrapping and unwrapping of constructors.}

\begin{minipage}{0.62\textwidth}
\begin{code}
type D τ = τ (Value τ);   type DName = D T
data T v = Step Event (T v) | Ret v
data Event  =  Lookup Name | Update | App1 | App2
            |  Let1 | Case1 | Case2 {-"\iffalse"-} | Let0{-"\fi"-}
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
A trace |T| can either |Ret|urn or it can make a |Step|, indicating that the
program makes another small-step transition before reaching a terminal state.
So every value in |DName| corresponds to a \emph{program trace} |T| that ends with a
concrete, semantic |Value|.

Each |Step| is decorated with an |Event|, which describes what happpens
in that |Step|; for example, a |Lookup| event describes a lookup in the
environment, and we further decorate it with the |Name| of the let-bound
variable for later scrutinisation in \Cref{sec:abstraction}.
Note that the choice of |Event| suggests a spectrum of intensionality,
with |data Event = Unit| corresponding to the ``delay monad'' popularised by
\citet{Capretta:05} on the more abstract end of the spectrum and arbitrary
syntactic detail attached to each of |Event|'s constructors at the intensional
end of the spectrum.%
\footnote{If our language had facilities for input/output and more general
side-effects, we could have started from a more elaborate trace construction
such as (guarded) interaction trees~\citep{interaction-trees,gitrees}.}

The coinductive nature of |T|'s definition in Haskell is crucial to our
approach\footnote{In a strict language, we would have introduced a thunk in
the definition of |Step|, \eg, @Step of event * (unit -> 'a t)@.
}, because diverging traces can be expressed as an infinite, but productive,
nesting of |Step|s.
The |Monad| instance of |T| implements the monadic bind operator |(>>=)| by
forwarding |Step|s, thus guarding the recursion~\citep{Capretta:05}.

A domain element |DName| is a trace that eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |DName| to yield another
|DName|, or a |Con|structor application giving the denotations of its fields.
|Value| is thus just a standard denotational encoding of its syntactic
counterpart |Lam|/|ConApp|, devoid of any syntax. \slpj{I don't know what that
sentence adds or even means. Omit?}
\sg{I clarified, mentioining |Lam|/|ConApp|. This point is one of the main
distinctions between operational semantics and denotational semantics.}
\slpj{I still don't know what ``devoid of syntax'' means.  Omit?}
(We postpone worries about well-definedness and totality to \Cref{sec:adequacy}.)

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
  bind rhs body = body (fix rhs))
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

It is clear that we want to vary the semantic domain quite a bit, so it
is natural to use type-class overloading to
allow the semantic
function |eval| to abstract over the particular domain, thus:
\[
|eval  ::  (Trace d, Domain d, HasBind d) =>  Exp -> (Name :-> d) -> d|
\]
We have parameterised the semantic domain |d| over three type classes |Trace|,
|Domain| and |HasBind|, whose signatures are given in \Cref{fig:trace-classes}.%
\footnote{One can think of these type classes as a fold-like final
encoding~\citep{Carette:07} of a domain.
However, the significance is in the \emph{decomposition} of the domain, not the
choice of encoding.}
Each of the three type classes offer knobs that we will tweak individually in
later Sections.

\Cref{fig:eval} gives the complete definition of |eval|.
It also gives type class instances for the particular domain |DName| that we
introduced in \Cref{sec:dna}.
Together this is enough to actually run the denotational interpreter to produce
traces.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:%
\footnote{We use |read :: String -> Exp| as a parsing function, and a |Show| instance
for |T (Value T)| that displays traces.}

< ghci> eval (read "let i = λx.x in i i") emp :: DName
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$,
\\[\belowdisplayskip]
\noindent
where $\langle\lambda\rangle$ means that the trace ends in a |Fun| value. This is
in direct correspondence to the earlier call-by-name small-step trace
\labelcref{ex:trace} in \Cref{sec:op-sem}.

The definition of |eval|, given in \Cref{fig:eval}, is by structural recursion over the input expression.
For example, to get the denotation of |Lam x body|, we must recursively invoke
|eval| on |body|, extending the environment to bind |x| to its denotation.
We wrap that body denotation in |step App2|, to prefix the trace of |body| with
an |App2| event whenever the function is invoked, where |step| is a method of class |Trace|.
Finally, we use |fun| to build the returned denotation; the details necessarily
depend on the |Domain|, so |fun| is a method of class |Domain|.
The lambda-bound |x::Name| passed to |fun| is ignored in the concrete by-name
semantics, as you can see in |Domain| instance for |DName| in \Cref{fig:trace-instances}.
As well it should: it is syntax, after all!
However, in \Cref{sec:abstraction} we will need |x|, much as
$\mathit{fun}_\px$ needed $\px$ in \Cref{fig:absence}.

The other cases follow a similar pattern; they each do some work, before handing off to
type class methods to do the domain-specific work.
As we shall see, we can reuse this single definition of |eval| with a variety of
different types to instantiate the semantic domain |d|.

The |HasBind| type class is particularly significant,
because it fixes a particular \emph{evaluation strategy}, as we shall see in
\Cref{sec:evaluation-strategies}.
The |bind| method of |HasBind| is used to give meaning to recursive let
bindings:
it takes two functionals
for building the denotation of the right-hand side and that of the let body,
given a denotation for the right-hand side.
The concrete implementation for |bind| given in \Cref{fig:trace-instances} simply
hands over the (guarded) fixpoint of the right-hand side to the body, yielding a
call-by-name evaluation strategy.
We will shortly see examples of eager evaluation strategies that will yield from
|fix rhs| inside |bind| instead of calling |body| immediately.
\slpj{But where is |fix| defined?}

We conclude this subsection with a few examples.
We will start with two programs that diverge.
The lazy |step| implementation means that the interpreter does \emph{not} diverge;
rather, it produces an infinite trace.  To display these traces we
use a function |takeT :: Int -> T v -> T (Maybe v)| to truncate them:
|takeT n τ| returns the first |n| steps of |τ| and replaces the final value
with |Nothing| (printed as $\bot$) if it goes on for longer.
\slpj{Should this not be |:: T (Maybe (Value T))| below?}

< ghci> takeT 5 $ eval (read "let x = x in x") emp :: T (Maybe Value)
$\perform{takeName 5 $ eval (read "let x = x in x") emp :: T (Maybe (Value (ByName T)))}$

< ghci> takeT 9 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe Value)
$\perform{takeName 9 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe (Value (ByName T)))}$
\\[\belowdisplayskip]
\noindent
Data types work as well, allowing for interesting ways (type errors) to get
|Stuck| (printed as $\lightning$):

< ghci> eval (read "let zro = Z() in let one = S(zro) in case one of { S(z) -> z }") emp :: DName
$\perform{eval (read "let zro = Z() in let one = S(zro) in case one of { S(zz) -> zz }") emp :: D (ByName T)}$

< ghci> eval (read "let zro = Z() in zro zro") emp :: DName
$\perform{eval (read "let zro = Z() in zro zro") emp :: D (ByName T)}$
\\
\slpj{What is the |...| in the first of these two examples?}

\subsection{More Evaluation Strategies}
\label{sec:evaluation-strategies}

By varying the |HasBind| instance of our type |D|, we can endow our language
|Exp| with different evaluation strategies.
Following a similar approach as~\citet{adi}, we maximise reuse by instantiating
the same |D| at different wrappers of |T|, rather than reinventing |Value| and |T|.

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
  bind rhs body = body (fix rhs)
\end{code}%
%endif
\\[-1em]
\caption{Redefinition of call-by-name semantics from \Cref{fig:trace-instances}}
\label{fig:by-name}
\end{figure}

\subsubsection{Call-by-name}

We redefine by-name semantics via the |ByName| \emph{trace transformer}
in \Cref{fig:by-name},%
\footnote{The Supplement defines these datatypes as |newtype|s.}
so called because |ByName τ| inherits its |Monad| and |Trace|
instance from |τ| (busywork we omit) and reminiscent of \citet{Darais:15}.
Our old |DName| can be recovered as |D (ByName T)|.

\begin{figure}
\begin{spec}
data ByValue τ v = ByValue { unByValue :: τ v }; data Event = ... | Let0
instance Monad τ => Monad (ByValue τ) where ...
instance Trace (τ v) => Trace (ByValue τ v) where ...

class Extract τ where extract :: τ v -> v
instance Extract T where extract (Ret v) = v; extract (Step _ τ) = extract τ

instance (Trace (D (ByValue τ)), Monad τ, Extract τ) => HasBind (D (ByValue τ)) where
  bind rhs body = step Let0 (fix (rhs . return . extract . unByValue) >>= body . return)
\end{spec}
%if style == newcode
\begin{code}
newtype ByValue τ v = ByValue { unByValue :: τ v }
  deriving (Functor,Applicative,Monad)
instance Trace (τ v) => Trace (ByValue τ v) where
  step e (ByValue τ) = ByValue (step e τ)
class Extract τ where extract :: τ v -> v
instance Extract T where extract (Ret v) = v; extract (Step _ τ) = extract τ
instance (Trace (D (ByValue τ)), Monad τ, Extract τ) => HasBind (D (ByValue τ)) where
  bind rhs body = step Let0 (fix (rhs . return . extract . unByValue) >>= body . return)
\end{code}
%endif
\\[-1em]
\caption{Call-by-value}
\label{fig:by-value}
\end{figure}

\subsubsection{Call-by-value}

Call-by-value eagerly traces evaluation of a let-bound RHS to substitute its
\emph{value}, rather than the complete trace that led to the value, into every
use site. \slpj{I could not follow this sentence.}

Our |ByValue| trace transfomer \Cref{fig:by-value} achieves this quite literally.
Let us unpack the definition of |bind|.
As its first action, it yields a brand new |Let0| event, indicating in the
trace that focus descends into the right-hand side of a |let|.
Then |>>=| will keep yielding from the |fix| expression corresponding to the RHS
until it is evaluated, and the value |v| is then passed |return|ed (\ie, wrapped
in |Ret|) to |body|.

The |τ >>= body . return| idiom is quite important, as it yields from the trace
|τ| eagerly, and only once, rather than duplicating it at every use site in
|body|, as |body τ| would.
The |fix| expression, on the other hand, expresses the following recursion equation:
|rhs τ| ends in the value |v| if and only if |τ| is |Ret v|.
The type class instance method |extract :: T v -> v| applied to |rhs τ| will
return |v|,%
\footnote{The keen reader may have noted that we could use |Extract| to define a
|MonadFix| instance for deterministic |τ|.}
and |return v = Ret v|, so |fix| solves this recursion equation for us.

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
denotational semantics. \slpj{Forward ref to where we handle this?}

\begin{figure}
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
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
\footnote{Indeed, we derive its monad instance |via State (Heap (ByNeed τ))
τ|~\citep{Blondal:18}.}
whose key operations |getN| and |putN| are given in \Cref{fig:by-need}.

|ByNeed τ| is best thought of as an answer to the request ``give me a |θ| such
that |D θ| models stateful computations in |D θ|''.
More formally, |θ := ByNeed τ| satisfies the recursion equation
$|(Heap θ -> τ (Value θ, Heap θ))| \cong |D θ|$ via |ByNeed| and its inverse
|unByNeed|.

So the denotation of an expression is no longer a trace, but rather a
\emph{stateful function returning a trace}, where the carried state
|Heap (ByNeed τ)| implements the heap in which call-by-need thunks are
allocated.
The |Trace| instance of |ByNeed τ| simply forwards to that of |τ| (\ie, often
|T|), pointwise over heaps.
Doing so needs a |Trace| instance for |τ (Value (ByNeed τ), Heap (ByNeed τ))|, but we
found it more succinct to use a quantified constraint |(forall v. Trace (τ
v))|, that is, we require a |Trace (τ v)| instance for every choice of |v|.
Given that |τ| must also be a |Monad|, that is not an onerous requirement.

The key part is again the implementation of |HasBind| for |D (ByNeed τ)|,
because that is the only place where thunks are allocated.
The implemention of |bind| designates a fresh heap address |a|
to hold the denotation of the right-hand side.
Both |rhs| and |body| are called with |fetchN a|, a denotation that looks up |a|
in the heap and runs it.
If we were to omit the |memo a| action explained next, we would thus have
recovered another form of call-by-name semantics based on mutable state instead
of guarded |fix|points.
The whole purpose of the |memo a d| combinator then is to \emph{memoise} the
computation of |d| the first time we run the computation, via |fetchN a| in the
|Var| case of |eval|.
So |memo a d| yields from |d| until it has reached a value, and then |upd|ates
the heap after an additional |Update| step.
Repeated access to the same variable will run the replacement |memo a (return
v)|, which immediately yields |v| after performing an |step Update| that does
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
the main |eval| function at all.%
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
