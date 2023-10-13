%options ghci -pgmL lhs2TeX -optL--pre
%if style == newcode
\begin{code}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Interpreter where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (find, foldl')
import Text.Show (showListWith)
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State
import Expr

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
  show Bind = "\\BindT"
  show Update = "\\UpdateT"
  show Let1 = "\\LetIT"
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "\\rightarrow" ++ show t
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
  show _ = show "\\wild"
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
  showsPrec _ = showListWith (\(k,v) -> showString k . showString "\\! \\mapsto \\! " . shows v) . Map.toList

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

We will now define a denotational interpreter in Haskell.
It is worth stressing that we picked Haskell out of convenience and familiarity,
rather than out of necessity:
We make use of thunks in only one key position where memoisation is not
important and could just as well have used a strict higher-order language such
as OCaml, ML or Scheme with explicit suspension @fun () -> _@.

\begin{figure}
\begin{spec}
type Name = String
data Tag = ...; conArity :: Tag -> Int
data Expr  = Var Name | App Expr Name | Lam Name Expr | Let Name Expr Expr
           | ConApp Tag [Name] | Case Expr [Alt]
type Alt = (Tag,[Name],Expr)
\end{spec}
\caption{Syntax}
\label{fig:syntax}
\end{figure}

\subsection{Semantic Domain}
A denotational interpreter is both a definitional interpreter as well as a
denotational semantics.
Then what is its \emph{semantic domain}?
To a first approximation, we can think of it as a type |D|, defined as
\begin{minipage}{0.65\textwidth}
%if style == newcode
\begin{code}
type D τ = τ (Value τ)
data T a = Step Event (T a) | Ret a
data Event  = Lookup Name | Update | App1 | App2
            | Bind | Case1 | Case2 | Let1
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{code}
%endif
\begin{spec}
type D = T Value
data T a = Step Event (T a) | Ret a
data Event  = Lookup Name | Update | App1 | App2
            | Bind | Case1 | Case2
data Value = Stuck | Fun (D -> D) | Con Tag [D]
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
Every such |D| corresponds to a program trace |T| that ends with a concrete
|Value|.
A trace |T| can either |Ret|urn or it can make another |Step|,
indicating that the program makes another small-step transition before reaching
a terminal state.

We embellished each |Step| with intensional information about the particular
type of small-step |Event|, for example we attach the |Name| of the let-bound
variable to |Lookup|.
The reason for this decision will become clear later on; just note that the
choice of |Event| suggests a spectrum of intensionality, with |data Event =
Unit| corresponding to the ``delay monad'' popularised by \citet{Capretta:05} on
the more abstract end of the spectrum and arbitrary syntactic detail attached to
each of |Event|'s constructors at the other end of the spectrum.
If our language had facilities for input/output, we could have started from a
more elaborate construction such as interaction trees~\citep{interaction-trees}.

The coinductive nature of |T|'s definition in Haskell is crucial to our
approach because it allows us to express diverging traces as an infinite,
productive nesting of |Step|s; in a strict language, we would have introduced
an explicit thunk in the definition of |Step|, \eg, @Step of event * (unit -> 'a t)@.
The |Monad| instance of |T| implements the bind operator |(>>=)| by forwarding
|Step|s, thus guarding the recursion~\citep{Capretta:05}.

A semantic element |D| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |D| to yield another
|D|, or a |Con|structor application giving the denotations of its fields.
|Value| is a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We postpone worries about well-definedness and totality to \Cref{sec:adequacy}.)

\begin{figure}
\begin{code}
type (:->) = Map
emp :: Ord k => k :-> v
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
exts :: Ord k => (k :-> v) -> [k] -> [v] -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
(∈) :: Name -> Set Name -> Bool
\end{code}
%if style == newcode
\begin{code}
emp = Map.empty
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl' (uncurry . ext) ρ (zip xs ds)
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
\end{code}
%endif
\caption{Environments}
\label{fig:map}
\end{figure}

\begin{figure}
\begin{minipage}{0.55\textwidth}
\begin{code}
eval  ::  (IsTrace τ, IsValue τ v, HasAlloc τ v)
      =>  Expr -> (Name :-> τ v) -> τ v
eval e ρ = case e of
  Var x    | x ∈ dom ρ  -> ρ ! x
           | otherwise  -> retStuck
  App e x  | x ∈ dom ρ  -> step App1 $ do
               v <- eval e ρ
               apply v (ρ ! x)
           | otherwise  -> retStuck
  Lam x e -> retFun {-" \iffalse "-}(label e){-" \fi "-} $ \d ->
    step App2 (eval e ((ext ρ x d)))
  Let x e1 e2 -> do
    d1 <- alloc (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
    step Bind (eval e2 (ext ρ x (step (Lookup x) d1)))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> retCon {-" \iffalse "-}(label e){-" \fi "-} k (map (ρ !) xs)
    | otherwise
    -> retStuck
  Case e alts -> step Case1 $ do
    v <- eval e ρ
    select v [ (k, cont er xs) | (k,xs,er) <- alts ]
    where
       cont er xs ds  |  length xs == length ds
                      =  step Case2 (eval er (exts ρ xs ds))
                      |  otherwise
                      =  retStuck
\end{code}
%  ConApp k xs  | all (∈ dom ρ) xs  -> retCon k (map (ρ !) xs)
%               | otherwise         -> retStuck
%  Case e alts -> step Case1 (eval e ρ >>= \v ->
%    select v [ (k, step Case2 . eval er . exts ρ xs) | (k,xs,er) <- alts ])
\end{minipage}%
\begin{minipage}{0.44\textwidth}
\begin{code}
class Monad τ => IsTrace τ where
  step :: Event -> τ v -> τ v

class IsValue τ v | v -> τ where
  retStuck :: τ v
  retFun :: {-" \iffalse "-}Label -> {-" \fi "-}(τ v -> τ v) -> τ v
  apply :: v -> τ v -> τ v
  retCon :: {-" \iffalse "-}Label -> {-" \fi "-}Tag -> [τ v] -> τ v
  select :: v -> [(Tag, [τ v] -> τ v)] ->  τ v

class HasAlloc τ v | v -> τ where
  alloc :: (τ v -> τ v) -> τ (τ v)
\end{code}
\subcaption{Final encoding of traces and values}
  \label{fig:trace-classes}
%if style /= newcode
\begin{code}
instance IsTrace T where
  step = Step

instance IsValue T Value where
  retStuck = return Stuck
  retFun {-" \iffalse "-}_{-" \fi "-} f = return (Fun f)
  retCon {-" \iffalse "-}_{-" \fi "-} k ds = return (Con k ds)
  apply  (Fun f)  d  = f d
  apply  _        _  = retStuck
  select v alts = ...

instance HasAlloc T Value where
  alloc f = return (fix f)
\end{code}
%else
\begin{code}
instance IsTrace T where
  step = Step

instance IsTrace τ => IsValue τ (Value τ) where
  retStuck = return Stuck
  retFun {-" \iffalse "-}_{-" \fi "-} f = return (Fun f)
  retCon {-" \iffalse "-}_{-" \fi "-} k ds = return (Con k ds)
  apply (Fun f) d = f d
  apply _       _ = retStuck
  select v alts
    | Con k ds <- v
    , Just (_,alt) <- find (\(k',_) -> k' == k) alts
    = alt ds
    | otherwise
    = retStuck
\end{code}
%endif
\subcaption{Concrete by-name semantics for |D|}
  \label{fig:trace-instances}
\end{minipage}%
\caption{Abstract Denotational Interpreter}
  \label{fig:eval}
\end{figure}

\subsection{The Interpreter}

We will now use |D| to give meaning to an expression |e| via an interpreter
function |eval :: Expr -> (Name :-> D) -> D|, where the variable environment
|Name :-> D| is a finite mapping from free variables of |e| to their meaning in
|D|.
We summarise the API of environments and sets in \Cref{fig:map}.

We give a definition for |eval| in \Cref{fig:eval}, although in the spirit of
abstract definitional interpreters such as in \citet{Keidel:18}, its type is
quite a bit more general than its instantiation at |D|.

In particular, the interpreter maps expressions not into a concrete,
\emph{initial} encoding of a trace as an algebraic data type, but into a
fold-like \emph{final encoding}~\citep{Carette:07} thereof, in terms
of three type classes |IsTrace|,|IsValue| and |HasAlloc| depicted in
\Cref{fig:trace-classes}.
%
%TODO: Related Work
%This approach evokes memories of~\citet{Carette:07} because we effectively
%encode expressions as a fold, but our semantic domain |D| of traces is quite
%different because it gives a proper account of diverging traces and is total.
%
Each of these offer knobs that we will tweak individually in later Sections.
|T|races and |Value|s are instances of these type classes via
\Cref{fig:trace-instances}, so |D| can stand in as a |τ v| for |eval|.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:%
\footnote{We use |read :: String -> Expr| as a parsing function.}

< ghci> eval (read "let i = λx.x in i i") emp :: D
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$
\\[\belowdisplayskip]
\noindent
Which is in direct correspondence to the call-by-name small-step trace
\[\begin{array}{c}
  \arraycolsep2pt
  \begin{array}{clclcl}
             & (\Let{i}{\Lam{x}{x}}{i~i}, [], [], \StopF) & \smallstep[\BindT] & (i~i, ρ_1, μ, \StopF)
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
While |IsTrace| is exactly a final encoding of |T|, |IsValue| is not quite the
same to |Value|:
For one, the ``injections'' |retStuck|, |retFun| and |retCon| return a
|D = T Value|, not simply a |Value|; a curiosity that we will revisit in
\Cref{fig:abstractions} when we consider abstract interpretations of |Value|
that don't necessarily instantiate these methods with |return . _|.
On the other hand, the ``eliminators'' |apply| and |select| can be implemented
in the obvious way for |T|.
The omitted definition for |select| finds the |alt| in |alts| that matches the
|Tag| of the |Con| value |v| and applies said |alt| to the field denotations of
|v|; failure to perform any of these steps results in |retStuck|.%
\footnote{We extract from this document a runnable Haskell file which we add as
a Supplement, containing the complete definitions.
Furthermore, the (non-diverging) interpreter outputs are directly generated from
this extract.}

The third type class is |HasAlloc|, a most significant knob to our
interpreter because it fixes a particular evaluation strategy.
We will play with this knob in \Cref{sec:evaluation-strategies}.
Like |IsValue|, it is parameterised both over the type of values
\emph{as well as} the type of trace, where the syntax | || v -> τ| is a
functional dependency indicating that the type of |v| completely determines |τ|.
In other words: The choice of value will always be specific to a particular type
of trace, the same way that |Value| hard-codes its use of |T|.

The |alloc| method of |HasAlloc| is used to give meaning to recursive let
bindings; as such its type is \emph{almost} an instance of the venerable least
fixpoint combinator |fix :: (a -> a) -> a|, if it weren't for the additional |τ|
wrapping in its result type.
The concrete implementation for |D| given in \Cref{fig:trace-instances} simply
defers to |fix|, yielding a call-by-name evaluation strategy.
We will shortly see examples of eager evaluation strategies that will make some
|step|s in |alloc| instead of simply |return|ing.

%TODO: Move to later section?
Evidently, |eval| is defined by recursion on the structure of |e|.
But every recursive call is also guarded by a call to |step|, so it also
corecursively generates what \Cref{sec:adequacy} will prove to be an adequate
proxy for a small-step trace.

We conclude this Subsection with a few examples, starting with two programs that
diverge. The corecursive formulation allows us to observe finite prefixes of the
trace:

< ghci> takeT 3 $ eval (read "let x = x in x") emp :: T (Maybe Value)
$\perform{takeName 3 $ eval (read "let x = x in x") emp :: T (Maybe (Value (ByName T)))}$

< ghci> takeT 3 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe Value)
$\perform{takeName 3 $ eval (read "let w = λy. y y in w w") emp :: T (Maybe (Value (ByName T)))}$
\\[\belowdisplayskip]
\noindent
And data types work as well, allowing for interesting ways (type errors) to get
stuck:

< ghci> eval (read "let zero = Z() in let one = S(zero) in case one of { S(z) -> z }") emp :: D
$\perform{eval (read "let zero = Z() in let one = S(zero) in case one of { S(zz) -> zz }") emp :: D (ByName T)}$

< ghci> eval (read "let zero = Z() in zero zero") emp :: D
$\perform{eval (read "let zero = Z() in zero zero") emp :: D (ByName T)}$

\begin{figure}
\begin{spec}
data ByName τ v = ByName (τ v)
instance Monad τ => Monad (ByName τ) where ...
instance IsTrace τ => IsTrace (ByName τ) where ...
instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = return (fix f)
\end{spec}
%if style == newcode
\begin{code}
newtype ByName τ v = ByName { unByName :: (τ v) }
  deriving newtype (Functor,Applicative,Monad)

instance IsTrace τ => IsTrace (ByName τ) where
  step e = ByName . step e . unByName

instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = return (fix f)
\end{code}
%endif
\caption{Call-by-name}
\label{fig:by-name}
\end{figure}

\begin{figure}
\begin{spec}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
data ByNeed τ v = ByNeed (StateT (Heap (ByNeed τ)) τ v)
runByNeed :: ByNeed τ a -> τ (a, Heap (ByNeed τ))
instance Monad τ => Monad (ByNeed τ) where ...

instance IsTrace τ => IsTrace (ByNeed τ) where
  step e (ByNeed (StateT m)) = ByNeed $ StateT $ \μ -> step e (m μ)

fetch :: Monad τ => Addr -> D (ByNeed τ)
fetch a = ByNeed get >>= \μ -> μ ! a

memo :: IsTrace τ => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memo a d = d >>= step Update . ByNeed . StateT . upd
  where upd v μ = return (v, ext μ a (memo a (return v)))

instance IsTrace τ => HasAlloc (ByNeed τ) (Value (ByNeed τ)) where
  alloc f = ByNeed $ StateT $ \μ -> do
    let a = nextFree μ
    return (fetch a, ext μ a (memo a (f (fetch a))))
\end{spec}
%if style == newcode
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr

nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

newtype ByNeed τ v = ByNeed (StateT (Heap (ByNeed τ)) τ v)
  deriving newtype (Functor,Applicative,Monad)

runByNeed :: ByNeed τ a -> τ (a, Heap (ByNeed τ))
runByNeed (ByNeed (StateT m)) = m emp

instance IsTrace τ => IsTrace (ByNeed τ) where
  step e (ByNeed (StateT m)) = ByNeed $ StateT $ \μ -> step e (m μ)

fetch :: Monad τ => Addr -> D (ByNeed τ)
fetch a = ByNeed get >>= \μ -> μ ! a

memo :: IsTrace τ => Addr -> D (ByNeed τ) -> D (ByNeed τ)
memo a d = d >>= step Update . ByNeed . StateT . upd
  where upd v μ = return (v, ext μ a (memo a (return v)))

instance IsTrace τ => HasAlloc (ByNeed τ) (Value (ByNeed τ)) where
  alloc f = ByNeed $ StateT $ \μ -> do
    let a = nextFree μ
    return (fetch a, ext μ a (memo a (f (fetch a))))
\end{code}
%endif
\caption{Call-by-need}
\label{fig:by-need}
\end{figure}

\subsection{More Evaluation Strategies}
\label{sec:evaluation-strategies}

By varying the |HasAlloc| instance of our type |D|, we can endow our language
|Expr| with different evaluation strategies.
With a bit of generalisation, variations become as simple as switching out a
monad transformer, a common phenomenon in abstract definitional
interpreters~\citep{adi}.
Thus we parameterise |D| and |Value| over the particular trace type |T|:
\begin{spec}
type D τ = τ (Value τ)
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
instance IsTrace τ => IsValue τ (Value τ) where ...
\end{spec}

\noindent
\subsubsection{Call-by-name}

We redefine by-name semantics via the |ByName| \emph{trace transformer}
in \Cref{fig:by-name}%
\footnote{The Supplement defines these datatypes as |newtype|s.},
so called because |ByName τ| inherits its |Monad| and |IsTrace|
instance from |τ| (busywork we omit).
Our old |D| can be recovered as |D (ByName T)|.

\subsubsection{Call-by-need}

The trace transformer |ByNeed| in \Cref{fig:by-need} mixes in a call-by-need
evaluation strategy by introducing a heap and memoisation to |τ|.
Interestingly, |ByNeed T| denotes a \emph{stateful function returning a trace},
thus it is the first time we compute with something different than a |T|.
The |alloc| implementation for |ByNeed| traces will return a |D| that |fetch|es
the bound action from a heap, under an address |a| that is not taken yet in the
current heap |μ|.
This newly heap-bound |D| in turn evaluates |f ...|, the result of which is
|memo|ised in an |Update| step, so that the heap-bound |D| is replaced by
one that immediately |return|s the value.
We have proven this semantics adequate \wrt to the LK transition system in
\Cref{fig:lk-semantics} with the techniques we develop in \Cref{sec:adequacy}.

\todo{Mention that we could also have tested this result, with a type like
|type ValidateT τ = StateT σ τ|, where the |step| action crashes if the |Event|
does not match the currently applicable LK transition for $σ$.}

It is worth stressing how simple it was to carry out this extension.
Furthermore, nothing here is specific to |Expr| or |Value|!
The only indirect requirement on |T| is that the |Event| type has an |Update|
action, which makes the implementation of |ByNeed| easily reusable.
\sg{That's not completely true; one would still need to duplicate the code to
adjust it to the particular |Event| data type.
That could be worked around with by parameterising |IsTrace τ ε| over the event
type and then have type class constraint |HasUpdateEvent ε| in |HasAlloc|,
but that seems like a lot complexity for such little benefit.
Perhaps retract on this claim before long.}

Example evaluating $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$:

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
transition system that we prove in \Cref{sec:adequacy}.

\begin{figure}
\begin{spec}
instance MonadFix T where
  mfix f = τ where  (τ,v) = go (f v)
                    go (Step e τ) | (τ', v) <- go τ  = (Step e τ', v)
                    go (Ret v)                       = (Ret v, v)

data Event = ... | Let1
data ByValue τ v = ByValue { unByValue :: τ v }

instance (IsTrace τ, MonadFix τ) => HasAlloc (ByValue τ) (Value (ByValue τ)) where
  alloc f = fmap return $ step Let1 $ ByValue $ mfix (unByValue . f . return)
\end{spec}
%if style == newcode
\begin{code}
instance MonadFix T where
  mfix f = τ where  (τ,v) = go (f v)
                    go (Step e τ) | (τ', v) <- go τ  = (Step e τ', v)
                    go (Ret v)                       = (Ret v, v)

newtype ByValue τ v = ByValue { unByValue :: τ v }
  deriving (Functor,Applicative,Monad)
instance IsTrace τ => IsTrace (ByValue τ) where
  step e (ByValue τ) = ByValue (step e τ)

instance (IsTrace τ, MonadFix τ) => HasAlloc (ByValue τ) (Value (ByValue τ)) where
  alloc f = fmap return $ step Let1 $ ByValue $ mfix (unByValue . f . return)
\end{code}
%endif
\caption{Call-by-value}
\label{fig:by-value}
\end{figure}

\begin{figure}
\begin{spec}
data ByVInit τ v = ByVInit (StateT (Heap (ByVInit τ)) τ v)
runByVInit :: ByVInit τ a -> τ a; fetch :: Monad τ => Addr -> D (ByVInit τ)
memo :: Monad τ => Addr -> D (ByVInit τ) -> D (ByVInit τ)
instance IsTrace τ => HasAlloc (ByVInit τ) (Value (ByVInit τ)) where
  alloc f = do
    a <- nextFree <$> ByVInit get
    ByVInit $ modify (\μ -> ext μ a retStuck)
    fmap return $ step Let1 $ memo a $ f (fetch a)
\end{spec}
%if style == newcode
\begin{code}
newtype ByVInit τ v = ByVInit (StateT (Heap (ByVInit τ)) τ v)
  deriving (Functor,Applicative,Monad)

runByVInit :: IsTrace τ => ByVInit τ a -> τ a
runByVInit (ByVInit m) = evalStateT m emp

instance IsTrace τ => IsTrace (ByVInit τ) where
  step e (ByVInit (StateT m)) = ByVInit $ StateT $ \μ -> step e (m μ)

fetch' :: Monad τ => Addr -> D (ByVInit τ)
fetch' a = ByVInit get >>= \μ -> μ ! a

memo' :: Monad τ => Addr -> D (ByVInit τ) -> D (ByVInit τ)
memo' a d = d >>= ByVInit . StateT . upd
  where upd v μ = return (v, ext μ a (return v))

instance IsTrace τ => HasAlloc (ByVInit τ) (Value (ByVInit τ)) where
  alloc f = do
    a <- nextFree <$> ByVInit get
    ByVInit $ modify (\μ -> ext μ a retStuck)
    fmap return $ step Let1 $ memo' a $ f (fetch' a)
\end{code}
%endif
\caption{Call-by-value with lazy initialisation}
\label{fig:by-value-init}
\end{figure}

\subsubsection{Call-by-value}

By defining a |MonadFix| instance for |T| and defining |alloc| in terms
of this instance, we can give a by-value semantics to |Expr|, as shown in
\Cref{fig:by-value}.
Let us unpack the definition of |alloc|.
As its first action, it yields a brand new |Let1| event, indicating in the
trace that focus descends into the right-hand side of a |Let|.%
\footnote{If call-by-value was our main focus, it would be prudent to rename
$\BindT$ to $\LetET$ to indicate the bracket relation.}
The definition of |mfix| on |T| then takes over;
producing a trace |τ| which ends in a |Ret v| after finitely many steps.
The value |v| is then passed to the argument |f| of |alloc|, wrapped in a
|return|.
This procedure works as long as |f| does not scrutinise |v| before producing
the |Ret| constructor.
The effect is that the trace |τ| is yielded \emph{while executing |mfix|}, and
the value |v| is then |return|ed as the result of |alloc|.
Subsequent evaluations of |return v| will not have to yield the |Step|s of |τ|
again.

Let us trace $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$ for call-by-value:

< ghci> eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)
$\perform{eval (read "let i = (λy.λx.x) i in i i") emp :: D (ByValue T)}$
\\[\belowdisplayskip]
\noindent
The beta reduction now happens once within the $\LetIT$/$\BindT$ bracket; the
two subsequent $\LookupT$ events immediately halt with a value.

\subsubsection{Lazy Initialisation and Black-holing}

Alas, this model of call-by-value does not yield a total interpreter!
Consider the case when the right-hand side accesses its value before yielding
one, \eg,

< ghci> takeT 5 $ eval (read "let x = x in x x") emp :: ByValue T (Maybe (Value (ByValue T)))
$\LetIT\rightarrow\LookupT(x)\rightarrow\BindT\rightarrow\AppIT\rightarrow\LookupT(x)\rightarrow\texttt{\textasciicircum{}CInterrupted}$
\\[\belowdisplayskip]
\noindent
This loops forever unproductively, rendering the interpreter unfit as a
denotational semantics.
Typical strict languages work around this issue in either of two ways:
They enforce termination of the RHS syntactically (OCaml, ML), or they use
\emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
We could recover a total interpreter using the semantics in \citet{Nakata:10},
reusing the implementation from |ByNeed| and initialising the heap
with a \emph{black hole}~\citep{stg} |retStuck| in |alloc| as in
\Cref{fig:by-value-init}.

< ghci> runByVInit $ eval (read "let x = x in x x") emp :: T (Value (ByVInit T))
$\perform{runByVInit $ eval (read "let x = x in x x") emp :: T (Value (ByVInit T))}$


\begin{figure}
\begin{spec}
data Fork f a = Empty | Single a | Fork (f a) (f a)
data ParT m a = ParT (m (Fork (ParT m) a))
instance Monad τ => Alternative (ParT τ) where
  empty = ParT (pure Empty)
  l <|> r = ParT (pure (Fork l r))

newtype Clairvoyant τ a = Clairvoyant (ParT τ a)
runClair :: D (Clairvoyant T) -> T (Value (Clairvoyant T))

instance (MonadFix τ, IsTrace τ) => HasAlloc (Clairvoyant τ) (Value (Clairvoyant τ)) where
  alloc f = Clairvoyant (skip <|> let') where  skip = return (Clairvoyant empty)
                                               let' = fmap return $ step Let1 $ ... ^^ mfix ... f ...
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

instance IsTrace τ => IsTrace (Clairvoyant τ) where
  step e (Clairvoyant (ParT mforks)) = Clairvoyant $ ParT $ step e mforks

leftT :: Monad τ => ParT τ a -> ParT τ a
leftT (ParT τ) = ParT $ τ >>= \case
  Fork l _ -> unParT l
  _ -> undefined

rightT :: Monad τ => ParT τ a -> ParT τ a
rightT (ParT τ) = ParT $ τ >>= \case
  Fork _ r -> unParT r
  _ -> undefined

parLöb :: MonadFix τ => (Fork (ParT τ) a -> ParT τ a) -> ParT τ a
parLöb f = ParT $ mfix (unParT . f) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork _ _ -> pure (Fork (parLöb (leftT . f)) (parLöb (rightT . f)))

instance (MonadFix τ, IsTrace τ) => HasAlloc (Clairvoyant τ) (Value (Clairvoyant τ)) where
  alloc f = Clairvoyant (skip <|> let')
    where
      skip = return (Clairvoyant empty)
      let' = do
        v <- parLöb $ unClair . step Let1 . f . Clairvoyant . ParT . pure
        return (return v)

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
with an additional $\LetIT$ event.
Similar to |ByValue|, the interpreter is not total so it is unfit as a
denotational semantics without a complicated domain theoretic judgment.
Furthermore, the decision whether or not a $\LetIT$ is needed can be delayed for
an infinite amount of time, as exemplified by

< ghci> runClair $ eval (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))
%$\perform{runClair $ eval (read "let i = Z() in let w = λy.y y in w w") emp :: T (Value (Clairvoyant T))}$
\texttt{\textasciicircum{}CInterrupted}
\\[\belowdisplayskip]
\noindent
The program diverges without producing even a prefix of a trace because the
binding for $i$ might be needed at an unknown point in the future
(a \emph{liveness property} and hence impossible to verify at runtime).
This renders Clairvoyant call-by-value inadequate for verifying safety
properties.

\subsection{More Trace Types}

Our simple trace type |T| has served us well so far, allowing us to study a
variety of total denotational interpreters for all major evaluation strategies
(\eg, |ByName|, |ByNeed|, |ByVInit|).
It is of course possible in Haskell to abandon totality, discard all events and
use plain |data Identity a = Identity a| as the trace type accompanied by the
one-line definition |instance IsTrace Identity where step _ ia = ia|.
The resulting interpreter diverges whenever the defined program diverges, as is
typical for partial definitional interpreters:

%if style == newcode
\begin{code}
instance IsTrace Identity where step _ = id
\end{code}
%endif

< ghci> eval (read "let i = λx.x in i i") emp :: D (ByName Identity)
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName Identity)}$

< ghci> eval (read "let x = x in x") emp :: D (ByName Identity)
%$\perform{eval (read "let x = x in x") emp :: D (ByName Identity)}$
\texttt{\textasciicircum{}CInterrupted}
\\[\belowdisplayskip]
\noindent
We will consider more abstract trace instantiations in \Cref{sec:abstractions}.
