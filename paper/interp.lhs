%options ghci
\begin{comment}
\begin{code}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (find, foldl')
import Data.Function (fix)
import Control.Monad
import Expr

main = eval @_ @(Value (ByName T))`seq` return ()

deriving instance Show Event
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "→" ++ show t
  show (Ret a) = '⟨':show a++"⟩"
instance Show (Value τ) where
  show (Fun _) = "λ"
  show (Con k _) = show k
  show Stuck = "🗲"
instance (Show (τ v)) => Show (ByName τ v) where
  show (ByName τ) = show τ
\end{code}
\end{comment}

\section{A Denotational Interpreter}
\label{sec:interp}

We will now define a denotational interpreter in Haskell.
It is worth stressing that we picked Haskell out of convenience and familiarity,
rather than out of necessity:
We make use of laziness in only one key position and could just as well have
used a strict higher-order language such as OCaml, ML or Scheme with an explicit
thunk operator.

\begin{figure}
\begin{spec}
type Name = String
type Tag = Int; conArity :: Tag -> Int
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
\begin{comment}
\begin{code}
type D τ = τ (Value τ)
data T a = Step Event (T a) | Ret a
data Event  = Lookup Name | Update | App1 | App2
            | Bind | Case1 | Case2
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{code}
\end{comment}
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
\begin{comment}
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
\end{comment}
\end{minipage}
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
an explicit thunk in the definition of |Step|, \eg, @Step of event * 'a t Lazy.t@.
The |Monad| instance of |T| implements the bind operator |(>>=)| by forwarding
|Step|s, thus guarding the recursion~\citep{Capretta:05}.

A semantic element |D| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |D| to yield
one of the same, or a |Con|structor application giving the denotations of its
fields.
|Value| is a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We repress foreboding thoughts on well-definedness and totality to
\Cref{sec:totality}.)



\begin{figure}
\begin{code}
type (:->) = Map
empty :: Name :-> v
ext :: (Name :-> v) -> Name -> v -> (Name :-> v)
exts :: (Name :-> v) -> [Name] -> [v] -> (Name :-> v)
(!) :: (Name :-> v) -> Name -> v
dom :: (Name :-> v) -> Set Name
(∈) :: Name -> Set Name -> Bool
\end{code}
\begin{comment}
\begin{code}
empty = Map.empty
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl' (uncurry . ext) ρ (zip xs ds)
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
\end{code}
\end{comment}
\caption{Environments}
\label{fig:map}
\end{figure}

\subsection{The Interpreter}

We will now use |D| to give meaning to an expression |e| via an interpreter
function |eval :: Expr -> (Name :-> D) -> D|, where the variable environment
|Name :-> D| is simply a finite mapping from free variables of |e| to their
meaning in |D|.
We summarise the API of environments and sets in \Cref{fig:map}.

We give a definition for |eval| in \Cref{fig:eval}, although in the spirit of
abstract definitional interpreters its type is quite a bit more general than its
instantiation at |D| to offer the same abstraction capabilities.

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
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like this:

< ghci> eval (read "let i = λx.x in i i") empty :: D

%\eval{eval (read "let i = λx.x in i i") empty :: D (ByName T)}
\texttt{Bind→App1→Lookup "i"→App2→Lookup "i"→⟨λ⟩}

Which is in direct correspondence to the call-by-name small-step trace.

While |IsTrace| is exactly a final encoding of |T|, |IsValue| is not quite the
same to |Value|:
For one, the ``injections'' |retStuck|, |retFun| and |retCon| return a |T Value|,
not simply a |Value|; a curiosity that we will revisit in \Cref{fig:abstractions}
when we consider abstract interpretations of |Value| that don't necessarily
instantiate these methods with |return . _|.
On the other hand, the ``eliminators'' |apply| and |select| can be implemented
in the obvious way for |T|.
The omitted definition for |select| finds the |alt| in |alts| that matches the
|Tag| of the |Con| value |v| and applies said |alt| to the field denotations of
|v|; failure to perform any of these steps results in |retStuck|.
\footnote{We extract from this document a runnable Haskell file which we add as a Supplement.}

The third type class is |HasAlloc|, the most significant knob to our
interpreter.
Its |alloc| method is used to give meaning to recursive let bindings; as such
its type is \emph{almost} an instance of the venerable least fixpoint combinator
|fix :: (a -> a) -> a|, if it weren't for the additional |τ| wrapping in its
result type.
This function will be an important extension point for implementing heap-based
evaluation strategies such as call-by-need or ref cells; but for now the
concrete implementation for |D| given in \Cref{fig:trace-instances} simply calls
out to |fix|, yielding a call-by-name evaluation strategy.

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
  Lam x e -> retFun $ \d ->
    step App2 (eval e ((ext ρ x d)))
  Let x e1 e2 -> do
    d1 <- alloc (\d1 -> eval e1 (ext ρ x (step (Lookup x) d1)))
    step Bind (eval e2 (ext ρ x (step (Lookup x) d1)))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> retCon k (map (ρ !) xs)
    | otherwise
    -> retStuck
  Case e alts -> step Case1 $ do
    v <- eval e ρ
    select v [ (k, cont er xs) | (k,xs,er) <- alts ]
    where
       cont er xs ds
         | length xs == length ds
         = step Case2 (eval er (exts ρ xs ds))
         | otherwise
         = retStuck
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
  retFun :: (τ v -> τ v) -> τ v
  apply :: v -> τ v -> τ v
  retCon :: Tag -> [τ v] -> τ v
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
  retFun f = return (Fun f)
  retCon k ds = return (Con k ds)
  apply  (Fun f)  d  = f d
  apply  _        _  = retStuck
  select v alts = ...

instance HasAlloc T Value where
  alloc f = pure (fix f)
\end{code}
%else
\begin{code}
instance IsTrace T where
  step = Step

instance IsTrace τ => IsValue τ (Value τ) where
  retStuck = return Stuck
  retFun f = return (Fun f)
  retCon k ds = return (Con k ds)
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

\subsection{More Evaluation Strategies}

Need to generalise |D| and |Value| over the trace type,
\begin{spec}
type D τ = τ (Value τ)
data Value τ = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{spec}

\begin{figure}
\begin{spec}
newtype ByName τ v = ByName (τ v)
instance Monad τ => Monad (ByName τ)
instance IsTrace τ => IsTrace (ByName τ)
instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = pure (fix f)
\end{spec}
\begin{comment}
\begin{code}
newtype ByName τ v = ByName { unByName :: (τ v) }
  deriving newtype (Functor,Applicative,Monad)

instance IsTrace τ => IsTrace (ByName τ) where
  step e = ByName . step e . unByName

instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = pure (fix f)
\end{code}
\end{comment}
\caption{Call-by-name}
\label{fig:by-name}
\end{figure}

