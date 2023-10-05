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
main = eval @_ @(Value (ByName T))`seq` return ()
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
\begin{code}
type Name = String
type ConTag = Int; conArity :: ConTag -> Int
data Expr  = Var Name | App Expr Name | Lam Name Expr | Let Name Expr Expr
           | ConApp ConTag [Name] | Case Expr [Alt]
type Alt = (ConTag,[Name],Expr)
\end{code}
\begin{comment}
\begin{code}
kNothing,kJust,kPair,kTrue,kFalse :: ConTag
(kNothing:kJust:kPair:kTrue:kFalse:_) = [0..]
conArity k | k == kNothing = 0
           | k == kJust    = 1
           | k == kPair    = 2
           | k == kTrue    = 0
           | k == kFalse   = 0
           | otherwise     = error "unknown constructor"
\end{code}
\end{comment}
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
data Value τ = Stuck | Fun (D τ -> D τ) | Con ConTag [D τ]
\end{code}
\end{comment}
\begin{spec}
type D = T (Value T)
data T a = Step Event (T a) | Ret a
data Event  = Lookup Name | Update | App1 | App2
            | Bind | Case1 | Case2
data Value = Stuck | Fun (D -> D) | Con ConTag [D]
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

We decided to embellish each |Step| with intensional information about the
particular type of small-step |Event|, for example we attach the |Name| of the
let-bound variable to |Lookup|.
The reason for this decision will become clear later; just note that the
choice of |Event| suggests a spectrum of intensionality, with |data Event =
Unit| corresponding to the ``delay monad'' popularised by \citet{Capretta:05} on
the more abstract end of the spectrum and arbitrary syntactic detail attached to
each of |Event|'s constructors at the other end of the spectrum.
If our language had facilities for input/output, we could have started from a
more elaborate construction such as interaction trees~\citep{interaction-trees}.

The coinductive nature of |T|'s definition in Haskell is crucial to our
approach because it allows us to express diverging traces as an infinite,
productive nesting of |Delay|s; in a strict language, we would have introduced
an explicit thunk in the definition of |Delay|, \eg, @Delay of 'a t Lazy.t@.

A semantic element |D| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |D| to yield
one of the same, or a |Con|structor application giving the denotations of its
fields.
|Value| is a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We repress foreboding thoughts on well-definedness and totality to
\Cref{sec:totality}.)

The |Monad| instance of |T| implements |return| via |Ret| and the bind operator
|(>>=)| by forwarding the |Step|, thus guarding the recursion.
%It is no surprise that |T| is also an instance of the |IsTrace| type class in
%\Cref{fig:traces}.



Need to generalise |D| and |Value| over the trace type,
\begin{spec}
type D τ = τ (Value τ)
data Value τ = Stuck | Fun (D τ -> D τ) | Con ConTag [D τ]
\end{spec}

\begin{figure}
\begin{minipage}{0.43\textwidth}
\begin{code}
class Monad τ => IsTrace τ where
  step :: Event -> τ v -> τ v

class IsValue τ v | v -> τ where
  stuck :: τ v
  injFun :: (τ v -> τ v) -> τ v
  apply :: v -> τ v -> τ v
  injCon :: ConTag -> [τ v] -> τ v
  select :: v -> [(ConTag, [τ v] -> τ v)] -> τ v

class HasAlloc τ v | v -> τ where
  alloc :: (τ v -> τ v) -> τ (τ v)
\end{code}
\begin{comment}
\begin{code}
instance IsTrace T where
  step = Step
instance IsTrace τ => IsValue τ (Value τ) where
  stuck = return Stuck
  injFun f = return (Fun f)
  injCon k ds = return (Con k ds)
  apply (Fun f) d = f d
  apply _       _ = stuck
  select v alts
    | Con k ds <- v
    , Just (_,alt) <- find (\(k',_) -> k' == k) alts
    = alt ds
    | otherwise
    = stuck
\end{code}
\end{comment}
\begin{spec}
instance IsTrace T where
  step = Step
instance IsValue T (Value T) where ...
\end{spec}
\end{minipage}%
\label{fig:traces}
\caption{Semantic Domain of Traces}
\end{figure}

\begin{figure}
\begin{code}
type (:->) = Map
ext :: (Name :-> v) -> Name -> v -> (Name :-> v)
exts :: (Name :-> v) -> [Name] -> [v] -> (Name :-> v)
(!) :: (Name :-> v) -> Name -> v
dom :: (Name :-> v) -> Set Name
(∈) :: Name -> Set Name -> Bool
\end{code}
\begin{comment}
\begin{code}
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl' (uncurry . ext) ρ (zip xs ds)
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
\end{code}
\end{comment}
\label{fig:map}
\caption{Environments}
\end{figure}

\begin{figure}
\begin{code}
eval :: (IsTrace τ, IsValue τ v, HasAlloc τ v) => Expr -> (Name :-> τ v) -> τ v
eval e ρ = case e of
  Var x    | x ∈ dom ρ  -> ρ ! x
           | otherwise  -> stuck
  App e x  | x ∈ dom ρ  -> step App1 (eval e ρ) >>= \v -> apply v (ρ ! x)
           | otherwise  -> stuck
  Lam x e -> injFun (\d -> step App2 (eval e (ext ρ x d)))
  Let x e1 e2 -> do
    let wrap d = ext ρ x (step (Lookup x) d)
    d1 <- alloc (\d1 -> eval e1 (wrap d1))
    step Bind (eval e2 (wrap d1))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> injCon k (map (ρ !) xs)
    | otherwise
    -> stuck
  Case e alts -> step Case1 (eval e ρ >>= \v ->
    select v [ (k, cont rhs xs) | (k,xs,rhs) <- alts ])
    where
      cont rhs xs ds
        | length xs == length ds  = step Case2 (eval rhs (exts ρ xs ds))
        | otherwise               = stuck
\end{code}
%  ConApp k xs  | all (∈ dom ρ) xs  -> injCon k (map (ρ !) xs)
%               | otherwise         -> stuck
%  Case e alts -> step Case1 (eval e ρ >>= \v ->
%    select v [ (k, step Case2 . eval rhs . exts ρ xs) | (k,xs,rhs) <- alts ])
\label{fig:map}
\caption{Denotational interpreter}
\end{figure}

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
\label{fig:map}
\caption{Call-by-name}
\end{figure}

