%if style == newcode
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
import Control.Monad.Trans.State
import Expr

main = eval @_ @(Value (ByName T))`seq` return ()

deriving instance Show Event
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "→" ++ show t
  show (Ret a) = '⟨':show a++"⟩"
instance Show (Value τ) where
  show (Fun _) = "λ"
  show (Con k _) = show k ++ "(...)"
  show Stuck = "🗲"
instance (Show (τ v)) => Show (ByName τ v) where
  show (ByName τ) = show τ

data Div = Div
instance Show Div where
  show Div = "..."

takeT :: Int -> T a -> T (Either Div a)
takeT 0 _ = return (Left Div)
takeT _ (Ret a) = return (Right a)
takeT n (Step e t) = Step e (takeT (n-1) t)
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
an explicit thunk in the definition of |Step|, \eg, @Step of event * 'a t Lazy.t@.
The |Monad| instance of |T| implements the bind operator |(>>=)| by forwarding
|Step|s, thus guarding the recursion~\citep{Capretta:05}.

A semantic element |D| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument |D| to yield
one of the same, or a |Con|structor application giving the denotations of its
fields.
|Value| is a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We repress worries about well-definedness and totality to \Cref{sec:adequacy}.)

\begin{figure}
\begin{code}
type (:->) = Map
empty :: Ord k => k :-> v
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
exts :: Ord k => (k :-> v) -> [k] -> [v] -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
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
  alloc f = return (fix f)
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

\subsection{The Interpreter}

We will now use |D| to give meaning to an expression |e| via an interpreter
function |eval :: Expr -> (Name :-> D) -> D|, where the variable environment
|Name :-> D| is simply a finite mapping from free variables of |e| to their
meaning in |D|.
We summarise the API of environments and sets in \Cref{fig:map}.

We give a definition for |eval| in \Cref{fig:eval}, although in the spirit of
abstract definitional interpreters such as in \citet{Keidel:18} its type is
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
\footnote{where we use |read :: String -> Expr| as a parsing function}

< ghci> eval (read "let i = λx.x in i i") empty :: D

%options ghci -pgmL lhs2TeX -optL--pre
\perform{eval (read "let i = λx.x in i i") empty :: D (ByName T)}

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
a Supplement, containing the complete definitions.}

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

< ghci> takeT 3 $ eval (read "let x = x in x") empty :: D
%options ghci -pgmL lhs2TeX -optL--pre
\perform{takeT 3 $ eval (read "let x = x in x") empty :: D (ByName T)}

< ghci> takeT 3 $ eval (read "let w = λy. y y in w w") empty :: D
%options ghci -pgmL lhs2TeX -optL--pre
\perform{takeT 3 $ eval (read "let w = λy. y y in w w") empty :: D (ByName T)}

\noindent
And data types work as well, allowing for interesting ways to get stuck:

< ghci> takeT 3 $ eval (read "let z = Z() in let o = S(z) in case o of { S(zz) -> zz }") empty :: D
%options ghci -pgmL lhs2TeX -optL--pre
\perform{takeT 3 $ eval (read "let z = Z() in let o = S(z) in case o of { S(zz) -> zz }") empty :: D (ByName T)}

< ghci> takeT 3 $ eval (read "let z = Z() in z z") empty :: D
%options ghci -pgmL lhs2TeX -optL--pre
\perform{takeT 3 $ eval (read "let z = Z() in z z") empty :: D (ByName T)}

\begin{figure}
\begin{spec}
data ByName τ v = ByName (τ v)
instance Monad τ => Monad (ByName τ) where ...
instance IsTrace τ => IsTrace (ByName τ) where ...
instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = return (fix f)
\end{spec}
\begin{comment}
\begin{code}
newtype ByName τ v = ByName { unByName :: (τ v) }
  deriving newtype (Functor,Applicative,Monad)

instance IsTrace τ => IsTrace (ByName τ) where
  step e = ByName . step e . unByName

instance Monad τ => HasAlloc (ByName τ) (Value (ByName τ)) where
  alloc f = return (fix f)
\end{code}
\end{comment}
\caption{Call-by-name}
\label{fig:by-name}
\end{figure}

\begin{figure}
\begin{spec}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr
data ByNeed τ v = ByNeed (StateT (Heap (ByNeed τ)) τ v)
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
\begin{comment}
\begin{code}
type Addr = Int; type Heap τ = Addr :-> D τ; nextFree :: Heap τ -> Addr

nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

newtype ByNeed τ v = ByNeed (StateT (Heap (ByNeed τ)) τ v)
  deriving newtype (Functor,Applicative,Monad)

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
\end{comment}
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

By introducing a heap and memoisation to |τ|, yielding
a trace transformer |ByNeed| in \Cref{fig:by-need} that encodes a call-by-need
evaluation strategy.
What is interesting is that |ByNeed T| denotes a \emph{stateful function
returning a trace}, thus it is the first time we compute with something
different than a |T|.
The |alloc| implementation for |ByNeed| traces will return a |D| that |fetch|es
the bound action from the heap, under an address |a| that is not taken yet in
the current heap |μ|.
This newly heap-bound |D| in turn evaluates |f ...|, the result of which is then
|memo|ised in an |Update| step, so that the heap-bound |D| is replaced by
one that immediately |return|s the value.
We have proven this semantics adequate \wrt to the LK transition system in
\Cref{fig:lk-semantics} with the techniques we develop in \Cref{sec:adequacy}.

\todo{Mention that we could also have tested this result, with a type like
|type ValidateT τ = StateT σ τ|, where the |step| action crashes if the |Event|
does not match the currently applicable LK transition.}

It is worth stressing how simple it was to carry out this extension.
Furthermore, nothing here is specific to |Expr| or |Value|!
The only requirement on |T| is that its |Event| type has an |Update| action,
which makes the implementation of |ByNeed| easily reusable.
\sg{That's not completely true; one would still need to duplicate the code to
adjust it to the particular |Event| data type.
That could be worked around with by parameterising |IsTrace τ ε| over the event
type and then have type class constraint |HasUpdateEvent ε| in |HasAlloc|,
but that seems like a lot complexity for such little benefit.}

Example evaluating $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$:

< ghci> eval (read "let i = (λy.λx.x) i in i i") empty :: D (ByNeed T)
%options ghci -pgmL lhs2TeX -optL--pre
\perform{eval (read "let i = (λy.λx.x) i in i i") empty :: D (ByNeed T)}

