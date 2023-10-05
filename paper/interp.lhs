\section{A Denotational Interpreter}
\label{sec:interp}

We will now define a denotational interpreter in Haskell.
It is worth stressing that we picked Haskell out of convenience and familiarity,
rather than out of necessity:
We make use of laziness in only one key position and could just as well have
used a strict higher-order language such as OCaml, ML or Scheme with an explicit
thunk operator.

\iffalse
\begin{code}
import Expr
\end{code}
\fi

\subsection{Semantic Domain}

A denotational interpreter is both a definitional interpreter as well as a
denotational semantics.
Then what is its \emph{semantic domain}?
To a first approximation, we can think of it as a type |D T|, defined as
\begin{minipage}{0.65\textwidth}
\begin{code}
data T a = Delay (T a) | Now a
type D τ = τ (Value τ);      type Tag = Integer
data Value τ  = Stuck | Fun (D τ -> D τ) | Con Tag [D τ]
\end{code}
\end{minipage}
\begin{minipage}{0.35\textwidth}
\begin{code}
instance Monad T where
  return a = Now a
  Delay τ >>= k = Delay (τ >>= k)
\end{code}
\end{minipage}
Every such |D T| corresponds to a program trace |T| that ends with a concrete
|Value|.

A trace |T| can either have reached a terminal state |Now| or it can be
|Delay|ed, indicating that the program makes another small-step transition
before reaching a terminal state.
Readers who are familiar with the literature on coinduction will immediately
recgnise |T| as the delay monad popularised by \citet{Capretta:05}.
Furthermore, |T| could readily be replaced by a more elaborate construction such
as interaction trees~\citep{interaction-trees} or one that captures more
intensional information in its |Delay| constructor, such as the kind of
transition taken and relevant syntactic information from the state transition.
The reason we chose |T| is for its simplicity:
It is the simplest type that supports a semantics that is adequate \wrt the
small-step semantics.
The coinductive nature of |T|'s definition in Haskell is crucial to our
approach because it allows us to express diverging traces as an infinite,
productive nesting of |Delay|s; in a strict language, we would have introduced
an explicit thunk in the definition of |Delay|, \eg, @Delay of 'a t Lazy.t@.

A semantic element |D T| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument denotation to yield
one of the same, or a |Con|structor application giving the denotations of its
fields.
|Value| is a standard denotational encoding of its syntactic counterpart, devoid
of any syntax.
(We leave foreboding concerns of well-definedness and totality to
\Cref{sec:totality}.)

The |Monad| instance of |T| implements |return| via |Now| and the
bind operator |(>>=)| by forwarding the |Delay|, thus guarding the recursion.

\begin{figure}
\begin{minipage}{0.43\textwidth}
\begin{comment}
\begin{code}
instance IsTrace T where
  lookup _ = Delay
  app1 = Delay
  app2 = Delay
  case1 = Delay
  case2 = Delay
  update = Delay
  let_ = Delay
instance IsValue T (Value T) where
  stuck = return Stuck
  injFun f = return (Fun f)
  injCon k ds = return (Con k ds)
  apply (Fun f) d = f d
  apply _       _ = stuck
  select v alts
    | Con k ds <- v
    , Just (_,alt) <- List.find (\(k',_) -> k' == k) alts
    = alt ds
    | otherwise
    = stuck
\end{code}
\end{comment}
\begin{spec}
instance IsTrace T where
  lookup _ = Delay; app1 = Delay; ...
instance IsValue T (Value T) where ...
\end{spec}
\end{minipage}%
\label{fig:conc-trace}
\caption{Concrete Domain of Traces}
\end{figure}

\begin{code}
class Monad τ => IsTrace τ where
  lookup :: Name -> τ v -> τ v
  app1,app2,bind,case1,case2,update :: τ v -> τ v

class Monad τ => IsValue τ v where
  stuck :: τ v
  injFun :: (τ v -> τ v) -> τ v
  apply :: v -> τ v -> τ v
  injCon :: ConTag -> [τ v] -> τ v
  select :: v -> [(ConTag, [τ v] -> τ v)] -> τ v

class IsTrace τ => HasAlloc τ v where
  alloc :: (τ v -> τ v) -> τ (τ v)

type (:->) = Map
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
(∈) :: Ord a => a -> Set a -> Bool
eval :: forall τ v. (IsTrace τ, IsValue τ v, HasAlloc τ v)
     => Expr -> (Name :-> τ v) -> τ v
eval e ρ = case e of
  Var x  | x ∈ dom ρ -> ρ ! x
         | otherwise -> stuck
  App e x  | x ∈ dom ρ -> app1 (eval e ρ) >>= \v -> apply v (ρ ! x)
           | otherwise -> stuck
  Lam x e -> injFun (\d -> app2 (eval e (ext x d ρ)))
  Let x e1 e2 -> do
    let wrap d = Map.insert x (lookup x d) ρ
    d1 <- alloc (\d1 -> eval e1 (wrap d1))
    bind (eval e2 (ext d1))
  ConApp k xs
    | all (\x -> x ∈ dom ρ) xs , length xs == conArity k
    -> injCon k (map (ρ !) xs)
    | otherwise
    -> stuck
  Case e alts -> case1 $ eval e ρ >>= \v ->
    select v [ (k, alt_cont xs rhs) | (k,xs,rhs) <- alts ]
    where
      alt_cont xs rhs ds
        | length xs == length ds = case2 (eval rhs (insertMany ρ xs ds))
        | otherwise              = stuck
      insertMany :: (Name :-> τ v) -> [Name] -> [τ v] -> (Name :-> τ v)
      insertMany ρ xs ds = foldr (uncurry Map.insert) ρ (zip xs ds)
\end{code}
