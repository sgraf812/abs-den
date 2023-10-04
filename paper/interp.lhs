\section{A Denotational Interpreter}
\label{sec:interp}

\iffalse
\begin{code}
import Expr
\end{code}
\fi

A denotational interpreter is both a definitional interpreter as well as a
denotational semantics.
Then what is its \emph{semantic domain}?
To a first approximation, we can think of it as a type |D T| such as
\begin{minipage}{0.65\textwidth}
\begin{code}
data T a      = Delay (T a) | Now a
type D τ      = τ (Value τ); type Tag = Integer
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
Every such |D T| corresponds to a program trace |T| that ends with a |Value|.

A trace |T| can either have reached a terminal state |Now| or it can be
|Delay|ed, indicating that the program makes another small-step transition
before reaching a terminal state.
Readers who are familiar with the literature on coinduction will immediately
note that |T| is the delay monad popularised by \citet{Capretta:05}, and that it
could readily be replaced by a more elaborate construction such as interaction
trees~\citep{interaction-trees}.
The coinductive nature of |T|'s definition in Haskell is crucial to our
approach because it allows us to express diverging traces as an infinite,
productive nesting of |Delay|s.

A semantic element |D T| eventually terminates with a |Value| that is either
|Stuck|, a |Fun|ction waiting to be applied to an argument denotation to yield
one of the same, or a |Con|structor application giving the denotations of its
fields.
|Value|s are a standard denotational encoding of their syntactic counterpart,
devoid of any syntax.
(We leave matters of well-definedness and totality to \Cref{sec:totality}.)

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
eval :: forall τ v. (IsTrace τ, IsValue τ v, HasAlloc τ v)
     => Expr -> (Name :-> τ v) -> τ v
eval e env = case e of
  Var x -> Map.findWithDefault stuck x env
  App e x -> case Map.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (eval e env) >>= \v -> apply v d
  Lam x e -> injFun (\d -> app2 (eval e (Map.insert x d env)))
  Let x e1 e2 -> do
    let ext d = Map.insert x (lookup x d) env
    d1 <- alloc (\d1 -> eval e1 (ext d1))
    bind (eval e2 (ext d1))
  ConApp k xs -> case traverse (env Map.!?) xs of
    Just ds
      | length xs == conArity k
      -> injCon k ds
    _ -> stuck
  Case e alts -> case1 $ eval e env >>= \v ->
    select v [ (k, alt_cont xs rhs) | (k,xs,rhs) <- alts ]
    where
      alt_cont xs rhs ds
        | length xs == length ds = case2 (eval rhs (insertMany env xs ds))
        | otherwise              = stuck
      insertMany :: (Name :-> τ v) -> [Name] -> [τ v] -> (Name :-> τ v)
      insertMany env xs ds = foldr (uncurry Map.insert) env (zip xs ds)
\end{code}
