%include custom.fmt
\section{A Denotational Interpreter}
\label{sec:interp}

\begin{minipage}{0.27\textwidth}
\begin{code}
type ConTag = Integer
type D τ = τ (Value τ)
data Value τ
  =  Stuck
  |  Fun (D τ -> D τ)
  |  Con ConTag [D τ]
data T a
  =  Delay (T a)
  |  Now a
\end{code}
\end{minipage}%
\begin{minipage}{0.43\textwidth}
\begin{code}
instance Monad T where ...
instance IsTrace T where
  lookup _ = Delay; app1 = Delay; ...
instance IsValue T (Value T) where ...
\end{code}
\end{minipage}%
\begin{minipage}{0.3\textwidth}
\begin{code}
instance Monad T where ...
instance IsTrace T where
  lookup _ = Delay; app1 = Delay; ...
instance IsTrace τ -> IsValue τ (Value τ) where ...
\end{code}
\end{minipage}

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
