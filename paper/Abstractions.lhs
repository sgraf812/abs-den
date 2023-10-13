%options ghci -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Abstractions where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.List as List
import Expr
import Order
import Interpreter
\end{code}
%endif

\section{Abstractions}
\label{sec:abstractions}

%\cite{*}
We have seen that |eval| is well-suited to express concrete semantics
coinductively.
In this section, we will see how |eval| is also well-suited to implement
abstract semantics, \eg, static program analyses thus featuring an
inductively-defined domain.

\begin{figure}
\begin{spec}
class Eq a => Lat a where bottom :: a; (⊔) :: a -> a -> a;
lub :: Lat a => [a] -> a; kleeneFix :: Lat a => (a -> a) -> a
instance (Ord k, Lat v) => Lat (k :-> v) where bottom = emp; (⊔) = Map.unionWith (⊔)
\end{spec}
%kleeneFix f = go (f bottom) where go x = let x' = f x in if x' ⊑ x then x' else go x'
\caption{Order theory and Kleene fixpoint}
\label{fig:lat}
\end{figure}

\begin{figure}
\begin{code}

data U = U0 | U1 | Uω; instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0 ⊔ u = u
  u ⊔ U0 = u
  U1 ⊔ U1 = U1
  _ ⊔ _ = Uω
{-" \fi "-}
data UT a = Uses (Name :-> U) a

instance Monad UT where
  return a = Uses emp a
  Uses φ1 a >>= k | Uses φ2 b <- k a = Uses (φ1+φ2) b

instance IsTrace UT where
  step (Lookup x)  (Uses φ a)  = Uses (φ + ext emp x U1) a
  step _           τ           = τ
\end{code}
\caption{|IsTrace| instance for semantic usage abstraction}
\label{fig:usg-abs}
\end{figure}

\begin{figure}
\begin{code}
data UValue = Nop; type UD = UT UValue

nopD :: UD
nopD = Uses emp Nop

manify :: UD -> UD
manify (Uses φ Nop) = Uses (φ+φ) Nop

instance IsValue UT UValue where
  retStuck                                  = nopD
  retFun {-" \iffalse "-}_{-" \fi "-} f     = manify (f nopD)
  retCon {-" \iffalse "-}_{-" \fi "-} _ ds  = manify (foldr (+) nopD ds)
  apply Nop d                               = manify d
  select Nop fs                             = lub [ f (replicate (conArity k) nopD) | (k,f) <- fs ]

instance Lat UD where
  bottom = nopD
  Uses φ1 Nop ⊔ Uses φ2 Nop = Uses (φ1 ⊔ φ2) Nop

instance HasAlloc UT UValue where alloc f = pure (kleeneFix f)
\end{code}
%if style == newcode
\begin{code}
deriving instance Eq U
deriving instance Eq a => Eq (UT a)
deriving instance Eq UValue
deriving instance Functor UT

instance Show U where
  show U0 = "0"
  show U1 = "1"
  show Uω = "ω"

class Plussable a where
  (+) :: a -> a -> a

instance Plussable U where
  U1 + U1 = Uω
  u1 + u2 = u1 ⊔ u2

instance Plussable (Name :-> U) where
  (+) = Map.unionWith (+)

instance Show a => Show (UT a) where
  show (Uses φ _) = show φ

instance Applicative UT where
  pure a = Uses emp a
  (<*>) = ap

instance Show UValue where
  show Nop = ""

instance Plussable UD where
  Uses us1 _ + Uses us2 _ = Uses (us1 + us2) Nop
\end{code}
%endif
\caption{Naïve usage analysis via |IsValue| and |HasAlloc|}
\label{fig:abs-usg}
\end{figure}

\subsection{Usage analysis}

The gist of usage analysis is that it collects upper bounds for the number
$\LookupT$ transitions per variable.
We can encode this intuition in the custom trace type |UT| in \Cref{fig:usg-abs}
that will take the place of |T|.
|UT| collects the number of transitions per variable in a usage environment
|Name :-> U|, with the matching |Monad| and |IsTrace| instances.
Whenever we omit definitions for |(⊔)| and |(+)| (such as for |U| and
|Name :-> U|), they follows straightforwardly from \Cref{fig:usage}.

If we had no interest in a terminating analysis, we could already make do
with the induced \emph{semantic usage abstraction} |ByName UT|:

< ghci> eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)
$\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)}$

Of course, this will diverge whenever the object program diverges.
Perhaps interestingly, we have not needed any order theory so far, because the
abstraction is a precise fold over the program trace, thanks to the concrete
|Value|s manipulated.

If we want to assess usage cardinality statically, we have to find a more abstract
representation of |Value|.
\Cref{fig:abs-usg} gives on such candidate |UValue|, a type containing a single
inhabitant |Nop|, so it is the simplest abstraction possible.
It is a matter of simple calculation to see that |eval e {-"\tr_Δ"-} :: UD|
indeed computes the same result as $\semusg{\pe}_{\tr_Δ}$ (given an appropriate
encoding of $\tr_Δ$ as a |Name :-> U| and an |e| without data types), once we
have understood the type class instances at play.

This abstraction is fundamentally encoded in the |IsValue| instance:
|retStuck|,|retFun| and |retCon| correspond to abstraction functions from
concrete value to abstract representation, and |apply| and |select| encode
the concretisation of operations on functions and constructors in terms of
the abstract domain |UD|.

When a |Nop| value is |apply|'d to an argument, the result is that of
evaluating that argument many times (note that it is enough to evaluate twice in
|U|), corresponding exactly to the $ω * d$ in the application case of
\Cref{fig:usage}.
When a |Nop| value is |select|ed, the result is that of evaluating the case
alternatives |fs| with |nopD| for field denotations of the corresponding
constructor, then returning the least upper bound |lub| of all alternatives.
Such a |nopD| is simply an inert denotation that does not contribute any uses
itself, but crucially distributes the |Nop| value to field accesses inside |fs|,
leading to conservative approximation in turn.

Dually, when a constructor application is returned in |retCon|, all the fields
are evaluated eagerly, and many times, conservatively approximating potential
use of any of the fields in the future.
This justifies passing |nopD| for field denotations in |select|; the fields have
already been ``squeezed dry'' in |retCon|.
Likewise, when returning a function in |retFun|, that function is ``squeezed
dry'' by passing it a |nopD| and |manify|ing the result, thus accounting for
uses inside the function body at any potential call site.
(Recall that uses of the concrete argument at the call site is handled by
|apply|.)

The final key to a terminating definition is in swapping out the fixpoint
combinator via a |HasAlloc| instance for |UValue| that computes an
order-theoretic Kleene fixpoint (\cf. \Cref{fig:lat}) instead of |fix| (which
only works for a productive |f|).
The Kleene fixpoint exists by monotonicity and finiteness of |UD|.

Our naive usage analysis yields the same result as the semantic usage
abstraction for simple examples:

< ghci> eval (read "let i = λx.x in let j = λy.y in i j j") emp :: UD
$\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: UD}$
\\[\belowdisplayskip]
\noindent
However, there are many examples where the results are approximate:
< ghci> eval (read "let i = λx.x in let j = λy.y in i j") emp :: D (ByName UT)
$\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp  :: D (ByName UT)}$
< ghci> eval (read "let i = λx.x in let j = λy.y in i j") emp :: UD
$\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp  :: UD}$
< ghci> eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp :: D (ByName UT)
$\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp  :: D (ByName UT)}$
< ghci> eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp :: UD
$\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp  :: UD}$

\begin{figure}
\begin{code}
data Type = Type :->: Type | TyConApp TyCon [Type] | TyVar Name | Wrong
data PolyType = PT [Name] Type; data TyCon = {-" ... \iffalse "-} BoolTyCon | NatTyCon | OptionTyCon | PairTyCon {-" \fi "-}

type Constraint = (Type, Type); type Subst = Name :-> Type
data Cts a = Cts (StateT (Set Name,Subst) Maybe a)
emitCt :: Constraint -> Cts ();                   freshTyVar :: Cts Type
instantiatePolyTy :: PolyType -> Cts Type; ^^ ^^  generaliseTy :: Cts Type -> Cts PolyType

instance IsTrace Cts where step _ = id
instance IsValue Cts PolyType where {-" ... \iffalse "-}
  retStuck = return (PT [] Wrong)
  retFun {-" \iffalse "-}_{-" \fi "-} f = do
    arg <- freshTyVar
    res <- f (return (PT [] arg)) >>= instantiatePolyTy
    return (PT [] (arg :->: res))
  retCon {-" \iffalse "-}_{-" \fi "-} k ds = do
    con_app_ty <- instantiateCon k
    arg_tys <- traverse (>>= instantiatePolyTy) ds
    res_ty <- freshTyVar
    emitCt (con_app_ty, foldr (:->:) res_ty arg_tys)
    return (PT [] res_ty)
  apply fun_ty d = do
    arg_ty <- d >>= instantiatePolyTy
    res_ty <- freshTyVar
    ty <- instantiatePolyTy fun_ty
    emitCt (ty, arg_ty :->: res_ty)
    return (PT [] res_ty)
  select _  [] = retStuck
  select con_ty fs@((k,_):_) = do
    res_ty <- snd . splitFunTys <$> instantiateCon k
    let TyConApp tc tc_args = res_ty
    ty <- instantiatePolyTy con_ty
    emitCt (ty, res_ty)
    ks_tys <- enumerateCons tc tc_args
    tys <- forM ks_tys $ \(k,tys) ->
      case List.find (\(k',_) -> k' == k) fs of
        Just (_,f) -> f (map (fmap (PT [])) tys)
        _          -> retStuck
    traverse instantiatePolyTy tys >>= \case
      []      -> retStuck
      ty:tys' -> traverse (\ty' -> emitCt (ty,ty')) tys' >> return (PT [] ty)

{-" \fi "-}
instance HasAlloc Cts PolyType where
  alloc f = fmap return $ generaliseTy $ do
    f_ty <- freshTyVar
    f_ty' <- f (return (PT [] f_ty)) >>= instantiatePolyTy
    emitCt (f_ty, f_ty')
    return f_ty

runCts :: Cts PolyType -> PolyType
runCts (Cts m) = case evalStateT m (Set.empty, emp) of Just ty -> ty; Nothing -> PT [] Wrong

closedType :: Cts PolyType -> PolyType
closedType d = runCts (generaliseTy $ d >>= instantiatePolyTy)
\end{code}
%if style == newcode
\begin{code}
deriving instance Eq TyCon
deriving instance Eq Type
deriving instance Functor Cts

instance Applicative Cts where
  pure = Cts . pure
  (<*>) = ap

instance Monad Cts where
  Cts m >>= k = Cts (m >>= unCts . k)

instance Show TyCon where
  show BoolTyCon = "\\texttt{bool}"
  show NatTyCon = "\\texttt{nat}"
  show OptionTyCon = "\\texttt{option}"
  show PairTyCon = "\\times"

instance Show Type where
  showsPrec _ (TyConApp k tys) = showsPrec 0 k . foldr (\t s -> showString "\\;" . showsPrec 1 t . s) id tys
  showsPrec _ (TyVar x)  = showString x
  showsPrec _ Wrong      = showString "\\textbf{wrong}"
  showsPrec p (l :->: r) =
    showParen (p > 0) $ showsPrec 1 l . showString " \\rightarrow " . showsPrec 0 r

instance Show PolyType where
  showsPrec _ (PT [] body) = shows body
  showsPrec _ (PT alphas body) = showString "\\forall" . showSep (showString ",") (map showString alphas) . showString ".\\ " . shows body

freeVars :: Type -> Set Name
freeVars (TyVar x) = Set.singleton x
freeVars (a :->: r) = freeVars a `Set.union` freeVars r
freeVars (TyConApp _ as) = Set.unions (map freeVars as)
freeVars Wrong = Set.empty

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = go [] ty
  where
    go as (a :->: r) = go (a:as) r
    go as ty = (reverse as, ty)

conTy :: Tag -> PolyType
conTy TT = PT [] (TyConApp BoolTyCon [])
conTy FF = PT [] (TyConApp BoolTyCon [])
conTy Z = PT [] (TyConApp NatTyCon [])
conTy S = PT [] (TyConApp NatTyCon [] :->: TyConApp NatTyCon [])
conTy None = PT ["a_none"] (TyConApp OptionTyCon [TyVar "a_none"])
conTy Some = PT ["a_some"] (TyVar "a_some" :->: TyConApp OptionTyCon [TyVar "a_some"])
conTy Pair = PT ["a_pair", "b_pair"]
  (TyVar "a_pair" :->: TyVar "b_pair" :->: TyConApp PairTyCon [TyVar "a_pair", TyVar "b_pair"])

tyConTags :: TyCon -> [Tag]
tyConTags tc =
  [ k | k <- [minBound..maxBound]
      , let PT _ ty = conTy k
      , TyConApp tc' _ <- [snd (splitFunTys ty)]
      , tc == tc' ]

applySubst :: Subst -> Type -> Type
applySubst subst ty@(TyVar y)
  | Just ty <- Map.lookup y subst = ty
  | otherwise                   = ty
applySubst subst (a :->: r) =
  applySubst subst a :->: applySubst subst r
applySubst subst (TyConApp k tys) =
  TyConApp k (map (applySubst subst) tys)
applySubst _ ty = ty

unCts :: Cts a -> StateT (Set Name,Subst) Maybe a
unCts (Cts m) = m

addCt (l,r) subst = case (applySubst subst l, applySubst subst r) of
  (l, r) | l == r -> Just subst
  (TyVar x, ty)
    | not (occurs x ty)
    -> Just (Map.insert x ty subst)
  (_, TyVar _) -> addCt (r,l) subst
  (a1 :->: r1, a2 :->: r2) -> addCt (a1,a2) subst >>= addCt (r1,r2)
  (Wrong, Wrong) -> Just subst
  (TyConApp k1 tys1, TyConApp k2 tys2) | k1 == k2 -> foldrM addCt subst (zip tys1 tys2)
  _ -> Nothing
  where
    occurs x ty = applySubst (ext emp x ty) ty /= ty -- quick and dirty

emitCt ct = Cts $ StateT $ \(names,subst) -> case addCt ct subst of
  Just subst' -> Just ((), (names, subst'))
  Nothing     -> Nothing

freshTyVar = Cts $ state $ \(ns,subst) ->
  let n = "\\alpha_{" ++ show (Set.size ns) ++ "}"
  in (TyVar n,(Set.insert n ns,subst))

freshenVars :: [Name] -> Cts Subst
freshenVars alphas = foldM one emp alphas
  where
    one subst alpha = do
      beta <- freshTyVar
      pure (ext subst alpha beta)

instantiatePolyTy (PT alphas ty) = do
  subst <- freshenVars alphas
  return (applySubst subst ty)

instantiateCon :: Tag -> Cts Type
instantiateCon k = instantiatePolyTy (conTy k)

enumerateCons :: TyCon -> [Type] -> Cts [(Tag,[Cts Type])]
enumerateCons tc tc_arg_tys = forM (tyConTags tc) $ \k -> do
  ty <- instantiateCon k
  let (field_tys,res_ty) = splitFunTys ty
  emitCt (TyConApp tc tc_arg_tys, res_ty)
  return (k, map pure field_tys)

generaliseTy (Cts m) = Cts $ do
  (outer_names,_) <- get
  ty <- m
  (_names',subst) <- get
  let ty' = applySubst subst ty
  let alphas = freeVars ty' `Set.difference` outer_names
  return (PT (Set.toList alphas) ty')
\end{code}
%endif
\caption{Hindley-Milner-style type analysis with Let generalisation}
\label{fig:type-analysis}
\end{figure}

\subsection{Type Analysis}

To demonstrate the flexibility of our approach, we have implemented
Hindley-Milner-style type analysis including Let generalisation as an
abstraction.
The gist is given in \Cref{fig:type-analysis}; we omitted large parts of the
implementation and the |IsValue| instance for space reasons.
The full implementation can be found in the Supplement,
the |HasAlloc| instance is exemplary of the approach.

This analysis is all about inferring the most general |PolyType| of the
form $\forall \many{\alpha}.\ θ$ for an expression, where $θ$ ranges over
a |Type| that can be either a type variable |TyVar x|, a function type |θ1 :->:
θ2|, or a type constructor application |TyConApp|.
The |Wrong| type is used to indicate a type error.

Key to the analysis is maintenance of a consistent set of type constraints
as a |Subst|itution, which is why the trace type |Cts| carries one as state,
with the option of failure indicated by |Maybe| when such a substitution
does not exist.
Additionally, |Cts| carries a set of used |Name|s with it to satisfy freshness
constraints in |freshTyVar| and |instantiatePolyTy|, as well as to have a
superset of $\fv(Γ)$ in |generaliseTy|.

While the operational detail offered by |IsTrace| is completely uninteresting to
|Cts|, all these pieces fall together in the implementation of |alloc|, where we
see yet another strategy to compute a fixpoint:
The knot is tied by calling the iteratee |f| with a fresh unification variable
type |f_ty| of the shape $α_1$.
The result of this call in turn is instantiated to a non-|PolyType| |f_ty|, perhaps
turning a type-scheme $\forall α_2.\ \mathtt{option}\;(α_2 \rightarrow α_2)$ into the
shape $\mathtt{option}\;(α_3 \rightarrow α_3)$ for fresh $α_3$.
Then a constraint is emitted to unify $α_1$ with
$\mathtt{option}\;(α_3 \rightarrow α_3)$.
Ultimately, the type |f_ty| is returned and generalised to $\forall α_3.\
\mathtt{option}\;(α_3 \rightarrow α_3)$, because $α_3$ is not a |Name| in use
before the call to |generaliseTy| (and thus couldn't have possibly leaked it
into the range of the type context).

Since this is just intended as another example, we do not attempt a proof of
correctness.
Instead, we conclude with some example uses:

< ghci> closedType $ eval (read "let i = λx.x in i i i i i i") emp
$\perform{closedType $ eval (read "let i = λx.x in i i i i i i") emp}$
< ghci> closedType $ eval (read "λx. let y = x in y x") emp
$\perform{closedType $ eval (read "λx. let y = x in y x") emp}$
< ghci> closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp
$\perform{closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp}$
< ghci> closedType $ eval (read "let x = x in x") emp
$\perform{closedType $ eval (read "let x = x in x") emp}$

\begin{figure}
\begin{spec}
class IsValue τ v | v -> τ where
  retCon :: {-" \highlight{ "-}Label -> {-" } "-}Tag -> [τ v] -> τ v
  retFun :: {-" \highlight{ "-}Label -> {-" } "-}(τ v -> τ v) -> τ v
\end{spec}
\begin{code}
type AbsD = CFA (Pow Label)

--instance Show SynVal where
--  show SomeLit = "N"
--  show (SomeLam l _) = show l

newtype Pow a = Pow { unPow :: Set.Set a }
  deriving (Eq, Ord)

instance Show a => Show (Pow a) where
  showsPrec _ (Pow s) =
    showString "{" . showSep (showString ", ") (map shows (Set.toList s)) . showString "}"

instance Ord a => Lat (Pow a) where
  bottom = Pow Set.empty
  Pow l ⊔ Pow r = Pow (Set.union l r)

data FunCache a b = FC (a :-> b) (a -> b)
data Cache = Cache
  { cCons :: Label :-> (Tag :-> [Pow Label])
  , cArgs :: Label :-> Pow Label
  , cFuns :: Label :-> (AbsD -> AbsD) }

instance Eq Cache where
  c1 == c2 = cArgs c1 == cArgs c2 && cCons c1 == cCons c2

instance Eq (AbsD -> AbsD) where
  _ == _ = True
instance Lat Cache where
  bottom = Cache Map.empty Map.empty Map.empty
  c1 ⊔ c2 = Cache (f cCons) (f cArgs) (Map.unionWith (\l r d -> d >>= \v -> lub <$> sequence [l (return v), r (return v)]) (cFuns c1) (cFuns c2))
    where
      f fld = fld c1 ⊔ fld c2

data CFA a = CFA (State Cache a)
  deriving Functor
instance Applicative CFA where
  pure = CFA . pure
  (<*>) = ap
unCFA :: CFA a -> State Cache a
unCFA (CFA m) = m
instance Monad CFA where
  CFA m >>= k = CFA (m >>= unCFA . k)
instance IsTrace CFA where step _ = id

instance Lat a => Lat [a] where
  bottom = []
  [] ⊔ ys = ys
  xs ⊔ [] = xs
  (x:xs) ⊔ (y:ys) = x ⊔ y : xs ⊔ ys

updCacheCon :: Label -> Tag -> [Pow Label] -> CFA ()
updCacheCon ell k vs = CFA $ modify $ \cache ->
  cache { cCons = Map.singleton ell (Map.singleton k vs) ⊔ cCons cache }
updCacheFun :: Label -> (AbsD -> AbsD) -> CFA ()
updCacheFun ell f = CFA $ modify $ \cache ->
  cache { cFuns = Map.singleton ell f ⊔ cFuns cache }
joinArgsAtLoc :: Label -> Pow Label -> CFA (Pow Label)
joinArgsAtLoc ell v = CFA $ do
  modify $ \cache ->
    cache { cArgs = Map.singleton ell v ⊔ cArgs cache }
  gets ((Map.! ell) . cArgs)
instance IsValue CFA (Pow Label) where
  retStuck = return (Pow Set.empty)
  retCon ell k ds = do
    vs <- sequence ds
    updCacheCon ell k vs
    return (Pow (Set.singleton ell))
  retFun ell f = do
    updCacheFun ell f
    return (Pow (Set.singleton ell))
  apply (Pow lbls) d = do
    cache <- CFA get
    v <- d
    vals <- sequence [ joinArgsAtLoc ell v >>= fun . return | ell <- Set.toList lbls, Just fun <- [Map.lookup ell (cFuns cache)] ]
    return (lub vals)
  select (Pow lbls) fs = do
    cache <- CFA get
    vals <- sequence [ f (map return vs) | ell <- Set.toList lbls, Just cons <- [Map.lookup ell (cCons cache)]
                     , (k,f) <- fs, Just vs <- [Map.lookup k cons] ]
    return (lub vals)
\end{code}
%if style == newcode
\begin{code}
\end{code}
%endif
\caption{0CFA for PCF}
\label{fig:pcf-cfa}
\end{figure}

\subsection{0CFA}

In our last example, we will discuss a classic benchmark of abstract
higher-order interpreters: Control-flow analysis.
For us, this example serves two purposes:
The first is that our approach can be applied to other languages such as PCF as
well; in fact, most abstractions carry over unchanged.
The second is that 0CFA becomes somewhat peculiar

