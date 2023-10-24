%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

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

We have seen that |eval| is well-suited to express concrete semantics
coinductively.
In this section, we will see how |eval| is also well-suited to implement
abstract semantics, \eg, static program analyses with an inductively-defined
domain.

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
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
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

The gist of usage analysis is that it collects upper bounds for the number of
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
\Cref{fig:abs-usg} gives one such candidate |UValue|, a type containing a single
inhabitant |Nop|, so it is the crudest possible summary of a concrete |Value|.
It is a matter of simple calculation to see that |eval e trD :: UD|
indeed computes the same result as $\semusg{\pe}_{\tr_Δ}$ from \Cref{fig:usage}
(given an appropriate encoding of $\tr_Δ$ as a |Name :-> UD| and an |e| without
data types), once we have understood the type class instances at play.

The |IsValue| instance calculates a summary of a semantic usage value.
|retStuck|,|retFun| and |retCon| map from values to summarised representation,
and |apply| and |select| encode the concretisation of |Nop| in terms of the
abstract domain |UD|.

When a |Nop| is |apply|'d to an argument, the result is that of
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
(Recall that uses of the argument at the call site is handled by |apply|.)

The final key to a terminating definition is in swapping out the fixpoint
combinator via the |HasAlloc| instance for |UValue| that computes an
order-theoretic Kleene fixpoint (\cf. \Cref{fig:lat}) instead of |fix| (which
only works for a corecursive |f|).
The Kleene fixpoint exists by monotonicity and finiteness of |UD|.

\subsubsection*{Examples}
Our naive usage analysis yields the same result as the semantic usage
abstraction in simple cases:

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
deriving instance Enum TyCon
deriving instance Bounded TyCon
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
  let one n = freeVars $ applySubst subst (TyVar n)
  let fvΓ = Set.unions (Set.map one outer_names)
  let alphas = freeVars ty' `Set.difference` fvΓ
  return (PT (Set.toList alphas) ty')
\end{code}
%endif
\caption{Hindley-Milner-style type analysis with Let generalisation}
\label{fig:type-analysis}
\end{figure}

\subsection{Type Analysis}

To demonstrate the flexibility of our approach, we have implemented
Hindley-Milner-style type analysis including Let generalisation as an
insitance of our abstract denotational interpreter.
The gist is given in \Cref{fig:type-analysis}; we omitted large parts of the
implementation and the |IsValue| instance for space reasons.
While the full implementation can be found in the extract generated from this
document, the |HasAlloc| instance is sufficiently exemplary of the approach.

The analysis infers most general |PolyType|s of the
form $\forall \many{\alpha}.\ θ$ for an expression, where $θ$ ranges over a
|Type| that can be either a type variable |TyVar α|, a function type |θ1 :->:
θ2|, or a type constructor application |TyConApp|.
The |Wrong| type is used to indicate a type error.

Key to the analysis is maintenance of a consistent set of type constraints
as a unifying |Subst|itution.
That is why the trace type |Cts| carries the current unifier as state, with the
option of failure indicated by |Maybe| when the unifier does not exist.
Additionally, |Cts| carries a set of used |Name|s with it to satisfy freshness
constraints in |freshTyVar| and |instantiatePolyTy|, as well as to construct a
superset of $\fv(Γ)$ in |generaliseTy|.

While the operational detail offered by |IsTrace| is ignored by |Cts|, all the
pieces fall together in the implementation of |alloc|, where we see yet another
domain-specific fixpoint strategy:
The knot is tied by calling the iteratee |f| with a fresh unification variable
type |f_ty| of the shape $α_1$.
The result of this call in turn is instantiated to a non-|PolyType| |f_ty'|,
perhaps turning a type-scheme $\forall α_2.\ \mathtt{option}\;(α_2 \rightarrow
α_2)$ into the shape $\mathtt{option}\;(α_3 \rightarrow α_3)$ for fresh $α_3$.
Then a constraint is emitted to unify $α_1$ with
$\mathtt{option}\;(α_3 \rightarrow α_3)$.
Ultimately, the type |f_ty| is returned and generalised to $\forall α_3.\
\mathtt{option}\;(α_3 \rightarrow α_3)$, because $α_3$ is not a |Name| in use
before the call to |generaliseTy| (and thus it couldn't have possibly leaked
into the range of the ambient type context).

\subsubsection*{Examples}
%Since this is just intended as another example, we do not attempt a proof of
%correctness.
%Instead, we conclude with some example uses:
Let us again conclude with some examples:

< ghci> closedType $ eval (read "let i = λx.x in i i i i i i") emp
$\perform{closedType $ eval (read "let i = λx.x in i i i i i i") emp}$
< ghci> closedType $ eval (read "λx. let y = x in y x") emp
$\perform{closedType $ eval (read "λx. let y = x in y x") emp}$
< ghci> closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp
$\perform{closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp}$
< ghci> closedType $ eval (read "let x = x in x") emp
$\perform{closedType $ eval (read "let x = x in x") emp}$


\begin{figure}
\begin{code}
data Pow a = P (Set a); type CValue = Pow Label
type ConCache = (Tag, [CValue]); data FunCache = FC (Maybe (CValue, CValue)) (CD -> CD)
data Cache = Cache (Label :-> ConCache) (Label :-> FunCache)
data CT a = CT (State Cache a); type CD = CT CValue

runCFA :: CD -> CValue; updFunCache :: Label -> (CD -> CD) -> CT ()

instance IsTrace CT where step _ = id

instance IsValue CT CValue where
  retFun ell f = do updFunCache ell f; return (P (Set.singleton ell))
  apply (P ells) d = d >>= \v -> lub <$> traverse (\ell -> cachedCall ell v) (Set.toList ells)
  {-" ... \iffalse "-}
  retStuck = return bottom
  retCon ell k ds = do vs <- sequence ds; updConCache ell k vs; return (P (Set.singleton ell))
  select (P ells) fs = do
    cache <- CT get
    vals <- sequence [ f (map return vs) | ell <- Set.toList ells, Just (k',vs) <- [Map.lookup ell (cCons cache)]
                     , (k,f) <- fs, k == k' ]
    return (lub vals)
{-" \fi "-}

instance HasAlloc CT CValue where{-" ... \iffalse "-}
  alloc f = fmap return (go bottom)
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- f (return v)
        cache' <- CT get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- f (return v'); if v' /= v'' then error "blah" else return v' } else go v'
{-" \fi "-}
\end{code}

%if style == newcode
\begin{code}
deriving instance Eq a => Eq (Pow a)
deriving instance Ord a => Ord (Pow a)

instance Show (CValue) where
  showsPrec _ (P s) =
    showString "\\{" . showSep (showString ", ") (map showString (Set.toList s)) . showString "\\}"

instance Ord a => Lat (Pow a) where
  bottom = P Set.empty
  P l ⊔ P r = P (Set.union l r)

instance Eq FunCache where
  FC cache1 _ == FC cache2 _ = cache1 == cache2
instance Lat FunCache where
  bottom = FC Nothing (const (return bottom))
  FC cache1 f1 ⊔ FC cache2 f2 = FC cache' f'
    where
      f' d = do
        v <- d
        lv <- f1 (return v)
        rv <- f2 (return v)
        return (lv ⊔ rv)
      cache' = case (cache1,cache2) of
        (Nothing, Nothing)            -> Nothing
        (Just c1, Nothing)            -> Just c1
        (Nothing, Just c2)            -> Just c2
        (Just (in_1,out1), Just (in_2,out2))
          | in_1 ⊑ in_2, out1 ⊑ out2  -> Just (in_2, out2)
          | in_2 ⊑ in_1, out2 ⊑ out1  -> Just (in_1, out1)
          | otherwise                 -> error "uh oh"

instance Show FunCache where
  show (FC Nothing _)           = "[]"
  show (FC (Just (in_, out)) _) = "[" ++ show in_ ++ " \\mapsto " ++ show out ++ "]"

instance Eq Cache where
  c1 == c2 = cFuns c1 == cFuns c2 && cCons c1 == cCons c2

instance Lat Cache where
  bottom = Cache Map.empty Map.empty
  c1 ⊔ c2 = Cache (f cCons) (f cFuns)
    where
      f fld = fld c1 ⊔ fld c2

deriving instance Show Cache

unCT :: CT a -> State Cache a
unCT (CT m) = m

runCFA (CT m) = evalState m (Cache bottom bottom)

deriving instance Functor CT

instance Applicative CT where
  pure = CT . pure
  (<*>) = ap

instance Monad CT where
  CT m >>= k = CT (m >>= unCT . k)

-- | This instance is a huge hack, but it works.
-- If we were serious, we should have used the flat lattice over `Tag`.
instance Lat Tag where
  bottom = error "no bottom Tag"
  k1 ⊔ k2 = if k1 /= k2 then error "k1 /= k2" else k1

instance Lat a => Lat [a] where
  bottom = []
  [] ⊔ ys = ys
  xs ⊔ [] = xs
  (x:xs) ⊔ (y:ys) = x ⊔ y : xs ⊔ ys

cCons :: Cache -> Label :-> ConCache
cCons (Cache cons _) = cons

overCons :: ((Label :-> ConCache) -> (Label :-> ConCache)) -> Cache -> Cache
overCons f (Cache cons funs) = Cache (f cons) funs

cFuns :: Cache -> Label :-> FunCache
cFuns (Cache _ funs) = funs

overFuns :: ((Label :-> FunCache) -> (Label :-> FunCache)) -> Cache -> Cache
overFuns f (Cache cons funs) = Cache cons (f funs)

updConCache :: Label -> Tag -> [CValue] -> CT ()
updConCache ell k vs = CT $ modify $ overCons $ \cons ->
  Map.singleton ell (k, vs) ⊔ cons

updFunCache ell f = CT $ modify $ overFuns $ \funs ->
  Map.singleton ell (FC Nothing f) ⊔ funs

cachedCall :: Label -> CValue -> CT CValue
cachedCall ell v = CT $ do
  FC cache f <- gets (Map.findWithDefault bottom ell . cFuns)
  let call in_ out = do
        let in_' = in_ ⊔ v      com merge all Labels that reach the lambda var ell!
        modify $ overFuns (Map.insert ell (FC (Just (in_',out)) f))
        out' <- unCT (f (return in_'))
        modify $ overFuns (Map.insert ell (FC (Just (in_',out')) f))
        return out'
  case cache of
    Just (in_,out)
      | v ⊑ in_   -> return out
      | otherwise -> call in_ out
    Nothing       -> call bottom bottom
\end{code}
%endif

\caption{0CFA}
\label{fig:cfa}
\end{figure}

\subsection{Control-flow Analysis}

In our last example, we will discuss a classic benchmark of abstract
higher-order interpreters: Control-flow analysis (CFA).
CFA calculates an approximation of which values an expression might evaluate to,
so as to narrow down the control-flow edges at application sites.
The resulting control-flow graph conservatively approximates the control-flow of
the whole program and can be used to apply classic intraprocedural analyses such
as interval analysis in a higher-order setting.

To facilitate CFA, we have to revise the |IsValue| class to pass down a
\emph{label} from allocation sites, which is to serve as the syntactic proxy of
the value's control-flow node:
\begin{spec}
type Label = String
class IsValue τ v | v -> τ where
  retCon  :: {-" \highlight{ "-}Label -> {-" {}} "-} Tag -> [τ v] -> τ v
  retFun  :: {-" \highlight{ "-}Label -> {-" {}} "-} (τ v -> τ v) -> τ v
\end{spec}
\noindent
We omit how to forward labels appropriately in |eval| and how to adjust
|IsValue| instances.

\Cref{fig:cfa} gives a rough outline of how we use this extension to define a 0CFA:%
\footnote{As before, the extract of this document contains the full, executable
definition.}
An abstract |CValue| is the usual set of |Label|s standing in for a syntactic
value.
The trace abstraction |CT| maintains as state a |Cache| that approximates the
shape of values at a particular |Label|, an abstraction of the heap.
For constructor values, the shape is simply a pair of the |Tag| and |CValue|s
for the fields.
For a lambda value, the shape is its abstract control-flow transformer, of
type |CD -> CD| (populated by |updFunCache|), plus a single point |(v1,v2)| of
its graph ($k$-CFA would have one point per contour), serving as the transformer's
summary.

At call sites in |apply|, we will iterate over each function label and attempt a
|cachedCall|.
In doing so, we look up the label's transformer and sees if the single point
is applicable for the incoming value |v|, \eg, if |v ⊑ v1|, and if so return the
cached result |v2| straight away.
Otherwise, the transformer stored for the label is evaluated at |v| and the
result is cached as the new summary.
An allocation site might be re-analysed multiple times with monotonically increasing
environment due to fixed-point iteration in |alloc|.
Whenever that happens, the point that has been cached for that allocation
site is cleared, because the function might have increased its result.
Then re-evaluating the function at the next |cachedCall| is mandatory.

Note that a |CD| transitively (through |Cache|) recurses into |CD -> CD|, thus
introducing vicious cycles in negative position.
This highlights a common challenge with instances of CFA: The obligation to
prove that the analysis actually terminates on all inputs; an obligation that we
will gloss over in this work.
\sg{Surprisingly tricky due to mutual recursion; but I'm sure this has been done
before in one form or another, hence boring.}

\subsubsection*{Examples}
The following two examples demonstrate a precise and an imprecise result,
respectively. The latter is due to the fact that both |i| and |j| flow into |x|.

< ghci> runCFA $ eval (read "let i = λx.x in let j = λy.y in i j") emp
$\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i j") emp}$
< ghci> runCFA $ eval (read "let i = λx.x in let j = λy.y in i i j") emp
$\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i i j") emp}$
\\[\belowdisplayskip]
\noindent
The |HasAlloc| instance guarantees termination for diverging programs and cyclic
data:
< ghci> runCFA $ eval (read "let ω = λx. x x in ω ω") emp
$\perform{runCFA $ eval (read "let ω = λx. x x in ω ω") emp}$
< ghci> runCFA $ eval (read "let x = let y = S(x) in S(y) in x") emp
$\perform{runCFA $ eval (read "let x = let y = S(x) in S(y) in x") emp}$

\subsection{Discussion}

By recovering usage analysis as an abstraction of |eval|, we have achieved our
main goal:
To derive a \emph{structurally-defined} static analysis approximating a property
of a \emph{small-step trace} with a simple but useful \emph{summary} mechanism
as an instance of an abstract definitional interpreter, thus sharing most of its
structure with the concrete semantics.

Our second example of type analysis, in which |PolyType|s serve as summaries
that can be instantiated at call sites, demonstrates that our approach enjoys a
broad range of applications that wouldn't be easily defined in terms of abstract
big-step interpreters.
We think that the ability to symbolically compute summaries of abstract
transformers is an inherent advantage to our denotational approach, because it
enables modular analyses; just like a type signature needs to be inferred once
and subsequently can be instantiated in client modules without needing to
re-analyse the original function.
\sg{Perhaps move tangent to Problem statement}

Finally, the example of 0CFA demonstrates that our framework can be instantiated
to perform traditional, whole-program, higher-order analysis based on
approximate call-strings.

We think that for any trace property (\ie, |IsTrace| instance), there is
an analysis that can be built on 0CFA, without the need to define a custom
summary mechanism encoded as an |IsValue| instance.
For our usage analysis, that would mean less explanation of its |Nop| summary,
but in some cases we'd lose out on precision due to the lack of modularity.

For example, it is trivial for modular usage analysis to determine that |i|
in $\Let{i}{\Lam{y}{y}}{i~x~x}$ uses |i| only once, \emph{in any context this
expression is ever embedded}.
By contrast, an approach based on $k$-CFA will have trouble with recursions
where multiple activations of |i| are live simultaneously, \ie, in the Haskell
expression

< let f n = let i y = y in if n == 0 then 0 else i (f (n-1) + 1) in f 42{-"."-}

The definition of |f| is a complicated way to define the identity function.
Nevertheless, it is evident that |i| is evaluated at most once, and
$\semusg{\wild}$ would infer this fact if we were to desugar and ANFise this
expression into an |Expr|.
On the other hand, $k$-CFA (for $k < 42$) would confuse different recursive
activations of |i|, thus conservatively attributing evaluations multiple times,
to the effect that |i| is not inferred as used at most once.
So the very simple summary-based $\semusg{\wild}$ can yield more precise results
than any usage analysis based on $k$-CFA.

We are not the first to realise this.
\citep{Mangal:14} report that 2-CFA is less precise and slower than a
summary-based approach to pointer analysis.
That is why we would strongly favour a summary-based approach where possible.
