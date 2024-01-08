%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE LambdaCase #-}

module Abstractions where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import qualified Data.List as List
import Exp
import Order
import Interpreter
import {-# SOURCE #-} Sergey14

root = call `seq` anyCtx -- Suppress redundant import warning
\end{code}
%endif

\section{Abstractions}
\label{sec:abstractions}

\begin{figure}
\begin{spec}
class Eq a => Lat a where bottom :: a; (⊔) :: a -> a -> a;
lub :: Lat a => [a] -> a; kleeneFix :: Lat a => (a -> a) -> a
kleeneFix f = go bottom where go x = let x' = f x in if x' ⊑ x then x' else go x'
instance (Ord k, Lat v) => Lat (k :-> v) where bottom = emp; (⊔) = Map.unionWith (⊔)
\end{spec}
\caption{Order theory and Kleene fixpoint}
\label{fig:lat}
\end{figure}

\subsection{Usage analysis}
\label{sec:usage-analysis}

\begin{figure}
\begin{minipage}{0.65\textwidth}
\begin{code}
data U = U0 | U1 | Uω; instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
{-" \fi "-}
data UT a = Uses (Name :-> U) a

instance Trace (UT v) where
  step (Lookup x)  (Uses φ a)  = Uses (φ + ext emp x U1) a
  step _           τ           = τ
\end{code}
\end{minipage}%
\begin{minipage}{0.35\textwidth}
\begin{code}
instance Monad UT where
  return a = Uses emp a
  Uses φ1 a >>= k
    |  Uses φ2 b <- k a
    =  Uses (φ1+φ2) b
\end{code}
\end{minipage}
\caption{|Trace| instance for usage analysis}
\label{fig:usg-abs}
\end{figure}

\begin{figure}
\begin{minipage}{0.51\textwidth}
\begin{code}
data UValue = Nop; type UD = UT UValue

nopD :: UD
nopD = Uses emp Nop

manify :: UD -> UD
manify (Uses φ Nop) = Uses (φ+φ) Nop

instance Lat UD where
  bottom = nopD
  Uses φ1 _ ⊔ Uses φ2 _ = Uses (φ1 ⊔ φ2) Nop
\end{code}
\end{minipage}%
\begin{minipage}{0.49\textwidth}
\begin{code}
instance Domain UD where
  stuck                                  = nopD
  fun {-" \iffalse "-}_{-" \fi "-} f     = manify (f nopD)
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = manify (foldr (>>) nopD ds)
  apply d a                              = manify a >> d
  select d fs                            =
    d >> lub  [  f (replicate (conArity k) nopD)
              |  (k,f) <- Map.assocs fs ]

instance HasBind UD where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = body (kleeneFix rhs)
\end{code}
\end{minipage}
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

instance (Ord k, Plussable v) => Plussable (k :-> v) where
  (+) = Map.unionWith (+)

instance Show a => Show (UT a) where
  show (Uses φ _) = show φ

instance Applicative UT where
  pure a = Uses emp a
  (<*>) = ap

instance Show UValue where
  show Nop = ""
\end{code}
%endif
\caption{Naïve usage analysis via |Domain| and |HasBind|}
\label{fig:abs-usg}
\end{figure}

The gist of usage analysis is that it collects upper bounds for the number of
$\LookupT$ transitions per variable.
We can encode this intuition in the custom trace type |UT| in \Cref{fig:usg-abs}
that will take the place of |T|.
|UT| aggregates the number of |Lookup x| transitions per variable |x| in a usage
environment |Name :-> U|, with the matching |Monad| and |Trace| instances.
An |U| abstracts an upper bound on the number of such |Lookup| transitions,
where |U0| means ``at most 0 times'' (\ie, dead) and |U1| means ``at most 1 times''.
|Uω| is the top element of the lattice defined by the total ordering |U0 ⊏ U1
⊏ Uω| and can be read as ``at most ω times'', where $ω$ is the first limit
ordinal.
The definitioin of |(+)| on |U| coincides with |(⊔)|, except for carrying over
|U1 + U1 = Uω|, so any number of lookups beyond $1$ goes straight to $ω$.
Both |(+)| and |(⊔)| are lifted pointwise to |Name :-> U|.

If we had no interest in a terminating analysis, we could already make do
with the induced \emph{semantic usage abstraction} |D (ByName UT)|:

< ghci> eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)
$\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)}$
\\[\belowdisplayskip]
\noindent
This analysis amounts to running the concrete semantics and then folding the
trace into a |UT|; it is what the static analysis is supposed to approximate.
Of course, this will diverge whenever the object program diverges.
Perhaps interestingly, we have not needed any order theory so far, because the
abstraction is a precise fold over the program trace, thanks to the concrete
|Value|s manipulated.

If we want to assess usage cardinality statically, we have to find a more abstract
representation of |Value|.
\Cref{fig:abs-usg} gives one such candidate |UValue|, a type containing a single
inhabitant |Nop|, so it is the crudest possible summary of a concrete |Value|.
The |Domain| instance is reponsible for implementing the summary mechanism.
|stuck|,|fun| and |con| map from values to summarised representation, and
|apply| and |select| encode the concretisation of |Nop| in terms of the abstract
domain |UD|.

When a |d| is |apply|'d to an argument |a|, the result is that of
evaluating |a| many times (note that it is enough to evaluate twice in
|U|, as in |manify|) as well as |d|, roughly corresponding to the $x ∈ Γ$
premise of the \textsc{App} rule in \Cref{fig:deadness}.
When a |d| is |select|ed, the result is that of evaluating the case
alternatives |fs| with |nopD| for field denotations of the corresponding
constructor, then returning the least upper bound |lub| of all alternatives.
Such a |nopD| is simply an inert denotation that does not contribute any uses
itself, but crucially distributes the |Nop| value to field accesses inside |fs|,
leading to conservative approximation in turn.

Dually, when a constructor application is returned in |con|, all the fields
are evaluated eagerly, and many times, conservatively approximating potential
use of any of the fields in the future.
This justifies passing |nopD| for field denotations in |select|; the fields have
already been ``squeezed dry'' in |con|.
Likewise, when returning a function in |fun|, that function is ``squeezed
dry'' by passing it a |nopD| and |manify|ing the result, thus accounting for
uses inside the function body at any potential call site.
(Recall that uses of the argument at the call site is handled by |apply|.)
This bears a strong resemblence to rule \textsc{Lam} of \Cref{fig:deadness},
where analysis of the body assumes that the argument is dead in everything
(``squeezed dry'') when adding $\px$ to $Γ$.

The following ``substitution lemma'' formalises this notion of ``sequeezing
dry'' a |d|, and it is material in proving the summary mechanism correct in
\Cref{sec:soundness}:
\begin{lemmarep}[Usage squeezing]
\label{thm:usage-squeezing}
|eval e (ext ρ x d) ⊑ manify d >> eval e (ext ρ x nopD)|.
\end{lemmarep}
\begin{proof}
By induction on |e|.
\begin{itemize}
  \item \textbf{Case} |Var|: By assumption.
  \item \textbf{Case} |Lam|: By induction hypothesis.
  \item \textbf{Case} |App e y|:
    The case |x /= y| is a simple application of the induction hypothesis.
    Otherwise, we might evaluate |x| both as part of evaluating |e| and in the
    lambda body it produces.
    Fortunately, we may collapse |manify d >> manify d = manify d| as often as
    needed, and |manify nopD >>| is the identity function.
    Thus we can show
    \begin{spec}
      eval (App e x) (ext ρ x d)
    = {- Definition of |eval| -}
      apply (eval e (ext ρ x d)) d
    = {- Definition of |apply| -}
      manify d >> eval e (ext ρ x d)
    ⊑ {- Induction hypothesis -}
      manify d >> manify d >> eval e (ext ρ x nopD)
    ⊑ {- Collapse |manify d|, expand |d = manify nopD >> d| -}
      manify nopD >> manify d >> eval e (ext ρ x nopD)
    = {- Definition of |apply| -}
      manify d >> apply (eval e (ext ρ x nopD)) nopD
    = {- Definition of |eval| -}
      manify d >> eval (App e x) (ext ρ x nopD)
    \end{spec}
  \item \textbf{Case} |Con|, |Case|:
    Similar; need to collapse |manify d| after applying the induction
    hypothesis.
\end{itemize}
\end{proof}

The final key to a terminating definition is in swapping out the fixpoint
combinator via the |HasBind| instance for |UValue| that computes an
order-theoretic Kleene fixpoint (\cf \Cref{fig:lat}) instead of |fix| (which
only works for a guarded recursive |f|).
The Kleene fixpoint exists by monotonicity and finiteness of |UD|, as we will
make formal in \Cref{sec:soundness}.

\begin{table}
\begin{tabular}{clll}
\toprule
\# & |d|             & |e|                                               & |eval e emp :: d| \\
\midrule
(1)        & |UD|            & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$ & $\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: UD}$ \\
(2)        & |D (ByName UT)| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp :: D (ByName UT)}$ \\
(3)        & |UD|            & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp :: UD}$ \\
(4)        & |D (ByName UT)| & $\Let{z}{Z()}{\Case{Z()}{Z() → Z(); S(n) → z}}$   & $\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp  :: D (ByName UT)}$ \\
(5)        & |UD|            & $\Let{z}{Z()}{\Case{Z()}{Z() → Z(); S(n) → z}}$   & $\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp :: UD}$ \\
\bottomrule
\end{tabular}
\caption{Comparing usage analysis |UD| to the semantics usage abstraction |D (ByName UT)|.}
\label{fig:usage-examples}
\end{table}

\subsubsection*{Examples}
Our naïve usage analysis can yield the same result as the semantic usage
abstraction, as can be seen for example (1) of \Cref{fig:usage-examples}.
The results will be more approximate when summaries are involved, however, as
the contrasting examples (2)-(5) point out.

\subsection{Type Analysis}

\begin{figure}
\begin{code}
data Type = Type :->: Type | TyConApp TyCon [Type] | TyVar Name | Wrong
data PolyType = PT [Name] Type; data TyCon = {-" ... \iffalse "-} BoolTyCon | NatTyCon | OptionTyCon | PairTyCon {-" \fi "-}

type Constraint = (Type, Type); type Subst = Name :-> Type
data Cts a = Cts (StateT (Set Name,Subst) Maybe a)
emitCt :: Constraint -> Cts ();                   freshTyVar :: Cts Type
instantiatePolyTy :: PolyType -> Cts Type; ^^ ^^  generaliseTy :: Cts Type -> Cts PolyType
closedType :: Cts PolyType -> PolyType {-" \iffalse "-}
closedType d = runCts (generaliseTy $ d >>= instantiatePolyTy)
{-" \fi "-}

instance Trace (Cts v) where step _ = id
instance Domain (Cts PolyType) where stuck = return (PT [] Wrong); {-" ... \iffalse "-}
                                     fun {-" \iffalse "-}_{-" \fi "-} f = do
                                       arg <- freshTyVar
                                       res <- f (return (PT [] arg)) >>= instantiatePolyTy
                                       return (PT [] (arg :->: res))
                                     con {-" \iffalse "-}_{-" \fi "-} k ds = do
                                       con_app_ty <- instantiateCon k
                                       arg_tys <- traverse (>>= instantiatePolyTy) ds
                                       res_ty <- freshTyVar
                                       emitCt (con_app_ty, foldr (:->:) res_ty arg_tys)
                                       return (PT [] res_ty)
                                     apply dv da = do
                                       fun_ty <- dv >>= instantiatePolyTy
                                       arg_ty <- da >>= instantiatePolyTy
                                       res_ty <- freshTyVar
                                       emitCt (fun_ty, arg_ty :->: res_ty)
                                       return (PT [] res_ty)
                                     select dv fs = case Map.assocs fs of
                                       []            -> stuck
                                       fs@((k,_):_)  -> do
                                         con_ty <- dv >>= instantiatePolyTy
                                         res_ty <- snd . splitFunTys <$> instantiateCon k
                                         let TyConApp tc tc_args = res_ty
                                         emitCt (con_ty, res_ty)
                                         ks_tys <- enumerateCons tc tc_args
                                         tys <- forM ks_tys $ \(k,tys) ->
                                           case List.find (\(k',_) -> k' == k) fs of
                                             Just (_,f) -> f (map (fmap (PT [])) tys)
                                             _          -> stuck
                                         traverse instantiatePolyTy tys >>= \case
                                           []      -> stuck
                                           ty:tys' -> traverse (\ty' -> emitCt (ty,ty')) tys' >> return (PT [] ty)

{-" \fi "-}
instance HasBind (Cts PolyType) where
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = generaliseTy (do
    rhs_ty <- freshTyVar
    rhs_ty' <- rhs (return (PT [] rhs_ty)) >>= instantiatePolyTy
    emitCt (rhs_ty, rhs_ty')
    return rhs_ty) >>= body . return

\end{code}
%if style == newcode
\begin{code}
deriving instance Eq TyCon
deriving instance Enum TyCon
deriving instance Bounded TyCon
deriving instance Eq Type
deriving instance Functor Cts

runCts :: Cts PolyType -> PolyType
runCts (Cts m) = case evalStateT m (Set.empty, emp) of Just ty -> ty; Nothing -> PT [] Wrong

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

To demonstrate the flexibility of our approach, we have implemented
Hindley-Milner-style type analysis including Let generalisation as an
instance of our abstract denotational interpreter.
The gist is given in \Cref{fig:type-analysis}; we omitted large parts of the
implementation and the |Domain| instance for space reasons.
While the full implementation can be found in the extract generated from this
document, the |HasBind| instance is sufficiently exemplary of the approach.

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

While the operational detail offered by |Trace| is ignored by |Cts|, all the
pieces fall together in the implementation of |bind|, where we see yet another
domain-specific fixpoint strategy:
The knot is tied by calling the iteratee |rhs| with a fresh unification variable
type |rhs_ty| of the shape $α_1$.
The result of this call in turn is instantiated to a non-|PolyType| |rhs_ty'|,
perhaps turning a type-scheme $\forall α_2.\ \mathtt{option}\;(α_2 \rightarrow
α_2)$ into the shape $\mathtt{option}\;(α_3 \rightarrow α_3)$ for fresh $α_3$.
Then a constraint is emitted to unify $α_1$ with
$\mathtt{option}\;(α_3 \rightarrow α_3)$.
Ultimately, the type |rhs_ty| is returned and generalised to $\forall α_3.\
\mathtt{option}\;(α_3 \rightarrow α_3)$, because $α_3$ is not a |Name| in use
before the call to |generaliseTy| (and thus it couldn't have possibly leaked
into the range of the ambient type context).
The generalised |PolyType| is then used when analysing the |body|.

\begin{table}
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |closedType (eval e emp)| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{i~i~i~i~i~i}$                  & $\perform{closedType $ eval (read "let i = λx.x in i i i i i i") emp}$ \\
(2) & $\Lam{x}{\Let{y}{x}{y~x}}$                          & $\perform{closedType $ eval (read "λx. let y = x in y x") emp}$ \\
(3) & $\Let{i}{\Lam{x}{x}}{\Let{o}{\mathit{Some}(i)}{o}}$ & $\perform{closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp}$ \\
(4) & $\Let{x}{x}{x}$                                     & $\perform{closedType $ eval (read "let x = x in x") emp}$ \\
\bottomrule
\end{tabular}
\caption{Examples for type analysis.}
\label{fig:type-examples}
\end{table}

\subsubsection*{Examples}
Let us again conclude with some examples in \Cref{fig:type-examples}.
Example (1) demonstrates repeated instantiation and generalisation.
Example (2) shows that let generalisation does not accidentally generalise the
type of |y|.
Example (3) shows an example involving data types and the characteristic
approximation to higher-rank types, and example (4) shows that type inference
for diverging programs works as expected.

\begin{figure}
\begin{code}
data Pow a = P (Set a); type CValue = Pow Label
type ConCache = (Tag, [CValue]); data FunCache = FC (Maybe (CValue, CValue)) (CD -> CD)
data Cache = Cache (Label :-> ConCache) (Label :-> FunCache)
data CT a = CT (State Cache a); type CD = CT CValue; runCFA :: CD -> CValue

updFunCache :: Label -> (CD -> CD) -> CT (); cachedCall :: Label -> CValue -> CD

instance HasBind CD where{-" ... \iffalse "-}
  bind {-" \iffalse "-}_{-" \fi "-} rhs body = go bottom >>= body . return
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- rhs (return v)
        cache' <- CT get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- rhs (return v'); if v' /= v'' then error "blah" else return v' } else go v'
{-" \fi "-}; instance Trace (CT v) where step _ = id
instance Domain CD where
  fun ell f = do updFunCache ell f; return (P (Set.singleton ell))
  apply dv da = dv >>= \(P ells) -> da >>= \a -> lub <$> traverse (\ell -> cachedCall ell a) (Set.toList ells)
  {-" ... \iffalse "-}
  stuck = return bottom
  con ell k ds = do vs <- sequence ds; updConCache ell k vs; return (P (Set.singleton ell))
  select dv fs = do
    P ells <- dv
    cache <- CT get
    vals <- sequence [ f (map return vs) | ell <- Set.toList ells, Just (k',vs) <- [Map.lookup ell (cCons cache)]
                     , (k,f) <- Map.assocs fs, k == k' ]
    return (lub vals)
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
\vspace{-1.5em}
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

To facilitate CFA, we have to revise the |Domain| class to pass down a
\emph{label} from allocation sites, which is to serve as the syntactic proxy of
the value's control-flow node:
\begin{spec}
type Label = String
class Domain d where
  con  :: {-" \highlight{ "-}Label -> {-" {}} "-} Tag -> [d] -> d
  fun  :: {-" \highlight{ "-}Label -> {-" {}} "-} (d -> d) -> d
\end{spec}
\noindent
We omit how to forward labels appropriately in |eval| and how to adjust
|Domain| instances.

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
environment due to fixpoint iteration in |bind|.
Whenever that happens, the point that has been cached for that allocation
site is cleared, because the function might have increased its result.
Then re-evaluating the function at the next |cachedCall| is mandatory.

Note that a |CD| transitively (through |Cache|) recurses into |CD -> CD|, thus
introducing vicious cycles in negative position.
This highlights a common challenge with instances of CFA: The obligation to
prove that the analysis actually terminates on all inputs; an obligation that we
will gloss over in this work.

\begin{table}
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |runCFA (eval e emp)| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i j") emp}$ \\
(2) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$ & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i i j") emp}$ \\
(3) & $\Let{ω}{\Lam{x}{x~x}}{ω~ω}$                      & $\perform{runCFA $ eval (read "let ω = λx. x x in ω ω") emp}$ \\
(4) & $\Let{x}{\Let{y}{S(x)}{S(y)}}{x}$                 & $\perform{runCFA $ eval (read "let x = let y = S(x) in S(y) in x") emp}$ \\
\bottomrule
\end{tabular}
\caption{Examples for control-flow analysis.}
\label{fig:cfa-examples}
\end{table}

\subsubsection*{Examples}
The first two examples of \Cref{fig:cfa-examples} demonstrate a precise and an
imprecise result, respectively. The latter is due to the fact that both |i| and
|j| flow into |x|.
Examples (3) and (4) show that the |HasBind| instance guarantees termination for
diverging programs and cyclic data:

\subsection{Discussion}

By recovering usage analysis as an abstraction of |eval|, we have achieved our
main goal:
To derive a \emph{structurally-defined} static analysis approximating a property
of a \emph{small-step trace} with a simple but useful summary mechanism as an
instance of an abstract definitional interpreter, thus sharing most of its
structure with the concrete semantics.

Our second example of type analysis, in which |PolyType|s serve as summaries
that can be instantiated at call sites, demonstrates that our approach enjoys a
broad range of applications that wouldn't be easily defined in terms of abstract
big-step interpreters due to their inherent lack of modularity.

Finally, the example of 0CFA demonstrates that our framework can be instantiated
to perform traditional, whole-program, higher-order analysis based on
approximate call strings.

\subsection{Bonus: Higher-order Cardinality Analysis}

In the style of \citet{cardinality-ext}.
\sg{Flesh out, move to Appendix or remove. I left this section in for Ilya to
have a look. |call 2| means ``assume an evaluation context that applies 2
arguments'', |anyCtx| means ``evaluate in any evaluation context'' (top).}

\begin{tabular}{clll}
\toprule
\#  & |f|      & |e|                                                                    & |f e| \\
\midrule
(1) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$                      & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j j"}$ \\
(2) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$                        & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j"}$ \\
(3) & |call 2| & $\Let{i}{\Lam{x}{x}}{i}$                                               & $\perform{call 2 "let i = λx.x in i"}$ \\
(4) & |call 2| & $\Let{\mathit{const}}{\Lam{x}{\Lam{y}{y}}}{\mathit{const}}$            & $\perform{call 2 "let const = λx.λy.y in const"}$ \\
(5) & |call 2| & $\Let{f}{\Lam{a}{\Lam{g}{\Let{t}{g~a}{t~t}}}}{\mathit{f}}$ & $\scriptstyle \perform{call 2 "let f = λa. λg. let t = g a in t t in f"}$ \\
%(6) & |anyCtx| & $\Let{z}{Z()}{\Let{o}{S(z)}{\Let{\mathit{plus}}{\Lam{a}{\Lam{b}{...S(\mathit{plus}~(a-1)~b)...}}}{\mathit{plus}~z~o}}}$
%               & $\perform{anyCtx "let z = Z() in let o = S(z) in let plus = λa.λb. case a of { Z() -> b; S(n) -> let plusn = plus n b in S(plusn) } in plus z o"}$ \\
\bottomrule
\end{tabular}
