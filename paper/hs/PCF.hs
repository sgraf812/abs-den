{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedRecordDot #-}

module PCF where

import Prelude hiding (lookup, succ, pred)
import GHC.Read
import qualified Text.Read as Read
import Data.Char
import qualified Text.ParserCombinators.ReadP as ReadP
import Control.Monad
import Control.Monad.Trans.State
import Text.Read.Lex
import Data.List (foldl')
import Expr (Name)

type Label = Int

data PCF  = VarP Name | LamP Label Name PCF | AppP Label PCF PCF | Y Name PCF
          | Zero | Succ PCF | Pred PCF | IfZero PCF PCF PCF

appPrec, lamPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1

-- | Example output: @F (λa. G) (H I) (λb. J b)@
instance Show PCF where
  showsPrec _ (VarP v)      = showString v
  showsPrec _ (AppP l f arg)  = shows l . showString "@" . (showParen True $
    showsPrec appPrec f . showString " " . showsPrec appPrec arg)
  showsPrec _ (LamP l b body) = shows l . showString "@" . (showParen True $
    showString "λ" . showString b . showString ". " . showsPrec lamPrec body)
  showsPrec p (Y x e) = showParen (p > lamPrec) $
    showString "rec " . showString x
    . showString ". " . showsPrec lamPrec e
  showsPrec _ Zero = showString "0"
  showsPrec _ (Succ e) = showString "succ(" . showsPrec lamPrec e . showString ")"
  showsPrec _ (Pred e) = showString "pred(" . showsPrec lamPrec e . showString ")"
  showsPrec p (IfZero c t e) = showParen (p > lamPrec) $
    showString "if0(" .
    showsPrec lamPrec c . showString "; " .
    showsPrec lamPrec t . showString "; " .
    showsPrec lamPrec e . showString ")"

-- | The default 'ReadP.many1' function leads to ambiguity. What a terrible API.
greedyMany, greedyMany1 :: ReadP.ReadP a -> ReadP.ReadP [a]
greedyMany p  = greedyMany1 p ReadP.<++ pure []
greedyMany1 p = (:) <$> p <*> greedyMany p

-- | This monster parses PCF exprs in the REPL etc. It parses names that start
-- with an upper-case letter as literals and lower-case names as variables.
--
-- Accepts syntax like
-- @let x = λa. g z in (λb. j b) x@
--
-- >>> read "g z" :: PCF
-- g z
--
-- >>> read "λx.x" :: PCF
-- λx. x
--
-- >>> read "λ x . rec y . x y" :: PCF
-- λx. rec y. x y
--
-- >>> read "f (if0 ( 0 ; succ( 0 ); pred( 0 ) ))" :: PCF
-- f (if0(0; succ(0); pred(0)))
--
-- >>> read "(if0 ( 0 ; succ( 0 ); pred( 0 ) )) a" :: PCF
-- (if0(0; succ(0); pred(0))) a
instance Read PCF where
  readPrec = fmap label . Read.parens $ Read.choice
    [ VarP <$> readName
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        pure (foldl' (AppP 0) f args)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for LamP
        VarP v <- Read.readPrec
        Read.Symbol "." <- Read.lexP
        LamP 0 v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "rec" <- Read.lexP
        x <- readName
        Read.Symbol "." <- Read.lexP
        e <- Read.readPrec
        pure (Y x e)
    , do
        Read.Number n <- Read.lexP
        Just m <- pure (numberToInteger n)
        guard $ m >= 0
        pure (iterate Succ Zero !! fromIntegral m)
    , Read.prec appPrec $ do
        Read.Ident "succ" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Succ e)
    , Read.prec appPrec $ do
        Read.Ident "pred" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Pred e)
    , Read.prec appPrec $ do
        Read.Ident "if0" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        c <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        t <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (IfZero c t e)
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in", "succ", "pred", "if0", "rec"])
        guard (all isAlphaNum v)
        pure v

label :: PCF -> PCF
label e = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: PCF -> State Label PCF
    lab e = case e of
      VarP n -> pure (VarP n)
      LamP _ n e -> LamP <$> next <*> pure n <*> lab e
      AppP _ f a ->
        AppP <$> next <*> lab f <*> lab a
      Y n e -> Y n <$> lab e
      Zero -> pure Zero
      Succ e -> Succ <$> lab e
      Pred e -> Pred <$> lab e
      IfZero c t e -> IfZero <$> lab c <*> lab t <*> lab e

type Env = Map.Map Name

data Event = App1 | App2 | App3 | Unroll | Other
class IsTrace τ where
  step :: Event -> τ v -> τ v
class IsValue τ v | v -> τ where
  retStuck :: τ v
  zero :: τ v
  pred :: v -> τ v
  succ :: v -> τ v
  ifZero :: v -> τ v -> τ v -> τ v
  retFun :: Label -> (v -> τ v) -> τ v
  apply :: Label -> v -> (v -> τ v)
class HasAlloc τ v | v -> τ where
  alloc :: (τ v -> τ v) -> τ (τ v)
    -- Could also have chosen to return τ v instead of τ (τ v); then this would
    -- be literally `fix`

eval :: forall τ v. (IsTrace τ, IsValue τ v, HasAlloc τ v) => PCF -> Env (τ v) -> τ v
eval e env = case e.expr of
  VarP x -> lookup e.lbl (Map.findWithDefault stuck x env)
  AppP f a -> do
    vf <- step App1 (eval f env)
    va <- step App2 (eval a env)
    apply e.lbl vf va
  LamP x body -> retFun e.lbl (\d -> step App3 (eval body (Map.insert x d env)))
  Y x f -> do
    ld <- alloc (\ld -> eval f (Map.insert x (unroll ld) env))
    unroll ld
  Zero -> zero e.lbl
  Succ e -> eval e env >>= succ
  Pred e -> eval e env >>= pred
  IfZero c t e -> eval c env >>= \v -> ifZero v (eval t env) (eval e env)

type D m = m (Value m)
data Value m = Stuck | Lit Natural | Fun (D m -> D m)
data T v = Step Event (T v) | Ret v deriving Functor

instance Applicative T where
  pure = Ret
  (<*>) = ap
instance Monad T where
  Ret a >>= k = k a
  Step e τ >>= k = Step e (τ >>= k)
instance IsTrace T where step = Step

instance Show a => Show (T a) where
  show (Step e t) = show e ++ "->" ++ show t
  show (Ret a) = "<"++show a++">"

instance Show (Value m) where
  show (Fun _) = "λ"
  show (Lit n) = show n
  show Stuck = "🗲"

instance IsTrace τ => IsValue τ (Value τ) where
  retStuck = return Stuck
  zero = return (Lit 0)
  succ (Lit n) = return (Lit (n+1))
  succ _       = retStuck
  pred (Lit 0) = return (Lit 0)
  pred (Lit n) = return (Lit (n-1))
  pred _       = retStuck
  ifZero (Lit 0) t _ = t
  ifZero (Lit _) _ e = e
  ifZero _       _ _ = retStuck
  retFun _ = return . Fun
  apply _ (Fun f) d = f d
  apply _ _       _ = retStuck

-----------------------
-- Concrete semantics
-----------------------
newtype Concrete τ v = Concrete { unConcrete :: (τ v) }
  deriving newtype (Functor,Applicative,Monad,IsTrace)

instance HasAlloc (Concrete τ) (Value (Concrete τ)) where
  alloc f = pure (fix f)
    -- As I said in the class decl, this particular type class could be just
    -- about providing a `fix`, in contrast to the Sestoft-style calculus
    -- where we use this combinator to encode different evaluation strategies

instance Show (Concrete τ v) where
  show _ = "_"

evalConc :: IsTrace τ => Expr -> τ (Value (Concrete τ))
evalConc e = unConcrete $ eval e Map.empty

--------------------
-- 0CFA+IntervalAnalysis
--------------------
-----------
-- IV
data InfiniteNumber a = NegInfinity | Number a | Infinity deriving (Eq,Ord)
data IV = IV { lower :: InfiniteNumber Natural, upper :: InfiniteNumber Natural }
  deriving Eq

instance Lat IV where
  bottom = IV Infinity NegInfinity
  IV l1 u1 ⊔ IV l2 u2 = IV (min l1 l2) (max u1 u2)

instance Show a => Show (InfiniteNumber a) where
  show NefInfinity = "-∞"
  show Infinity = "∞"
  show (Number a) = show a
instance Show IV where IV l u = "[" ++ show l ++ "," ++ show u ++ "]"

-----------
-- May-Powersets
newtype Pow a = P { unP :: Set a } deriving (Eq, Ord,Show)

instance Ord a => Lat (Pow a) where
  bottom = Pow Set.empty
  Pow l ⊔ Pow r = Pow (Set.union l r)

type CValue = Pow Label
type CD = CT CValue

-----------
-- FunCache
data FunCache = FC (Maybe (CValue, CValue)) (CValue -> CD)
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

-----------
-- Cache
data Cache = Cache { cIVs :: Label :-> IV, cFuns :: Label :-> FunCache }
  deriving Eq

instance Eq Cache where
  c1 == c2 = cFuns c1 == cFuns c2 && cIVs c1 == cIVs c2

instance Lat Cache where
  bottom = Cache Map.empty Map.empty
  c1 ⊔ c2 = Cache (f cIVs) (f cFuns)
    where
      f fld = fld c1 ⊔ fld c2

----------
-- CT (the trace monad)
newtype CT a = CT { unCT :: State Cache a } deriving (Functor,Applicative,Monad)
instance IsTrace CT where step _ = id
instance IsValue CT CValue where
  retStuck = return bottom
  zero =
  retFun ell f = do updCacheFun ell f; return (P (Set..singleton ell))
  apply (Pow ells) d = d >>= \v ->
    lub <$> traverse (\ell -> cachedCall ell v) (Set.toList ells)
instance HasAlloc CT CValue where
  alloc f = fmap return (go bottom)
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- f (return v)
        cache' <- CT get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- f (return v'); if v' /= v'' then error "blah" else return v' } else go v'

runCFA :: CT CValue -> CValue
runCFA (CT m) = evalState m (Cache bottom bottom)

overIVs :: ((Label :-> IV) -> (Label :-> IV)) -> Cache -> Cache
overIVs f (Cache ivs funs) = Cache (f ivs) funs

overFuns :: ((Label :-> FunCache) -> (Label :-> FunCache)) -> Cache -> Cache
overFuns f (Cache ivs funs) = Cache ivs (f funs)

updCacheIV :: Label -> IV -> CT ()
updCacheIV ell iv = CT $ modify $ overIVs $ \ivs ->
  Map.singleton ell iv ⊔ ivs

updCacheFun :: Label -> (CD -> CD) -> CT ()
updCacheFun ell f = CT $ modify $ overFuns $ \funs ->
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

{-
type AbsD = CFA (Pow SynVal)
data SynVal = SomeLit | SomeLam Label (AllEqual (AbsD -> AbsD))
  deriving (Eq, Ord)
instance Show SynVal where
  show SomeLit = "N"
  show (SomeLam l _) = show l

newtype Pow a = Pow { unPow :: Set.Set a }
  deriving (Eq, Ord)
showSep :: ShowS -> [ShowS] -> ShowS
showSep _   [] = id
showSep _   [s] = s
showSep sep (s:ss) = s . sep . showString " " . showSep sep ss
instance Show a => Show (Pow a) where
  showsPrec _ (Pow s) =
    showString "{" . showSep (showString ", ") (map shows (Set.toList s)) . showString "}"
instance Ord a => PreOrd (Pow a) where
  l ⊑ r = l ⊔ r == r
instance Ord a => LowerBounded (Pow a) where
  bottom = Pow Set.empty
instance Ord a => Complete (Pow a) where
  Pow l ⊔ Pow r = Pow (Set.union l r)

type Calls = Map.Map Label (Pow SynVal) -- Application site label :-> Potential labels of lambdas applied

data CFA a = CFA Calls a
  deriving (Eq, Ord, Functor)
instance Show a => Show (CFA a) where
  show (CFA calls a) = show calls ++ show a
instance PreOrd a => PreOrd (CFA a) where
  CFA l1 l2 ⊑ CFA r1 r2 = l1 ⊑ r1 && l2 ⊑ r2
instance LowerBounded a => LowerBounded (CFA a) where
  bottom = CFA bottom bottom
instance Complete a => Complete (CFA a) where
  CFA l1 l2 ⊔ CFA r1 r2 = CFA (l1 ⊔ r1) (l2 ⊔ r2)

instance Applicative CFA where
  pure = CFA Map.empty
  (<*>) = ap
instance Monad CFA where
  CFA c1 a >>= k = case k a of
    CFA c2 b -> CFA (c1 ⊔ c2) b
instance IsTrace CFA where

addCall :: Label -> Pow SynVal -> CFA ()
addCall app_lbl head_lams =
  CFA (Map.singleton app_lbl head_lams) ()

instance IsValue CFA (Pow SynVal) where
  stuck = return $ Pow Set.empty
  zero = return $ Pow (Set.singleton SomeLit)
  succ _ = return $ Pow (Set.singleton SomeLit)
  pred _ = return $ Pow (Set.singleton SomeLit)
  ifZero _ t e = (⊔) <$> t <*> e
  retFun l f = do
    return (Pow (Set.singleton (SomeLam l (AE f))))
  apply l head_lams arg = do
    addCall l head_lams
    let do_one SomeLit = stuck
        do_one (SomeLam _l (AE f)) = f arg
    vs <- traverse do_one (Set.toList (unPow head_lams))
    return (lub vs)

----------------------
-- Caching
----------------------

data FunCache a b = FC (LMap.Map a b) (FunCache a b -> a -> b)
instance (Show a, Show b) => Show (FunCache a b) where
  show (FC cache _) = show cache
instance (Eq a, Eq b) => Eq (FunCache a b) where
  FC l _ == FC r _ = l == r
instance (Ord a, Ord b) => Ord (FunCache a b) where
  compare (FC l _) (FC r _) = compare l r
instance (Ord a, PreOrd b) => PreOrd (FunCache a b) where
  FC l _ ⊑ FC r _ = l ⊑ r
instance (Ord a, LowerBounded b) => LowerBounded (FunCache a b) where
  bottom = FC LMap.empty (const bottom)
instance (Ord a, Complete b) => Complete (FunCache a b) where
  FC l1 l2 ⊔ FC r1 r2 =
    -- naive recaching: recompute all cached points with new_fun
    -- Thanks to laziness, this isn't too naive, actually
    let new_fun   = l2 ⊔ r2
        old_cache = l1 ⊔ r1
        old_fc    = FC old_cache new_fun -- might be out of date
        new_cache = LMap.mapWithKey (\a _ -> trace "test" new_fun old_fc a) old_cache
    in FC new_cache new_fun

applyFunCache :: (Ord a, LowerBounded b) => FunCache a b -> a -> (FunCache a b, b)
applyFunCache fc@(FC cache fun) a = case LMap.lookup a cache of
  Just b  -> (fc, b)
  Nothing ->
    -- Note that we insert bottom into the cache before calling fun
    -- and then update the cache again with the result.
    -- It seems that this initialisation is necessary to guarantee
    -- termination; otherwise we get a <<loop>> (in case taking fc1=fc2)
    -- or an actually infinite loop (taking fc1=fc), for example in
    --   rec f. λx. f x
    let fc1 = FC (LMap.insert a bottom cache) fun
        b = fun fc1 a
        fc2 = FC (LMap.insert a b cache) fun
    in (fc2, b)

type Lams = Map.Map Label (FunCache AbsD AbsD) -- LamP label :-> join of all activations of the lambda (memoised and comparable)
newtype CachedCFA a = CCFA { unCached :: StateT Lams CFA a }
  deriving (Functor, Applicative, Monad)

instance MonadAlloc CFA (Pow SynVal) where
  alloc f = pure $ Identity $ kleeneFix (f . Identity)

addFun :: Label -> (CachedCFA (Pow SynVal) -> CachedCFA (Pow SynVal)) -> CachedCFA ()
addFun l f = CCFA $ do
  lams <- get
  let
    f' :: FunCache AbsD AbsD -> AbsD -> AbsD
    f' fc a = evalStateT (unCached (f (CCFA (lift a)))) (Map.insert l fc lams)
  modify (Map.insertWith (⊔) l (FC bottom f'))

instance MonadTrace CachedCFA where
  type L CachedCFA = Identity
  unroll (Identity m) = m
  lookup _ = id
  app1 = id
  app2 = id
  app3 = id

callWithCache :: Label -> CachedCFA (Pow SynVal) -> CachedCFA (Pow SynVal)
callWithCache l (CCFA d) = CCFA $ StateT $ \lams ->
  let cache = Map.findWithDefault bottom l lams in
  case applyFunCache cache (evalStateT d lams) of
    (cache', res) -> do
      v <- res
      return (v, Map.insert l cache' lams)

liftCached :: CFA a -> CachedCFA a
liftCached = CCFA . lift

instance IsValue CachedCFA (Pow SynVal) where
  stuck = liftCached stuck
  zero = liftCached zero
  succ = liftCached . succ
  pred = liftCached . pred
  ifZero _ t e = (⊔) <$> t <*> e -- same impl, but more caching
  retFun l f = do
    addFun l f
    liftCached $ retFun l (runCached . f . liftCached)
  apply l head_lams arg = do
    liftCached $ addCall l head_lams
    let do_one SomeLit = stuck
        do_one (SomeLam l _f) = callWithCache l arg
    vs <- traverse do_one (Set.toList (unPow head_lams))
    return (lub vs)

instance MonadAlloc CachedCFA (Pow SynVal) where
  alloc f = CCFA $ do
    lams_start <- get
    let wrap = Identity . CCFA . lift
    let
      (d,lams') = kleeneFix $ \(d :: CFA (Pow SynVal), lams :: Lams) ->
        let lams1 = if lams ⊑ lams_start then lams_start else lams in
        let CFA calls (v,lams2) = runStateT (unCached (f (wrap d))) lams1 in
        (CFA calls v, lams2)
    put lams'
    pure (wrap d)

runCached :: CachedCFA a -> CFA a
runCached (CCFA s) = evalStateT s Map.empty

execCFA :: CFA (Pow SynVal) -> Calls
execCFA (CFA m _) = m

evalCFA :: CFA (Pow SynVal) -> Pow SynVal
evalCFA (CFA _ a) = a

execCCFA :: CachedCFA (Pow SynVal) -> Calls
execCCFA = execCFA . runCached

evalCCFA :: CachedCFA (Pow SynVal) -> Pow SynVal
evalCCFA = evalCFA . runCached

exec0CFA :: LExpr -> Calls
exec0CFA e = execCFA $ eval e Map.empty

eval0CFA :: LExpr -> Pow SynVal
eval0CFA e = evalCFA $ eval e Map.empty

exec0CachedCFA :: LExpr -> Calls
exec0CachedCFA e = execCCFA $ eval e Map.empty

eval0CachedCFA :: LExpr -> Pow SynVal
eval0CachedCFA e = evalCCFA $ eval e Map.empty
-}
