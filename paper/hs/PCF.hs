{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE FunctionalDependencies #-}

module PCF where

import Prelude hiding (lookup, succ, pred)
import GHC.Read
import qualified Text.Read as Read
import Data.Char
import qualified Text.ParserCombinators.ReadP as ReadP
import Control.Monad
import Control.Monad.Trans.State
import qualified Text.Read.Lex as Lex
import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Order
import Debug.Trace
import Data.Function (fix)

type Label = Int
type Name = String

data ExprF r
  = Var Name
  | Lam Name r
  | App r r
  | Y Name r
  | Zero
  | Succ r
  | Pred r
  | IfZero r r r
  deriving (Show, Functor)

data Exp = Exp { lbl :: Label, expr :: ExprF Exp }

appPrec, lamPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1

-- | Example output: @F (λa. G) (H I) (λb. J b)@
instance Show Exp where
  showsPrec _ (Exp l (Var v))      = showString v
  showsPrec _ (Exp l (App f arg))  = shows l . showString "@" . (showParen True $
    showsPrec appPrec f . showString " " . showsPrec appPrec arg)
  showsPrec _ (Exp l (Lam b body)) = shows l . showString "@" . (showParen True $
    showString "λ" . showString b . showString ". " . showsPrec lamPrec body)
  showsPrec p (Exp l (Y x e)) = showParen (p > lamPrec) $
    showString "rec " . showString x
    . showString ". " . showsPrec lamPrec e
  showsPrec _ (Exp l Zero) = showString "0"
  showsPrec _ (Exp l (Succ e)) = showString "succ(" . showsPrec lamPrec e . showString ")"
  showsPrec _ (Exp l (Pred e)) = showString "pred(" . showsPrec lamPrec e . showString ")"
  showsPrec p (Exp l (IfZero c t e)) = showParen (p > lamPrec) $
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
-- >>> read "g z" :: Exp
-- 1@(g z)
--
-- >>> read "λx.x" :: Exp
-- 1@(λx. x)
--
-- >>> read "λ x . rec y . x y" :: Exp
-- 1@(λx. rec y. 3@(x y))
--
-- >>> read "f (if0 ( 0 ; succ( 0 ); pred( 0 ) ))" :: Exp
-- 1@(f (if0(0; succ(0); pred(0))))
--
-- >>> read "(if0 ( 0 ; succ( 0 ); pred( 0 ) )) a" :: Exp
-- 1@((if0(0; succ(0); pred(0))) a)
instance Read Exp where
  readPrec = fmap label . Read.parens $ Read.choice
    [ Exp 0 . Var <$> readName
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        pure (foldl' (\l r -> Exp 0 (App l r)) f args)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for Lam
        Exp _ (Var v) <- Read.readPrec
        Read.Symbol "." <- Read.lexP
        Exp 0 . Lam v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "rec" <- Read.lexP
        x <- readName
        Read.Symbol "." <- Read.lexP
        e <- Read.readPrec
        pure (Exp 0 $ Y x e)
    , do
        Read.Number n <- Read.lexP
        Just m <- pure (Lex.numberToInteger n)
        guard $ m >= 0
        pure (iterate (Exp 0 . Succ) (Exp 0 Zero) !! fromIntegral m)
    , Read.prec appPrec $ do
        Read.Ident "succ" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Exp 0 $ Succ e)
    , Read.prec appPrec $ do
        Read.Ident "pred" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Exp 0 $ Pred e)
    , Read.prec appPrec $ do
        Read.Ident "if0" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        c <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        t <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Exp 0 $ IfZero c t e)
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in", "succ", "pred", "if0", "rec"])
        guard (all isAlphaNum v)
        pure v

label :: Exp -> Exp
label e = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: Exp -> State Label Exp
    lab e = do
      l <- next
      e' <- case e.expr of
        Var n -> pure (Var n)
        Lam n e -> Lam n <$> lab e
        App f a ->
          App <$> lab f <*> lab a
        Y n e -> Y n <$> lab e
        Zero -> pure Zero
        Succ e -> Succ <$> lab e
        Pred e -> Pred <$> lab e
        IfZero c t e -> IfZero <$> lab c <*> lab t <*> lab e
      return (Exp l e')

type Env = Map.Map Name

data Event = App1 | App2 | App3 | Unroll | Lookup deriving Show
class Monad τ => IsTrace τ where
  step :: Event -> τ v -> τ v
class IsValue τ v | v -> τ where
  retStuck :: τ v
  retZero :: τ v
  pred :: v -> τ v
  succ :: v -> τ v
  ifZero :: v -> τ v -> τ v -> τ v
  retFun :: Label -> (v -> τ v) -> τ v
  apply :: v -> (v -> τ v)
class HasAlloc τ v | v -> τ where
  alloc :: (τ v -> τ v) -> τ (τ v)
    -- Could also have chosen to return τ v instead of τ (τ v); then this would
    -- be literally `fix`

eval :: forall τ v. (IsTrace τ, IsValue τ v, HasAlloc τ v) => Exp -> Env (τ v) -> τ v
eval e env = case e.expr of
  Var x -> step Lookup (Map.findWithDefault retStuck x env)
  App f a -> do
    vf <- step App1 (eval f env)
    va <- join $ step App2 (alloc $ \_d -> eval a env)
    apply vf va
  Lam x body -> retFun e.lbl (\d -> step App3 (eval body (Map.insert x (return d) env)))
  Y x f -> do
    ld <- alloc (\ld -> eval f (Map.insert x (step Unroll ld) env))
    step Unroll ld
  Zero -> retZero
  Succ e -> eval e env >>= succ
  Pred e -> eval e env >>= pred
  IfZero c t e -> eval c env >>= \v -> ifZero v (eval t env) (eval e env)

type D m = m (Value m)
data Value m = Stuck | Lit Integer | Fun (Value m -> D m)
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
  retZero = return (Lit 0)
  succ (Lit n) = return (Lit (n+1))
  succ _       = retStuck
  pred (Lit n) = return (Lit (n-1))
  pred _       = retStuck
  ifZero (Lit 0) t _ = t
  ifZero (Lit _) _ e = e
  ifZero _       _ _ = retStuck
  retFun _ = return . Fun
  apply (Fun f) d = f d
  apply _       _ = retStuck

-----------------------
-- Concrete semantics
-----------------------
newtype Concrete τ v = Concrete { unConcrete :: (τ v) }
  deriving newtype (Functor,Applicative,Monad,IsTrace)

instance IsTrace τ => HasAlloc (Concrete τ) (Value (Concrete τ)) where
  alloc f = pure (fix f)
    -- As I said in the class decl, this particular type class could be just
    -- about providing a `fix`, in contrast to the Sestoft-style calculus
    -- where we use this combinator to encode different evaluation strategies

instance Show (Concrete τ v) where
  show _ = "_"

evalConc :: IsTrace τ => Exp -> τ (Value (Concrete τ))
evalConc e = unConcrete $ eval e Map.empty

--------------------
-- 0CFA+IntervalAnalysis
--------------------
-----------
-- IV
data InfiniteNumber a = NegInfinity | Number a | Infinity deriving (Eq,Ord)

instance (Num a, Ord a) => Num (InfiniteNumber a) where
  NegInfinity + Infinity = error "Addition of positive and negative infinity is undefined"
  Infinity + NegInfinity = error "Addition of positive and negative infinity is undefined"
  Infinity + _ = Infinity
  _ + Infinity = Infinity
  NegInfinity + _ = NegInfinity
  _ + NegInfinity = NegInfinity
  Number n + Number m = Number (n + m)

  --Number n * e = mult n e
  --e * Number m = mult m e
  --Infinity * Infinity = Infinity
  --Infinity * NegInfinity = NegInfinity
  --NegInfinity * Infinity = NegInfinity
  --NegInfinity * NegInfinity = Infinity

  abs (Number n) = Number (abs n)
  abs _ = Infinity

  signum Infinity = Number 1
  signum NegInfinity = Number (-1)
  signum (Number n) = Number (signum n)

  fromInteger = Number . fromInteger

  negate Infinity = NegInfinity
  negate NegInfinity = Infinity
  negate (Number n) = Number (negate n)

data IV = IV { lower :: InfiniteNumber Integer, upper :: InfiniteNumber Integer }
  deriving Eq

instance Lat IV where
  bottom = IV Infinity NegInfinity
  IV l1 u1 ⊔ IV l2 u2 = IV (min l1 l2) (max u1 u2)

instance Show a => Show (InfiniteNumber a) where
  show NegInfinity = "-∞"
  show Infinity = "∞"
  show (Number a) = show a
instance Show IV where show (IV l u) = "[" ++ show l ++ "," ++ show u ++ "]"

-----------
-- May-Powersets
newtype Pow a = P { unP :: Set.Set a } deriving (Eq, Ord,Show)

instance Ord a => Lat (Pow a) where
  bottom = P Set.empty
  P l ⊔ P r = P (Set.union l r)

-----------
-- CValue
data CValue = CV IV (Pow Label) deriving Eq
instance Lat CValue where
  bottom = CV bottom bottom
  CV i1 l1 ⊔ CV i2 l2 = CV (i1 ⊔ i2) (l1 ⊔ l2)
instance Show CValue where
  show (CV iv funs) = "(" ++ show iv ++ "," ++ show funs ++ ")"

-----------
-- FunCache
data FunCache = FC (Maybe (CValue, CValue)) (CValue -> CD)
instance Eq FunCache where
  FC cache1 _ == FC cache2 _ = cache1 == cache2
instance Lat FunCache where
  bottom = FC Nothing (const (return bottom))
  FC cache1 f1 ⊔ FC cache2 f2 = FC cache' f'
    where
      f' v = (⊔) <$> f1 v <*> f2 v
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

traceWith f a = trace (f a) a
----------
-- CT (the trace monad)
type CD = CT CValue
newtype CT a = CT { unCT :: State (Map.Map Label FunCache) a } deriving (Functor,Applicative,Monad)
instance IsTrace CT where step _ = id
instance IsValue CT CValue where
  retStuck = return bottom
  retZero = return (CV (IV 0 0) bottom)
  succ (CV iv@(IV l u) _) = return (CV (IV (l+1) (u+1)) bottom)
  pred (CV (IV l u) _) = return (CV (IV (l-1) (u-1)) bottom)
  ifZero (CV (IV l u) _) t e
    | l == 0, u == 0 = t
    | u < 0 || l > 0 = e
    | otherwise      = (⊔) <$> t <*> e
  retFun ell f = do updCacheFun ell f; return (CV bottom (P (Set.singleton ell)))
  apply (CV _ (P ells)) v = do
--    traceM ("apply " ++ show ells ++ show v)
    lub <$> traverse (\ell -> cachedCall ell v) (Set.toList ells)
instance HasAlloc CT CValue where
  alloc f = fmap return (go bottom)
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- f (return v)
        let v'' = widen v v'
        cache' <- CT get
--        traceM (show v' ++ show v'')
        if v'' ⊑ v && cache' ⊑ cache then return v'' else go v''
      widen _old (CV iv funs) = CV (bounded 10 iv) funs
      bounded n (IV l u) = IV (if l < (-n) then NegInfinity else l) (if u > n then Infinity else u)

updCacheFun :: Label -> (CValue -> CD) -> CT ()
updCacheFun ell f = CT $ modify $ \funs ->
  Map.singleton ell (FC Nothing f) ⊔ funs

cachedCall :: Label -> CValue -> CT CValue
cachedCall ell v = CT $ do
  FC cache f <- gets (Map.findWithDefault bottom ell)
  let call in_ out = do
        let in_' = in_ ⊔ v      -- merge all Labels that reach the lambda var ell!
        modify $ Map.insert ell (FC (Just (in_',out)) f)
        out' <- unCT (f in_')
        modify $ Map.insert ell (FC (Just (in_',out')) f)
        return out'
--  traceM ("cachedCall " ++ show ell ++ show v ++ show cache)
  case cache of
    Just (in_,out)
      | v ⊑ in_   -> return out
      | otherwise -> call in_ out
    Nothing       -> call bottom bottom

-- |
-- >>> runCFA $ eval (read "(rec id. λx. if0(x;x;succ (id (pred(x))))) 3") Map.empty
--
-- >>> runCFA $ eval (read "(rec id. λx. id x) 3") Map.empty
runCFA :: CT CValue -> CValue
runCFA (CT m) = evalState m bottom
