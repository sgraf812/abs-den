module Gen where

import           Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Char
import Text.Show
import Control.Monad
import Control.Monad.Trans.State
import Abstraction hiding ((+))

import Exp hiding (Env)
import GHC.Stack

newtype Env = Env { nextFree :: Int }

instance Show Env where
  showsPrec _ = showListWith showString . boundVars

idx2Name :: Int -> Name
idx2Name n | n <= 26   = [chr (ord 'a' + n)]
           | otherwise = "t" ++ show n

boundVars :: Env -> [Name]
boundVars (Env n) = map idx2Name [0..n-1]

mkEnvWithNVars :: Int -> Env
mkEnvWithNVars = Env

emptyEnv :: Env
emptyEnv = mkEnvWithNVars 0

env :: Gen Env
env = Gen.sized $ \size -> Gen.element (map mkEnvWithNVars [0..max 0 (unSize size)])

closedExpr :: Gen Exp
closedExpr = openExpr emptyEnv

openExpr :: Env -> Gen Exp
openExpr env = uniqify <$> openExprShadow env
  where
    uniqify e = evalState (go Map.empty e) emptyEnv
    go benv (Let n e1 e2) = do
      n' <- fresh
      let benv' = Map.insert n n' benv
      Let n' <$> go benv' e1 <*> go benv' e2
    go benv (Lam n e) = do
      n' <- fresh
      let benv' = Map.insert n n' benv
      Lam n' <$> go benv' e
    go benv (Var n) =
      pure (Var (Map.findWithDefault n n benv))
    go benv (App e n) =
      App <$> go benv e <*> pure (Map.findWithDefault n n benv)
    go benv (ConApp k ns) =
      pure (ConApp k (map (\n -> Map.findWithDefault n n benv) ns))
    go benv (Case e alts) =
      Case <$> go benv e <*> traverse alt alts
        where
          alt (k,ns,rhs) = do
            ns' <- traverse (const fresh) ns
            let benv' = foldr (uncurry Map.insert) benv (zip ns ns')
            rhs' <- go benv' rhs
            pure (k,ns',rhs')
    fresh = state $ \env -> (idx2Name $ nextFree env, env{nextFree = nextFree env + 1})

-- | May cause shadowing. Will be cleaned up in openExpr
openExprShadow :: Env -> Gen Exp
-- TODO: Try Gen.recursive
openExprShadow env = Gen.sized $ \size ->
  Gen.frequency $ concat
    [ [ ((unSize size `div` 10) + 2, boundName env) | not $ null $ boundVars env ]
    , [ ((unSize size `div` 3) + 1, let_ env) ]
    , [ ((unSize size `div` 3) + 1, lam env)      ]
    , [ ((unSize size `div` 3) + 1, app env)  | not $ null $ boundVars env ]
    , [ ((unSize size `div` 3) + 1, conApp env)  | not $ null $ boundVars env ]
    , [ ((unSize size `div` 3) + 1, case_ env)  | not $ null $ boundVars env ]
--    , [ (0, conApp env)  | not $ null $ boundVars env ]
--    , [ (0, case_ env)  | not $ null $ boundVars env ]
    ]

myElement :: HasCallStack => [a] -> Gen a
myElement = Gen.element

boundName, app, lam, let_, conApp, case_ :: Env -> Gen Exp
boundName env = Gen.element (map Var (boundVars env))
app       env =
  App <$> Gen.scale (max 0 . subtract 1) (openExprShadow env)
      <*> Gen.element (boundVars env)
lam       env = withBoundName env $ \v env' ->
  Lam v <$> Gen.scale (max 0 . subtract 1) (openExprShadow env')
let_      env = withBoundName env $ \v env' ->
  Let v <$> Gen.small (openExprShadow env')
        <*> Gen.small (openExprShadow env')
conApp    env = do
  k :: Tag <- Gen.enumBounded
  ConApp k <$> replicateM (conArity k) (Gen.element (boundVars env))
case_     env = do
  tc :: TyCon <- Gen.enumBounded
  let ks = tyConTags tc
  let alt k = withNBoundNames (conArity k) env $ \vs env' -> do
        rhs <- Gen.small (openExprShadow env)
        pure (k,vs,rhs)
  Case <$> Gen.scale (max 0 . subtract 1) (openExprShadow env)
       <*> traverse alt (tyConTags tc)

withBoundName :: Env -> (Name -> Env -> Gen a) -> Gen a
withBoundName env f = fresh -- dont want shadowing : [ shadowing | not $ null $ boundVars env ]
  where
    fresh = do
      let tv   = idx2Name (nextFree env)
          env' = env { nextFree = nextFree env + 1 }
      f tv env'
    shadowing = do
      tv <- Gen.element (boundVars env)
      f tv env

withNBoundNames :: Int -> Env -> ([Name] -> Env -> Gen a) -> Gen a
withNBoundNames n env f = go n [] env
  where
    go 0 vs env = f vs env
    go n vs env = withBoundName env $ \v env' -> go (n-1) (v:vs) env'

--exprDepth :: Exp -> Int
--exprDepth (Fix (Var _)) = 0
--exprDepth (Fix (App f a)) = 1 + exprDepth f
--exprDepth (Fix (Lam _ e)) = 1 + exprDepth e
--exprDepth (Fix (Let _ e1 e2)) = 1 + max (exprDepth e1) (exprDepth e2)

--exprSize :: Exp -> Int
--exprSize (Fix (Var _)) = 1
--exprSize (Fix (App f a)) = 1 + exprSize f
--exprSize (Fix (Lam _ e)) = 1 + exprSize e
--exprSize (Fix (Let _ e1 e2)) = 1 + exprSize e1 + exprSize e2

