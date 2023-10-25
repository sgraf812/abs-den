{-# LANGUAGE DerivingVia #-}
module DmdAnal where

import Prelude hiding ((+))
import Expr
import Order
import Interpreter
import Abstractions
import Numeric.Natural
import Data.Functor.Identity
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import qualified Data.Map as Map
import qualified Data.Set as Set


-- data U = U0 | U1 | Uω -- defined in Abstractions, including ⊔ and +
type UNonAbs  = U -- Not U0
type UNonOnce = U -- Not U1

data Demand = U :* SubDemand deriving Eq
data SubDemand
  = Call UNonAbs SubDemand
  | Data (Tag :-> [Demand])
  | Poly UNonOnce
  deriving Eq

instance Lat Demand where
instance Lat SubDemand where

instance Plussable Demand where
instance Plussable SubDemand where

absD :: Demand
absD = U0 :* Poly U0

data NameOrIdx = N Name | I Natural deriving (Eq,Ord)

type DmdEnv = NameOrIdx :-> Demand
instance Semigroup Demand where
  d1 <> d2 = d1 + d2
instance Monoid Demand where
  mempty = absD

newtype DmdT a = DT (SubDemand -> (a, DmdEnv))
  deriving (Functor,Applicative,Monad) via ReaderT SubDemand (Writer DmdEnv)

type DmdD = DmdT DmdVal
data DmdVal
  = DmdFun DmdD
  | DmdCon Tag [DmdD]
  | DmdBot -- e.g., stuck
  | DmdNop -- TODO Don't know what to do here

instance IsTrace DmdT where
  step (Lookup x) (DT m) = DT $ \sd ->
    let (a, φ) = m sd in (a, φ + Map.singleton (N x) (U1 :* sd))
  step _ τ = τ

abstractDmdD :: Name -> DmdD -> DmdD
abstractDmdD n = go_d
  where
    go_d (DT m) = DT $ \sd -> let (v,φ) = m sd in (go_v v, go_env φ)
    go_env φ = Map.mapKeys go_key φ
    go_key (I n)              = I (n+1)
    go_key (N n') | n == n'   = I 0
                  | otherwise = N n'
    go_v (DmdFun d) = DmdFun (go_d d)
    go_v (DmdCon k ds) = DmdCon k (map go_d ds)
    go_v DmdBot = DmdBot
    go_v DmdNop = DmdNop

applyDmdD :: Name -> DmdD -> DmdD
applyDmdD n = go_d
  where
    go_d (DT m) = DT $ \sd -> let (v,φ) = m sd in (go_v v, go_env φ)
    go_env φ = Map.mapKeys go_key φ
    go_key (I 0)              = N n
    go_key (I n)              = I (n-1)
    go_key n'                 = n'
    go_v (DmdFun d) = DmdFun (go_d d)
    go_v (DmdCon k ds) = DmdCon k (map go_d ds)
    go_v DmdBot = DmdBot
    go_v DmdNop = DmdNop

instance IsValue DmdT DmdVal where
  retStuck = return DmdBot
  retFun lbl f = DT $ \sd ->
    let sentinel = step (Lookup lbl) (pure DmdNop) in
    let (_n,sd') = case sd of
          Call n sd' -> (n, sd')
          Poly n     -> (n, Poly n)
          _          -> (Uω, Poly Uω) in
    let DT body = abstractDmdD lbl (f sentinel) in
    let (v,φ) = body sd in
    (DmdFun (body sd), emp)
  retCon lbl k ds = DT $ do
    return (DmdCon k ds) -- TODO doesn't look quite right
  apply (DmdFun (DT body)) arg = DT $ \sd ->
    let (_,_) = body (Call U1 sd) in
    applyDmdD body
