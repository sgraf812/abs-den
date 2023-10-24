module DmdAnal where

import Interpreter
import Abstractions
import Control.Monad.Trans.RWS


-- data U = U0 | U1 | Uω -- defined in Abstractions, including ⊔ and +
type UNonAbs  = U -- Not U0
type UNonOnce = U -- Not U1

data Demand = U :* SubDemand
data SubDemand
  = Call UNonAbs SubDemand
  | Data (Tag :-> [Demand])
  | Poly UNonOnce

data NameOrIdx = N Name | I Nat deriving (Eq,Ord)

newtype DmdEnv = DE (Name :-> Demand)
  deriving (Eq, Lat)
instance Semigroup DmdEnv where
  DE φ1 <> DE φ2 = DE (φ1 + φ2)
instance Monoid DmdEnv where
  mempty = DE emp

newtype DmdT a = DT (RWS SubDemand DmdEnv () a)
  deriving (Functor,Applicative,Monad)
type DmdD = DT DmdVal
data DmdVal
  = DmdFun DmdD
  | DmdCon Tag [DmdD]
  | DmdBot -- e.g., stuck
  | DmdNop -- TODO Don't know what to do here

instance IsTrace DmdT where
  step (Lookup x) (DT m) = DT $ do
    sd <- ask
    tell (ext emp x (U1 :* sd))
    m
  step _ τ = τ

abstractDmdD :: Name -> DmdD -> DmdD
abstractDmdD n = go_d
  where
    go_d (DT m) = DT $ mapWriter (\(v,φ) -> (go_v v, go_env φ)) m
    go_env (DE φ) = DE (Map.mapKeys go_key φ)
    go_key (I n)              = I (n+1)
    go_key (N n') | n == n'   = I 0
                  | otherwise = N n'
    go_v (DmdFun d) = DmdFun (go_d d)
    go_v (DmdCon k ds) = DmdCon k (map go_d ds)
    go_v DmdBot = DmdBot
    go_v DmdNop = DmdNop

-- applyDmdD :: Name -> DmdD -> DmdD -> DmdD
-- applyDmdD n d = go_d
--   where
--     go_d (DT m) = DT $ mapWriter (\(v,φ) -> (go_v v, go_env φ)) m
--     go_env (DE φ) = DE (Map.mapKeys go_key φ)
--     go_key (I 0)              = I (n+1)
--     go_key (N n') | n == n'   = I 0
--                   | otherwise = N n'
--     go_v (DmdFun d) = DmdFun (go_d d)
--     go_v (DmdCon k ds) = DmdCon k (map go_d ds)
--     go_v DmdBot = DmdBot
--     go_v DmdNop = DmdNop

instance IsValue DmdT DmdVal where
  retStuck = return DmdBot
  retFun lbl f = return (DmdFun (abstractDmdD lbl (f sentinel))) --TODO: Forward SubDemand, somehow??
    where
      sentinel = step (Lookup lbl) (pure DmdNop)
