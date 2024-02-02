module Sergey14 where

import Exp
import Interpreter
import Data.Map (Map)
import Data.Set (Set)

data Demand
data SubDemand

instance Show SubDemand
instance Show Demand

type DmdEnv = Map Name Demand

newtype DmdT a = DT { unDT :: Set Name -> SubDemand -> (a, DmdEnv) }
type DmdD = DmdT DmdVal
data DmdVal

instance Functor DmdT
instance Applicative DmdT
instance Monad DmdT
instance Trace (DmdT v)
instance Domain DmdD
instance HasBind DmdD

instance Show DmdVal

runDmd :: SubDemand -> DmdD -> (DmdVal, DmdEnv)

anyCtx :: String -> (DmdVal, DmdEnv)

call :: Int -> String -> (DmdVal, DmdEnv)
