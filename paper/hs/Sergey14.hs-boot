module Sergey14 where

import Expr
import Interpreter
import Data.Set (Set)

data Demand
data SubDemand

instance Show SubDemand
instance Show Demand

type DmdEnv = Name :-> Demand

newtype DmdT a = DT { unDT :: Set Name -> SubDemand -> (a, DmdEnv) }
type DmdD = DmdT DmdVal
data DmdVal

instance Functor DmdT
instance Applicative DmdT
instance Monad DmdT
instance Trace DmdT
instance Domain DmdD
instance HasBind DmdD

instance Show DmdVal

runDmd :: SubDemand -> DmdD -> (DmdVal, DmdEnv)

many :: String -> (DmdVal, DmdEnv)

call :: Int -> String -> (DmdVal, DmdEnv)
