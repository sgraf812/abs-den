{-# LANGUAGE DerivingVia #-}
module Sergey14 where

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

data Demand = Abs | UNonAbs :* SubDemand deriving Eq
data SubDemand
  = Seq
  | Top
  | Call UNonAbs SubDemand
  | Prod [Demand]

absDmd = Abs
topDmd = Uω :* Top

instance Lat Demand where
  bottom = Abs
  Abs ⊔ d = d
  d ⊔ Abs = d
  (u1:*sd1) ⊔ (u2:*sd2) = (u1⊔u2) :* (sd1⊔sd2)
instance Eq SubDemand where
  Seq == Seq = True
  Top == Top = True
  Top == Call n sd = n == Uω && sd == Top
  Top == Prod dmds = all (== topDmd) dmds
  Seq == Prod dmds = all (== absDmd) dmds
  _   == _         = False
instance Lat SubDemand where
  bottom = Seq
  Top ⊔ _ = Top
  _ ⊔ Top = Top
  Seq ⊔ sd = sd
  sd ⊔ Seq = sd
  Call n1 sd1 ⊔ Call n2 sd2 = Call (n1⊔n2) (sd1⊔sd2)
  Prod dmds1 ⊔ Prod dmds2 = Prod (dmds1⊔dmds2)
  _ ⊔ _ = Top

instance Plussable Demand where
  Abs + d = d
  d + Abs = d
  (_u1:*sd1) + (_u2:*sd2) = Uω :* (sd1+sd2)

instance Plussable SubDemand where
  Top + _ = Top
  _ + Top = Top
  Seq + sd = sd
  sd + Seq = sd
  Call n1 sd1 + Call n2 sd2 = Call Uω (sd1 ⊔ sd2)
  Prod dmds1 + Prod dmds2 = Prod (dmds1+dmds2)
  _ + _ = Top

absD :: Demand
absD = U0 :* Poly U0

type DmdEnv = Name :-> Demand
instance Semigroup Demand where
  d1 <> d2 = d1 + d2
instance Monoid Demand where
  mempty = absD

newtype DmdT a = DT (SubDemand -> (a, DmdEnv))
  deriving (Functor,Applicative,Monad) via ReaderT SubDemand (Writer DmdEnv)

type DmdD = DmdT DmdVal
data DmdVal = DmdFun Demand DmdVal | DmdNop

instance IsTrace DmdT where
  step (Lookup x) (DT m) = DT $ \sd ->
    let (a, φ) = m sd in (a, φ + ext emp x (U1 :* sd))
  step _ τ = τ

abstractDmdD :: Name -> DmdD -> DmdD
abstractDmdD n = _

applyDmdD :: Name -> DmdD -> DmdD
applyDmdD n = _

isProd :: Tag -> Bool
isProd Pair = True
isProd _    = False -- TT,FF,Some,None,S,Z

squeezeSubDmd :: DmdD -> SubDemand -> DmdEnv
squeezeSubDmd (DT f) sd = snd (f sd)

squeezeDmd :: DmdD -> Demand -> DmdEnv
squeezeDmd d Abs = emp
squeezeDmd d (n :* sd)
  | U1 <- n = squeezeSubDmd d sd
  | Uω <- n = squeezeSubDmd d sd + squeezeSubDmd d Seq

instance IsValue DmdT DmdVal where
  retStuck = return DmdBot
  retFun lbl f = DT $ \sd ->
    let sentinel = step (Lookup lbl) (pure DmdNop) in
    let (_n,sd') = case sd of
          Call n sd' -> (n, sd')
          Seq        -> (U0, Seq)
          _          -> (Uω, Top) in
    let DT body = abstractDmdD lbl (f sentinel) in
    let (v,φ) = body sd in
    (DmdFun (body sd), emp)
  retCon lbl k ds = DT $ \sd ->
    let dmds = case sd of
          Prod dmds | length dmds == length ds, isProd k -> dmds
          Seq -> replicate (length ds) absDmd
          _   -> replciate (length ds) topDmd in
    (DmdNop, foldr (+) emp (zipWith squeeze ds dmds))
  apply (DmdFun (DT body)) arg = DT $ \sd ->
    let (_,_) = body (Call U1 sd) in
    applyDmdD body
