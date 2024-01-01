module Annotated where

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

type Ann a = Name :-> a

(|||) :: Ann U -> Ann U -> Ann U
(|||) = Map.unionWith undefined

data U = U0 | U1 | Uω; instance Lat U where
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
data UT a = Uses (Name :-> U) (Ann U) a

instance Trace (UT v) where
  step (Lookup x)  (Uses φ ann a)  = Uses (φ + ext emp x U1) ann a
  step _           τ               = τ

instance Monad UT where
  Uses φ1 ann1 a >>= k
    |  Uses φ2 ann2 b <- k a
    =  Uses (φ1+φ2) (ann1 ||| ann2) b

data UValue = Nop; type UD = UT UValue

nopD :: UD
nopD = Uses emp emp Nop

manify :: UD -> UD
manify (Uses φ ann Nop) = Uses (φ+φ) ann Nop

instance Domain UD where
  stuck                                  = nopD
  fun {-" \iffalse "-}_{-" \fi "-} f     = manify (f nopD)
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = manify (foldr (>>) nopD ds)
  apply d a                              = manify a >> d
  select d fs                            = d >> lub [ f (replicate (conArity k) nopD) | (k,f) <- Map.assocs fs ]

instance Lat UD where
  bottom = nopD
  Uses φ1 ann1 Nop ⊔ Uses φ2 ann2 Nop = Uses (φ1 ⊔ φ2) (ann1 ⊔ ann2) Nop

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
  show (Uses φ anns _) = show φ ++ ", " ++ show anns

instance Applicative UT where
  pure a = Uses emp emp a
  (<*>) = ap

instance Show UValue where
  show Nop = ""

annotate :: Name -> UD -> UD
annotate x (Uses φ ann v) = Uses (Map.delete x φ) (ext ann x (Map.findWithDefault bottom x φ)) v

instance HasBind UD where
  bind x rhs body =
    let Uses φ1 ann1 v1 = kleeneFix rhs in
    let Uses φ2 ann2 v2 = annotate x (body (Uses φ1 emp v1)) in
    Uses φ2 (ann1 ||| ann2) v2
