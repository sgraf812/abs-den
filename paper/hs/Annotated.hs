module Annotated where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Data.Foldable
import Data.STRef
import qualified Data.List as List
import Exp
import Order
import Interpreter

type AnnT s a = ReaderT (STRef s (Name :-> a))

instance Trace d => Trace (ReaderT e (ST s) d) where
  step ev (ReaderT f) = ReaderT (\e -> step ev <$> f e)

--(|||) :: Ann U -> Ann U -> Ann U
--(|||) = Map.unionWith undefined

data U = U0 | U1 | Uω; instance Lat U where
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
data UT a = Uses (Name :-> U) a

instance Trace (UT v) where
  step (Lookup x)  (Uses φ a)  = Uses (φ + ext emp x U1) a
  step _           τ           = τ

instance Monad UT where
  Uses φ1 a >>= k
    |  Uses φ2 b <- k a
    =  Uses (φ1+φ2) b

data UValue = Nop; type UD = UT UValue

nopD :: UD
nopD = Uses emp Nop

manify :: UD -> UD
manify (Uses φ Nop) = Uses (φ+φ) Nop

instance Domain UD where
  stuck                                  = nopD
  fun {-" \iffalse "-}_{-" \fi "-} f     = manify (f nopD)
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = manify (foldr (>>) nopD ds)
  apply d a                              = manify a >> d
  select d fs                            = d >> lub [ f (replicate (conArity k) nopD) | (k,f) <- Map.assocs fs ]

instance Lat UD where
  bottom = nopD
  Uses φ1 Nop ⊔ Uses φ2 Nop = Uses (φ1 ⊔ φ2) Nop

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

instance HasBind UD where
  bind _ rhs body = body (kleeneFix rhs)

data Anns s = A { cache :: STRef s (Name :-> UD), anns :: STRef s (Name :-> U) }

newtype AnnUT s a = AnnUT (ReaderT (Anns s) (ST s) a)
  deriving (Functor, Applicative, Monad, Trace)

type AnnUD s = AnnUT s UD

instance Domain (AnnUD s) where
  stuck = return stuck
  fun l f = manify <$> f (pure nopD) -- it is key that we don't need to call `fun` here and in `select` below
  con l k ds = con l k <$> sequence ds
  apply f d = apply <$> f <*> d
  select d fs = do
    (>>) <$> d <*> fmap lub (sequence [ f (replicate (conArity k) (pure nopD)) | (k,f) <- Map.assocs fs ])

getCache :: Name -> AnnUT s UD
getCache n = AnnUT $ ReaderT $ \ann -> do
  c <- readSTRef (cache ann)
  pure (Map.findWithDefault bottom n c)

setCache :: Name -> UD -> AnnUT s ()
setCache n d = AnnUT $ ReaderT $ \ann -> do
  modifySTRef' (cache ann) $ \c -> ext c n d

annotate :: Name -> AnnUD s -> AnnUD s
annotate x d = do
  Uses φ v <- d
  AnnUT $ ReaderT $ \ann -> modifySTRef' (anns ann) $ \a -> ext a x (Map.findWithDefault bottom x φ)
  pure (Uses (Map.delete x φ) v)

instance HasBind (AnnUD s) where
  bind x rhs body = do
    d <- getCache x
    d1 <- kleeneFixFromM d rhs
    setCache x d1
    annotate x (body (pure d1))

run :: (forall s. AnnUD s) -> (Name :-> U, Name :-> U)
run m = runST $ do
  ann <- A <$> newSTRef emp <*> newSTRef emp
  Uses φ Nop <- runReaderT (case m of AnnUT r -> r) ann
  anns <- readSTRef (anns ann)
  return (φ, anns)
