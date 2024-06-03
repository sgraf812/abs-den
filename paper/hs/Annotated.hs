{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
module Annotated where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Reader
import Data.STRef
import Exp
import Order
import Interpreter
import StaticAnalysis hiding (Cache)
import Data.Kind

data Cache s d = C (STRef s (Name :-> d)) (STRef s (Name :-> Ann d))

newtype AnnT s d a = AnnT (Cache s d -> ST s a)
  deriving (Functor, Applicative, Monad) via ReaderT (Cache s d) (ST s)

type AnnD s d = AnnT s d d

instance Trace d => Trace (AnnD s d) where
  step ev (AnnT f) = AnnT (\cache -> step ev <$> f cache)

class Domain d => StaticDomain d where
  type Ann d :: *
  funS :: Monad m => Name -> Label -> (m d -> m d) -> m d
  selectS :: Monad m => m d -> (Tag :-> ([m d] -> m d)) -> m d
  extractAnn :: Name -> d -> (Ann d, d)

instance StaticDomain d => Domain (AnnD s d) where
  stuck = return stuck
  fun x l f = funS x l f
  con l k ds = con l k <$> sequence ds
  apply f d = apply <$> f <*> d
  select md mfs = selectS md mfs

getCache :: Lat d => Name -> AnnD s d
getCache n = AnnT $ \(C cache _) -> do
  c <- readSTRef cache
  pure (Map.findWithDefault bottom n c)

setCache :: Name -> d -> AnnT s d ()
setCache n d = AnnT $ \(C cache _) ->
  modifySTRef' cache $ \c -> ext c n d

annotate :: StaticDomain d => Name -> AnnD s d -> AnnD s d
annotate x ad = do
  d <- ad
  let (ann, d') = extractAnn x d
  AnnT $ \(C _ anns) -> modifySTRef' anns $ \a -> ext a x ann
  pure d'

instance (Lat d, StaticDomain d) => HasBind (AnnD s d) where
  bind x rhs body = do
    d <- getCache x
    d1 <- kleeneFixFromM d rhs
    setCache x d1
    annotate x (body (pure d1))

instance StaticDomain UD where
  type Ann UD = U
  funS x _ f = do
    MkUT φ v <- f (pure (MkUT (singenv x U1) (Rep Uω)))
    pure (MkUT (ext φ x U0) (UCons (φ !? x) v))
  selectS md mfs = do
    (>>) <$> md <*> fmap lub (sequence [ f (replicate (conArity k) (pure (MkUT emp (Rep Uω))))
                                       | (k,f) <- Map.assocs mfs ])
  extractAnn x (MkUT φ v) = (Map.findWithDefault bottom x φ, MkUT (Map.delete x φ) v)

run :: (forall s. AnnD s d) -> (Name :-> Ann d, d)
run m = runST $ do
  c@(C _ anns) <- C <$> newSTRef emp <*> newSTRef emp
  d <- case m of AnnT r -> r c
  anns <- readSTRef anns
  return (anns, d)
