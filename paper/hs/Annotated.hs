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

type AnnT s a = ReaderT (STRef s (Name :-> a))

instance Trace d => Trace (ReaderT e (ST s) d) where
  step ev (ReaderT f) = ReaderT (\e -> step ev <$> f e)

---------------------------
-- Copied from Abstraction
---------------------------

data U = U0 | U1 | Uω
type Uses = Name :-> U
class UVec a where
  (+)  :: a -> a -> a
  (*)  :: U -> a -> a
instance UVec U where {-" ... \iffalse "-}
  U1 + U1 = Uω
  u1 + u2 = u1 ⊔ u2
  U0 * _ = U0
  _ * U0 = U0
  U1 * u = u
  Uω * _ = Uω {-" \fi "-}
instance UVec Uses where {-" ... \iffalse "-}
  (+) = Map.unionWith (+)
  u * m = Map.map (u *) m
{-" \fi "-}

data UT v = MkUT Uses v
instance Trace (UT v) where
  step (Lookup x)  (MkUT φ v)  = MkUT (singenv x U1 + φ) v
  step _           τ           = τ
instance Monad UT where
  MkUT φ1 a >>= k = let MkUT φ2 b = k a in MkUT (φ1+φ2) b

data UValue = UCons U UValue | Rep U
type UD = UT UValue

instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
{-" \fi "-}

instance Lat UValue where {-" ... \iffalse "-}
  bottom = (Rep U0)
  Rep u1 ⊔ Rep u2 = Rep (u1 ⊔ u2)
  Rep u1 ⊔ v = UCons u1 (Rep u1) ⊔ v
  v ⊔ Rep u2 = v ⊔ UCons u2 (Rep u2)
  UCons u1 v1 ⊔ UCons u2 v2 = UCons (u1 ⊔ u2) (v1 ⊔ v2)
{-" \fi "-}
instance Lat UD where {-" ... \iffalse "-}
  bottom = MkUT bottom bottom
  MkUT φ1 v1 ⊔ MkUT φ2 v2 = MkUT (φ1 ⊔ φ2) (v1 ⊔ v2)
{-" \fi "-}

peel :: UValue -> (U, UValue)
peel (Rep u)      = (u,(Rep u))
peel (UCons u v)  = (u,v)

(!?) :: Uses -> Name -> U
m !? x  | x ∈ dom m  = m ! x
        | otherwise  = U0

instance Domain UD where
  stuck                                  = bottom
  fun x {-" \iffalse "-}_{-" \fi "-} f   = case f (MkUT (singenv x U1) (Rep Uω)) of
    MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) v)
  apply (MkUT φ1 v1) (MkUT φ2 _)         = case peel v1 of
    (u, v2) -> MkUT (φ1 + u*φ2) v2
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = foldl apply (MkUT emp (Rep Uω)) ds
  select d fs                            =
    d >> lub  [  f (replicate (conArity k) (MkUT emp (Rep Uω)))
              |  (k,f) <- assocs fs ]

instance HasBind UD where
  bind _ rhs body = body (kleeneFix rhs)

deriving instance Eq U
deriving instance Eq a => Eq (UT a)
deriving instance Functor UT

instance Eq UValue where
  Rep u1 == Rep u2 = u1 == u2
  v1     == v2     = peel v1 == peel v2

instance Show U where
  show U0 = "\\concolor{\\mathsf{U_0}}"
  show U1 = "\\concolor{\\mathsf{U_1}}"
  show Uω = "\\concolor{\\mathsf{U_ω}}"

infixl 6 +
infixl 7 *

instance Show v => Show (UT v) where
  show (MkUT φ v) = "\\langle " ++ show (Map.filter (/= U0) φ) ++ ", " ++ show v ++ " \\rangle"

instance Applicative UT where
  pure a = MkUT emp a
  (<*>) = ap

instance Show UValue where
  show (Rep u) = show u ++ ".."
  show (UCons u v) = show u ++ " \\sumcons " ++ show v

---------------------------
-- End Copied from Abstraction
---------------------------

data Anns s d = A { cache :: STRef s (Name :-> d), anns :: STRef s (Name :-> Ann d) }

newtype AnnUT s d a = AnnUT (ReaderT (Anns s d) (ST s) a)
  deriving (Functor, Applicative, Monad, Trace)

type AnnD s d = AnnT s d d

class StaticDomain d where
  type Ann d :: Type
  funS :: Monad m => Name -> Label -> (m d -> m d) -> m d
  selectS :: Monad m => m d -> (Tag :-> ([m d] -> m d)) -> m d
  extractAnn :: Name -> d -> (Ann d, d)

-- IndexedDomain does not seem to work well with Anns
-- class IndexedDomain i o where
--   funP :: Monad m => Name -> Label -> ((i -> m o) -> i -> m o) -> i -> m o
--   selectP :: Monad m => (i -> m o) -> (Tag :-> ([i -> m o] -> i -> m o)) -> i -> m o
--
-- instance StaticDomain s => IndexedDomain () s where
--   funP x l f () = funS x l (f ())
--   selectS md mfs () = selectS (md ()) (\f mds -> f (map const mds) ()) <$> mfs)

instance StaticDomain d => Domain (AnnD s d) where
  stuck = return stuck
  fun x l f = funS x l f
  con l k ds = con l k <$> sequence ds
  apply f d = apply <$> f <*> d
  select md mfs = selectS md mfs

getCache :: Name -> AnnD s d
getCache n = AnnT $ ReaderT $ \ann -> do
  c <- readSTRef (cache ann)
  pure (Map.findWithDefault bottom n c)

setCache :: Name -> UD -> AnnUT s ()
setCache n d = AnnUT $ ReaderT $ \ann ->
  modifySTRef' (cache ann) $ \c -> ext c n d

annotate :: StaticDomain d => Name -> AnnD s d -> AnnD s d
annotate x ad = do
  d <- ad
  let (ann, d') = extractAnn d
  AnnUT $ ReaderT $ \s -> modifySTRef' (anns s) $ \a -> ext a x ann
  pure d'

instance HasBind (AnnD s d) where
  bind x rhs body = do
    d <- getCache x
    d1 <- kleeneFixFromM d rhs
    setCache x d1
    annotate x (body (pure d1))

instance StaticDomain UD where
  funS x _ f = do
    MkUT φ v <- f (pure (MkUT (singenv x U1) (Rep Uω)))
    pure (MkUT (ext φ x U0) (UCons (φ !? x) v))
  selectS md mfs = do
    (>>) <$> md <*> fmap lub (sequence [ f (replicate (conArity k) (pure (MkUT emp (Rep Uω))))
                                       | (k,f) <- Map.assocs mfs ])
  extractAnn (MkUT φ v) = (Map.findWithDefault bottom x φ, MkUT (Map.delete x φ) v)

run :: (forall s. AnnUD s) -> (Name :-> U, Name :-> U)
run m = runST $ do
  ann <- A <$> newSTRef emp <*> newSTRef emp
  MkUT φ _v <- runReaderT (case m of AnnUT r -> r) ann
  anns <- readSTRef (anns ann)
  return (φ, anns)
