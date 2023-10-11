module Order where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Reflexive, transitive order
class PreOrd x where
  (⊑) :: x -> x -> Bool
  infix 4 ⊑

  (≈) :: x -> x -> Bool
  x ≈ y = x ⊑ y && y ⊑ x
  infix 4 ≈
  {-# INLINE (≈) #-}

-- | Order with all least upper bounds
class PreOrd x => Complete x where
  (⊔) :: x -> x -> x
  infixr 5 ⊔

-- | Order with a least element
class PreOrd x => LowerBounded x where
  bottom :: x

lub :: (Foldable f, Complete x, LowerBounded x) => f x -> x
lub = foldr (⊔) bottom
{-# INLINE lub #-}

instance (Ord k,PreOrd v) => PreOrd (Map k v) where
  c1 ⊑ c2 = Map.keysSet c1 `Set.isSubsetOf` Map.keysSet c2 && all (\k -> (c1 Map.! k) ⊑ (c2 Map.! k)) (Map.keys c1)

instance (Ord k, PreOrd v) => LowerBounded (Map k v) where
  bottom = Map.empty

instance (Ord k, Complete v) => Complete (Map k v) where
  (⊔) = Map.unionWith (⊔)

instance PreOrd a => PreOrd (Set a) where
  s1 ⊑ s2 = all (\x -> any (\y -> x ⊑ y) s2) s1

instance (Ord a, PreOrd a) => Complete (Set a) where
  (⊔) = Set.union

kleeneFix :: (Complete l, LowerBounded l) => (l -> l) -> l
kleeneFix f = go (f bottom)
  where
  go l = let l' = f l in if l' ⊑ l then l' else go l'
