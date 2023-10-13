{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Order where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

class Eq a => Lat a where
  bottom :: a
  (⊔) :: a -> a -> a;

(⊑) :: Lat a => a -> a -> Bool
x ⊑ y = x ⊔ y == y

lub :: (Foldable f, Lat a) => f a -> a
lub = foldr (⊔) bottom
{-# INLINE lub #-}

instance (Ord k, Lat v) => Lat (Map k v) where
  bottom = Map.empty
  (⊔) = Map.unionWith (⊔)

instance (Ord a, Lat a) => Lat (Set a) where
  bottom = Set.empty
  (⊔) = Set.union

kleeneFix :: Lat a => (a -> a) -> a
kleeneFix f = stationary $ iterate f bottom where stationary (a:b:r) = if b ⊑ a then b else stationary (b:r)