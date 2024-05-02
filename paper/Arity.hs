{-# LANGUAGE GeneralisedNewtypeDeriving #-}
module Arity where

import Order
import Exp
import Interpreter

data IntWithInfOp = I Int | Inf deriving Eq

instance Show IntWithInfOp where
  show Inf = "∞"
  show (I n) = show n

instance Lat IntWithInfOp where
  bottom = Inf
  Inf ⊔ i = i
  i ⊔ Inf = i
  I n1 ⊔ I n2 = I (min n1 n2)

type Arity = IntWithInfOp

topArity :: Arity
topArity = I 0

divArity :: Arity
divArity = I 0

inc :: Arity -> Arity
inc a@(Inf)  = a
inc (I n) = I (n+1)

dec :: Arity -> Arity
dec a@(Inf) = a
dec (I n)
  | n > 0     = I (n-1)
  | otherwise = I 0

instance Trace Arity where
  step _ a = a

instance Domain Arity where
  stuck = divArity
  apply f _ = dec f
  fun _ _ f = inc (f topArity)
  con _ k ds = topArity
  select _ _ = topArity

instance HasBind Arity where
  bind _ rhs body = body (kleeneFixFrom divArity rhs)
