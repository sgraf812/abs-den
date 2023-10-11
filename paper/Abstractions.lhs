%options ghci -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
\begin{code}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Abstractions where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (find, foldl')
import Text.Show (showListWith)
import GHC.Show (showList__)
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State
import Expr hiding (Z)
import Order
import Interpreter
\end{code}
%endif

\section{Abstractions}
\label{sec:abstractions}

\cite{*}

We have seen that |eval| is well-suited to express concrete semantics
coninductively.
In this section, we will see how |eval| is also well-suited to
implement abstract semantics, \eg, static program analyses.

\begin{figure}
\begin{code}
data U = Z | O | W -- 0 | 1 | ω
  deriving Eq

instance PreOrd U where
  l ⊑ r = l ⊔ r == r

instance Complete U where
  Z ⊔ u = u
  u ⊔ Z = u
  O ⊔ O = O
  _ ⊔ _ = W

instance LowerBounded U where
  bottom = Z

(+#) :: U -> U -> U
O  +# O  = W
u1 +# u2 = u1 ⊔ u2

type Us = Name :-> U

(.+.) :: Us -> Us -> Us
(.+.) = Map.unionWith (+#)

instance {-# OVERLAPPING #-} Show Us where
  show = ($ []) . showList__ (\(k,v) -> (k ++) . ('↦':) . shows v) . Map.toList

instance Show U where
  show Z = "0"
  show O = "1"
  show W = "ω"

data Usg a = Usg Us !a
  deriving (Eq,Functor)

instance Show a => Show (Usg a) where
  show (Usg us val) = show us ++ show val

instance Applicative Usg where
  pure a = Usg emp a
  (<*>) = ap

instance Monad Usg where
  Usg us1 a >>= k = case k a of
    Usg us2 b -> Usg (us1 .+. us2) b

add :: Us -> Name -> Us
add us x = Map.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us

instance IsTrace Usg where
  step (Lookup x) (Usg us a)  = Usg (add us x) a
  step _          usg         = usg

-- These won't work, because UTrace is an inductive trace type.
-- Use PrefixTrace instead!
--
-- evalByName :: Expr -> Usg (Value (ByName Usg))
-- evalByName = Template.evalByName
--
-- evalByNeed :: Expr -> Usg (Value (ByNeed Usg), Heap (ByNeed Usg))
-- evalByNeed = Template.evalByNeed
--
-- evalByValue :: Expr -> Usg (Value (ByValue Usg))
-- evalByValue = Template.evalByValue

---------------
-- AbsVal
---------------

data AbsVal = Nop
  deriving Eq

instance Show AbsVal where
  show Nop = ""

instance IsValue Usg AbsVal where
  retStuck = return Nop
  retFun f = Usg (evalDeep (f nopD)) Nop
  retCon _ ds = Usg (foldr (.+.) emp $ map evalDeep ds) Nop
  apply Nop d = Usg (evalDeep d) Nop
  select Nop fs = Usg (lub $ map (\(k,f) -> evalDeep (f (replicate (conArity k) nopD))) fs) Nop

nopD :: Usg AbsVal
nopD = Usg emp Nop

evalDeep :: Usg AbsVal -> Us
evalDeep (Usg us _) = W *# us

(*#) :: U -> Us -> Us
Z *# _  = emp
O *# us = us
W *# us = fmap (const W) us

instance PreOrd (Usg AbsVal) where
  l ⊑ r = l ⊔ r == r

instance LowerBounded (Usg AbsVal) where
  bottom = Usg bottom Nop

instance Complete (Usg AbsVal) where
  Usg us1 Nop ⊔ Usg us2 Nop = Usg (us1 ⊔ us2) Nop

instance HasAlloc Usg AbsVal where
  alloc f = pure (kleeneFix f)

evalAbsUsg :: Expr -> Usg AbsVal
evalAbsUsg e = eval e emp

\end{code}
\caption{Usage Analysis via |IsTrace|,|IsValue|,|HasAlloc|}
\label{fig:eval-usg}
\end{figure}

\subsection{Usage analysis}

< ghci> eval (read "let i = λx.x in i i") emp :: D
$\perform{eval (read "let i = λx.x in i i") emp :: D (ByName T)}$
\\[\belowdisplayskip]
\noindent
Which is in direct correspondence to the call-by-name small-step trace
