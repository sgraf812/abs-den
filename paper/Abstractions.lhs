%options ghci -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Abstractions where

import Prelude hiding ((+), (*))
import qualified Data.Map as Map
import Control.Monad
import Expr
import Order
import Interpreter
\end{code}
%endif

\section{Abstractions}
\label{sec:abstractions}

%\cite{*}
We have seen that |eval| is well-suited to express concrete semantics
coinductively.
In this section, we will see how |eval| is also well-suited to implement
abstract semantics, \eg, static program analyses thus featuring an
inductively-defined domain.

\begin{figure}
\begin{spec}
class Eq a => Lat a where bottom :: a; (⊔) :: a -> a -> a;
lub :: Lat a => [a] -> a; kleeneFix :: Lat a => (a -> a) -> a
instance (Ord k, Lat v) => Lat (k :-> v) where bottom = emp; (⊔) = Map.unionWith (⊔)
\end{spec}
%kleeneFix f = go (f bottom) where go x = let x' = f x in if x' ⊑ x then x' else go x'
\caption{Order theory and Kleene fixpoint}
\label{fig:lat}
\end{figure}

\begin{figure}
\begin{code}

data U = U0 | U1 | Uω; instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0 ⊔ u = u
  u ⊔ U0 = u
  U1 ⊔ U1 = U1
  _ ⊔ _ = Uω
{-" \fi "-}
data UT a = Uses (Name :-> U) a

instance Monad UT where
  return a = Uses emp a
  Uses φ1 a >>= k | Uses φ2 b <- k a = Uses (φ1+φ2) b

instance IsTrace UT where
  step (Lookup x)  (Uses φ a)  = Uses (φ + ext emp x U1) a
  step _           τ           = τ
\end{code}
\caption{|IsTrace| instance for semantic usage abstraction}
\label{fig:usg-abs}
\end{figure}

\begin{figure}
\begin{code}
data UValue = Nop; type UD = UT UValue

nopD :: UD
nopD = Uses emp Nop

manify :: UD -> UD
manify (Uses φ Nop) = Uses (φ+φ) Nop

instance IsValue UT UValue where
  retStuck       = nopD
  retFun f       = manify (f nopD)
  retCon _ ds    = manify (foldr (+) nopD ds)
  apply Nop d    = manify d
  select Nop fs  = lub [ f (replicate (conArity k) nopD) | (k,f) <- fs ]

instance Lat UD where
  bottom = nopD
  Uses φ1 Nop ⊔ Uses φ2 Nop = Uses (φ1 ⊔ φ2) Nop

instance HasAlloc UT UValue where alloc f = pure (kleeneFix f)
\end{code}
%if style == newcode
\begin{code}
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

instance Plussable (Name :-> U) where
  (+) = Map.unionWith (+)

instance Show a => Show (UT a) where
  show (Uses φ _) = show φ

instance Applicative UT where
  pure a = Uses emp a
  (<*>) = ap

instance Show UValue where
  show Nop = ""

instance Plussable UD where
  Uses us1 _ + Uses us2 _ = Uses (us1 + us2) Nop
\end{code}
%endif
\caption{Naïve usage analysis via |IsValue| and |HasAlloc|}
\label{fig:abs-usg}
\end{figure}

\subsection{Usage analysis}

The gist of usage analysis is that it collects upper bounds for the number
$\LookupT$ transitions per variable.
We can encode this intuition in the custom trace type |UT| in \Cref{fig:usg-abs}
that will take the place of |T|.
|UT| collects the number of transitions per variable in a usage environment
|Name :-> U|, with the matching |Monad| and |IsTrace| instances.
Whenever we omit definitions for |(⊔)| and |(+)| (such as for |U| and
|Name :-> U|), they follows straightforwardly from \Cref{fig:usage}.

If we had no interest in a terminating analysis, we could already make do
with the induced \emph{semantic usage abstraction} |ByName UT|:

< ghci> eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)
$\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: D (ByName UT)}$

Of course, this will diverge whenever the object program diverges.
Perhaps interestingly, we have not needed any order theory so far, because the
abstraction is a precise fold over the program trace, thanks to the concrete
|Value|s manipulated.

If we want to assess usage cardinality statically, we have to find a more abstract
representation of |Value|.
\Cref{fig:abs-usg} gives on such candidate |UValue|, a type containing a single
inhabitant |Nop|, so it is the simplest abstraction possible.
It is a matter of simple calculation to see that |eval e {-"\tr_Δ"-} :: UD|
indeed computes the same result as $\semusg{\pe}_{\tr_Δ}$ (given an appropriate
encoding of $\tr_Δ$ as a |Name :-> U| and an |e| without data types), once we
have understood the type class instances at play.

This abstraction is fundamentally encoded in the |IsValue| instance:
|retStuck|,|retFun| and |retCon| correspond to abstraction functions from
concrete value to abstract representation, and |apply| and |select| encode
the concretisation of operations on functions and constructors in terms of
the abstract domain |UD|.

When a |Nop| value is |apply|'d to an argument, the result is that of
evaluating that argument many times (note that it is enough to evaluate twice in
|U|), corresponding exactly to the $ω * d$ in the application case of
\Cref{fig:usage}.
When a |Nop| value is |select|ed, the result is that of evaluating the case
alternatives |fs| with |nopD| for field denotations of the corresponding
constructor, then returning the least upper bound |lub| of all alternatives.
Such a |nopD| is simply an inert denotation that does not contribute any uses
itself, but crucially distributes the |Nop| value to field accesses inside |fs|,
leading to conservative approximation in turn.

Dually, when a constructor application is returned in |retCon|, all the fields
are evaluated eagerly, and many times, conservatively approximating potential
use of any of the fields in the future.
This justifies passing |nopD| for field denotations in |select|; the fields have
already been ``squeezed dry'' in |retCon|.
Likewise, when returning a function in |retFun|, that function is ``squeezed
dry'' by passing it a |nopD| and |manify|ing the result, thus accounting for
uses inside the function body at any potential call site.
(Recall that uses of the concrete argument at the call site is handled by
|apply|.)

The final key to a terminating definition is in swapping out the fixpoint
combinator via a |HasAlloc| instance for |UValue| that computes an
order-theoretic Kleene fixpoint (\cf. \Cref{fig:lat}) instead of |fix| (which
only works for a productive |f|).
The Kleene fixpoint exists by monotonicity and finiteness of |UD|.

Our naive usage analysis yields the same result as the semantic usage
abstraction for simple examples:

< ghci> eval (read "let i = λx.x in let j = λy.y in i j j") emp :: UD
$\perform{eval (read "let i = λx.x in let j = λy.y in i j j") emp :: UD}$
\\[\belowdisplayskip]

\noindent
However, there are many examples where the results are approximate:
< ghci> eval (read "let i = λx.x in let j = λy.y in i j") emp :: D (ByName UT)
$\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp  :: D (ByName UT)}$
< ghci> eval (read "let i = λx.x in let j = λy.y in i j") emp :: UD
$\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp  :: UD}$
< ghci> eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp :: D (ByName UT)
$\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp  :: D (ByName UT)}$
< ghci> eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp :: UD
$\perform{eval (read "let z = Z() in case Z() of { Z() -> Z(); S(n) -> z }") emp  :: UD}$
\\[\belowdisplayskip]
\noindent
