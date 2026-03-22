%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures
% Need the -XPartialTypeSignatures for the CbNeed example, for some weird reason
%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints -Wno-unused-matches #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Interpreter where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Show (showListWith)
import Control.Monad
import Control.Monad.Trans.State
import Exp

instance {-# OVERLAPPING #-} Show (Maybe Value) where
  show Nothing = "\\bot"
  show (Just a) = "\\mathtt{Just}(" ++ show a ++ ")"
instance {-# OVERLAPPING #-} Show (Maybe ValueNeed) where
  show Nothing = "\\bot"
  show (Just a) = "\\mathtt{Just}(" ++ show a ++ ")"
instance Show Event where
  show (Look x) = "\\LookupT(" ++ x ++ ")"
  show App1 = "\\AppIT"
  show App2 = "\\AppET"
  show Case1 = "\\CaseIT"
  show Case2 = "\\CaseET"
  show Let0 = "\\LetOT"
  show Let1 = "\\LetIT"
  show Upd = "\\UpdateT"
instance Show a => Show (T a) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret a) = "\\langle "++show a++"\\rangle "
instance {-# OVERLAPPING #-} Show a => Show (T (Maybe a)) where
  show (Step e t) = show e ++ "\\xhookrightarrow{\\hspace{1.1ex}}" ++ show t
  show (Ret Nothing)  = "..."
  show (Ret (Just a)) = "\\langle "++show a++"\\rangle "
instance Show Value where
  show (Fun _) = "\\lambda"
  show (Con k _) = "\\mathit{Con}(" ++ show k ++ ")"
  show Stuck = "\\lightning"
instance Show ValueNeed where
  show (FunNeed _) = "\\lambda"
  show (ConNeed k _) = "\\mathit{Con}(" ++ show k ++ ")"
  show StuckNeed = "\\lightning"
instance Show ValueVInit where
  show (FunVInit _) = "\\lambda"
  show (ConVInit k _) = "\\mathit{Con}(" ++ show k ++ ")"
  show StuckVInit = "\\lightning"
instance Show (TNeed a) where
  show _ = "\\wild"
instance Show (TVInit a) where
  show _ = "\\wild"
instance {-# OVERLAPPING #-} (Show v) => Show (Addr :-> v) where
  showsPrec _ = showListWith (\(k,v) -> shows k . showString "\\!\\! \\mapsto \\!\\! " . shows v) . Map.toList
instance {-# OVERLAPPING #-} (Show v) => Show (Name :-> v) where
  showsPrec _ = showListWith (\(k,v) -> showString "\\mathit{" . showString k . showString "} \\! \\mapsto \\! " . shows v) . Map.toList

takeT :: Int -> T a -> T (Maybe a)
takeT 0 _ = return Nothing
takeT _ (Ret a) = return (Just a)
takeT n (Step e t) = Step e (takeT (n-1) t)
\end{code}
%endif

\section{A Denotational Interpreter}
\label{sec:interp}

In this section, we present a generic \emph{denotational interpreter}%
\footnote{This term was coined by \citet{Might:10}. We find it fitting,
because a denotational interpreter is both a \emph{denotational
semantics}~\citep{ScottStrachey:71} as well as a total \emph{definitional
interpreter}~\citep{Reynolds:72}.}
for the language defined in \cref{sec:lang} which we instantiate with different
semantic domains.
Instantiated at \emph{concrete} semantic domains, the interpreter becomes a
semantics for the language.
To this end, we will see that the interpreter definition can be easily adjusted
to different \emph{evaluation strategies} (call-by-name, call-by-value, call-by-need)
and observes rich \emph{operational detail}.
Other semantic domains give rise to useful \emph{summary-based} static
analyses such as usage analysis in \Cref{sec:abstraction}.
The major contribution of denotational interpreters is that the derived summary-based
analyses may observe operational detail in an intuitive and semantically
meaningful way, while still sharing structure with the semantics.
Adhering to the denotational interpreter pattern for analyses pays off in
that it enables sharing of soundness proofs, thus drastically simplifying the
soundness proof obligations per derived analysis (\Cref{sec:soundness}).

Denotational interpreters can be implemented in any higher-order language such as OCaml, Scheme or Java with explicit thunks, but we picked Haskell for convenience.%
\footnote{We extract from this document runnable Haskell files which we add as a Supplement, containing the complete definitions. Furthermore, the (terminating) interpreter outputs are directly generated from this extract.}

\begin{figure}
\begin{minipage}{0.49\textwidth}
\begin{spec}
data Exp
  =  Var Name | Let Name Exp Exp
  |  Lam Name Exp | App Exp Name
  |  ConApp Tag [Name] | Case Exp Alts
type Name = String
type Alts = Tag :-> ([Name],Exp)
data Tag = ...; conArity :: Tag -> Int
\end{spec}
\caption{Syntax}
\label{fig:syntax}
\end{minipage}%
\begin{minipage}{0.51\textwidth}
\begin{code}
type (:->) = Map; emp :: Ord k => k :-> v
ext :: Ord k => (k :-> v) -> k -> v -> (k :-> v)
exts :: Ord k  => (k :-> v) -> [k] -> [v]
               -> (k :-> v)
(!) :: Ord k => (k :-> v) -> k -> v
dom :: Ord k => (k :-> v) -> Set k
(∈) :: Ord k => k -> Set k -> Bool
(<<) :: (b -> c) -> (a :-> b) -> (a :-> c)
assocs :: (k :-> v) -> [(k,v)]
\end{code}
%if style == newcode
\begin{code}
emp = Map.empty
ext ρ x d = Map.insert x d ρ
exts ρ xs ds = foldl (uncurry . ext) ρ (zip xs ds)
singenv x d = Map.singleton x d
(<<) = Map.map
infixr 9 <<
(!) = (Map.!)
dom = Map.keysSet
(∈) = Set.member
assocs = Map.assocs
\end{code}
%endif
\caption{Environments}
\label{fig:map}
\end{minipage}
\end{figure}

\subsection{Semantic Domain} \label{sec:dna}

Just as traditional denotational semantics, denotational interpreters
assign meaning to programs in some semantic domain.
Traditionally, the semantic domain |D| comprises \emph{semantic values} such as
base values (integers, strings, etc.) and functions |D -> D|.
One of the main features of these semantic domains is that they lack
\emph{operational}, or, \emph{intensional detail} that is unnecessary to
assigning each observationally distinct expression a distinct meaning.
For example, it is not possible to observe evaluation cardinality, which
is the whole point of analyses such as usage analysis (\Cref{sec:abstraction}).

A distinctive feature of our work is that our semantic domains are instead
\emph{traces} that describe the \emph{steps} taken by an abstract machine, and
that \emph{end} in semantic values.
It is possible to describe usage cardinality as a property of the traces
thus generated, as required for a soundness proof of usage analysis.
We choose |DName|, defined below, as the first example of such a semantic domain,
because it is simple and illustrative of the approach.
Instantiated at |DName|, our generic interpreter will produce precisely the
traces of the by-\textbf{\textrm{na}}me variant of the Krivine machine in
\Cref{fig:lk-semantics}.%
\footnote{For a realistic implementation, we would define |D| as a |newtype| to
keep type class resolution decidable and non-overlapping. We will however stick
to a |type| synonym in this presentation in order to elide noisy wrapping and
unwrapping of constructors.}

\begin{minipage}{0.62\textwidth}
\begin{code}
data T v = Step Event (T v) | Ret v
ifPoly(data Event  =  Look Name | App1 | App2
                   |  Let1 | Case1 | Case2)
type DName = T Value
data Value = Stuck | Fun (DName -> DName) | Con Tag [DName]
\end{code}
\end{minipage}
\begin{minipage}{0.38\textwidth}
\begin{spec}
instance Monad T where
  return v = Ret v
  Ret v >>= k = k v
  Step e τ >>= k = Step e (τ >>= k)
\end{spec}
%if style == newcode
\begin{code}
data Event  =  Look Name | Upd | App1 | App2
            |  Let0 | Let1 | Case1 | Case2
instance Functor T where
  fmap f (Ret a) = Ret (f a)
  fmap f (Step e t) = Step e (fmap f t)
instance Applicative T where
  pure = Ret
  (<*>) = ap
instance Monad T where
  Ret v >>= k = k v
  Step e τ >>= k = Step e (τ >>= k)
\end{code}
%endif
\end{minipage}
\noindent
A trace |T| either returns a value (|Ret|) or makes a small-step transition (|Step|).
Each step |Step ev rest| is decorated with an event |ev|, which describes what happens in that step.
For example, event |Look x| describes the lookup of variable |x :: Name| in the environment.
Note that the choice of |Event| is use-case (\ie semantics- and analysis-) specific and suggests
a spectrum of intensionality, with |data Event = Unit| on the more abstract end
of the spectrum and arbitrary syntactic detail attached to each of |Event|'s
constructors at the intensional end of the spectrum.%
\footnote{If our language had facilities for input/output and more general
side-effects, we could have started from a more elaborate trace construction
such as (guarded) interaction trees~\citep{interaction-trees,gitrees}.}

A trace in |DName = T (Value T)| eventually terminates with a |Value| that is
either stuck (|Stuck|), a function waiting to be applied to a domain value
(|Fun|), or a constructor application giving the denotations of its
fields (|Con|).
%|Value| is thus just a standard denotational encoding of its syntactic counterpart |Lam|/|ConApp|, devoid of any syntax. \slpj{I don't know what that sentence adds or even means. Omit?}
%\sg{I clarified, mentioining |Lam|/|ConApp|. This point is one of the main distinctions between operational semantics and denotational semantics.}
%\slpj{I still don't know what ``devoid of syntax'' means.  Omit?}
We postpone worries about well-definedness and totality of this encoding to
\Cref{sec:totality}.

\begin{figure}
\begin{minipage}{0.55\textwidth}
\begin{code}
eval  ::  (Trace d, Domain d)
      =>  Exp -> (Name :-> d) -> d
eval e ρ = case e of
  Var x  | x ∈ dom ρ  -> ρ ! x
         | otherwise  -> domainfun(stuck)
  Lam x body ->
    domainfun(fun) x {-" \iffalse "-}(label e){-" \fi "-} (\d -> tracefun(step) App2 (eval body ((ext ρ x d))))
  App e x  | x ∈ dom ρ  ->
               tracefun(step) App1 (domainfun(apply) (eval e ρ) (ρ ! x))
           | otherwise  -> domainfun(stuck)
  Let x e1 e2 -> domainfun(bind) {-" \iffalse "-}x{-" \fi "-}
    (\d1 -> eval e1 (ext ρ x (tracefun(step) (Look x) d1)))
    (\d1 -> tracefun(step) Let1 (eval e2 (ext ρ x (tracefun(step) (Look x) d1))))
  ConApp k xs
    | all (∈ dom ρ) xs, length xs == conArity k
    -> domainfun(con) {-" \iffalse "-}(label e){-" \fi "-} k (map (ρ !) xs)
    | otherwise
    -> domainfun(stuck)
  Case e alts ->
    tracefun(step) Case1 (domainfun(select) (eval e ρ) (cont << alts))
    where
       cont (xs, er) ds  |  length xs == length ds
                         =  tracefun(step) Case2 (eval er (exts ρ xs ds))
                         |  otherwise
                         =  domainfun(stuck)
\end{code}
\end{minipage}%
\begin{minipage}{0.44\textwidth}
\begin{code}
class Trace d where
  step :: Event -> d -> d

class Domain d where
  stuck :: d
  fun :: Name -> {-" \iffalse "-}Label -> {-" \fi "-}(d -> d) -> d
  apply :: d -> d -> d
  con :: {-" \iffalse "-}Label -> {-" \fi "-}Tag -> [d] -> d
  select :: d -> (Tag :-> ([d] -> d)) ->  d
  bind :: {-" \iffalse "-}Name -> {-" \fi "-}(d -> d) -> (d -> d) -> d
\end{code}
\\[-2.5em]
\subcaption{Interface of traces and values}
  \label{fig:trace-classes}
\begin{code}
evalName e ρ = eval e ρ :: DName

instance Trace (T v) where
  tracefun(step) = Step

instance Domain DName where
  domainfun(stuck) = return Stuck
  domainfun(fun) _ {-" \iffalse "-}_{-" \fi "-} f = return (Fun f)
  domainfun(apply)  d a = d >>= \v -> case v of
    Fun f -> f a; _ -> domainfun(stuck)
  domainfun(con) {-" \iffalse "-}_{-" \fi "-} k ds = return (Con k ds)
  domainfun(select) dv alts = dv >>= \v -> case v of
    Con k ds | k ∈ dom alts  -> (alts ! k) ds
    _                        -> domainfun(stuck)
  domainfun(bind) # rhs body = let d = rhs d in body d
\end{code}
\\[-2.5em]
\subcaption{Concrete by-name semantics for |DName|}
  \label{fig:trace-instances}
\end{minipage}%
\\[-0.5em]
\caption{Denotational Interpreter}
  \label{fig:eval}
\end{figure}

\subsection{The Interpreter}

Traditionally, a denotational semantics is expressed as a mathematical function,
often written |dsem e ρ|, to give an expression |e :: Exp| a meaning, or
\emph{denotation}, in terms of some semantic domain |D|.
The environment |ρ :: Name :-> D| gives meaning to the free variables of |e|,
by mapping each free variable to its denotation in |D|.
We sketch the Haskell encoding of |Exp| in \Cref{fig:syntax} and the API of
environments and sets in \Cref{fig:map}.
For concise notation, we will use a small number of infix operators: |(:->)| as
a synonym for finite |Map|s, with |m ! x| for looking up |x| in |m|, |emp| for
the empty map, |ext m x d| for updates, |assocs m| for a list of key-value pairs
in |m|, |f << m| for mapping |f| over every value in |m|, |dom m| for the set of
keys present in the map, and |(`elem`)| for membership tests in that set.

Our denotational interpreter |eval :: Exp -> (Name :-> DName) -> DName| can
have a similar type as |dsem|.
However, to derive both dynamic semantics and static analyses as instances of the same
generic interpreter |eval|, we need to vary the type of its semantic domain,
which is naturally expressed using type class overloading, thus:
\[
|eval  ::  (Trace d, Domain d) =>  Exp -> (Name :-> d) -> d|.
\]
We have parameterised the semantic domain |d| over two type classes
--- |Trace| and |Domain| --- whose signatures are given in
\Cref{fig:trace-classes}.
%\footnote{One can think of these type classes as a fold-like final encoding~\citep{Carette:07} of a domain. However, the significance is in the \emph{decomposition} of the domain, not the choice of encoding.}
Each of the two type classes offer knobs that we will tweak to derive
different evaluation strategies as well as static analyses.

\Cref{fig:eval} gives the complete definition of |eval| together with type class
instances for domain |DName| that we introduced in \Cref{sec:dna}.
We added visible cues in the form of gray boxes in \Cref{fig:eval} to highlight where
type class method calls (\ie, calls to function parameters) happen, as opposed
to regular function calls of known definitions.
These hooks are filled in by the type class instances for |DName| when the
polymorphic interpreter is instantiated at |DName|, so we also highlighted its
implementations.
These type class instances suffice to actually run the denotational interpreter to produce traces.

Having fixed the type class instances for |DName| in \Cref{fig:trace-instances},
we write |evalName e ρ| for |eval e ρ| instantiated for domain |DName|.
We introduce similar shorthands |evalNeed1| and |evalUsg1| for the by-need and
usage analysis instantiations in \Cref{sec:by-need-instance,sec:abstraction}.

We use |read :: String -> Exp| as a parsing function and a |Show| instance for
|D τ| that displays traces.
For example, we can evaluate the expression $\Let{i}{\Lam{x}{x}}{i~i}$ like
this:

< ghci> eval (read "let i = λx.x in i i") emp :: DName
$\perform{eval (read "let i = λx.x in i i") emp :: DName}$,
\\[\belowdisplayskip]
\noindent
where $\langle\lambda\rangle$
means that the trace ends in a |Fun| value.
We cannot generally print |DName| or |Fun|ctions thereof, but in this case the result would be the value $\Lam{x}{x}$.
This is in direct correspondence to the earlier call-by-name small-step trace
\labelcref{ex:trace} in \Cref{sec:op-sem}.
Henceforth, we write expressions in the mathematical meta notation of
\Cref{sec:lang} rather than as Haskell strings, e.g.,
|evalName (({-" \Let{i}{\Lam{x}{x}}{i~i} "-})) emp| in place of
|evalName (read "let i = λx.x in i i") emp|.
\Cref{sec:walkthrough} walks through the intermediate reduction steps for this
example; for now we focus on a general description of the interpreter.

The definition of |eval|, given in \Cref{fig:eval}, is by structural recursion over the input expression.
For |Lam x body|, the interpreter recursively computes the body's denotation in
an extended environment, prefixes it with |step App2|, and wraps the result via
|fun|.
The details of this necessarily depend on the particular |Domain|, so both
|step| and |fun| are methods of this type class.
The other cases follow a similar pattern:
each does some structural work before handing off to domain-specific type class methods.
The name |x| passed to |fun| is ignored for |DName| but needed by abstract
domains (\Cref{sec:abstraction}).
The |bind| method gives meaning to recursive let bindings via two
functionals, one for the right-hand side and one for the body.
For |DName| (\Cref{fig:trace-instances}), |bind| ties the knot via a
\emph{guarded fixpoint} |d = rhs d| and passes |d| to |body|, yielding
call-by-name evaluation.%
\footnote{Strict languages can define the guarded fixpoint as |d () = rhs (d ())|.}
Crucially, the |Let| case of |eval| also wraps every future reference to the bound
variable |x| in |step (Look x)|, making variable lookup observable --- a mechanism
we explore in \Cref{sec:walkthrough}.

A helpful analogy to abstract machine reduction by one of our reviewers is in order.
Every expression that appears as control expression in the LK machine from
\Cref{sec:op-sem} is a subexpression of the original program.
The meaning of a subexpression is determined purely in terms of what happens
when it is in the control position of valid configurations.
By analogy, the denotational interpreter maps the subexpression $\pe$ to a trace
prefix that corresponds to evaluating $\pe$ as the focus expression of a valid
machine configuration $(\pe, ρ, μ, κ)$.
The semantic value describes how that trace continues when the focus expression
reaches a value, indexed by the evaluation context $(ρ, μ, κ)$.
The following walkthrough makes this analogy concrete.

\subsubsection{Walkthrough: From Compositional Definition to Operational Trace}
\label{sec:walkthrough}

Before exploring further instances such as for by-need evaluation, let us
pause and trace through our concrete example from above in detail, to build
intuition for how a compositional definition can produce small-step operational
traces.
We fix the by-name domain |DName| and work through $\Let{i}{\Lam{x}{x}}{i~i}$
step by step, showing which clause of |eval| fires.

The goal is to recover the by-name trace from \labelcref{ex:trace} in
\Cref{sec:op-sem},
$\perform{evalName (read "let i = λx.x in i i") emp}$,
purely from the compositional structure of |eval|.
We inline the |DName| type class instances (\Cref{fig:trace-instances})
as we see fit.
To save horizontal space, we'll abbreviate |Step| to |S|.
\begin{align}
    & |eval (({-" \Let{i}{\Lam{x}{x}}{i~i} "-})) emp| \notag \\
={} & |let d = eval (({-" \Lam{x}{x} "-})) emp in S Let1 (eval (({-" i~i "-})) (singenv "i" (S (Look "i") d)))| \label{eqn:eval-ex1} \\
={} & |let d = eval (({-" \Lam{x}{x} "-})) emp in S Let1 (S App1 (apply (S (Look "i") d) (S (Look "i") d)))| \label{eqn:eval-ex2} \\
={} & |let d = Ret (Fun (\d -> S App2 d)) in S Let1 (S App1 (apply (S (Look "i") d) (...))| \label{eqn:eval-ex3} \\
={} & |let d = ... ^^ in S Let1 (S App1 (S (Look "i") (S App2 (S (Look "i") d))))| \label{eqn:eval-ex4} \\
={} & |S Let1 (S App1 (S (Look "i") (S App2 (S (Look "i") (Ret (Fun (\d -> S App2 d)))))))| \label{eqn:eval-ex5} \\
={} & \perform{evalName (read "let i = λx.x in i i") emp} \notag
\end{align}
\noindent
Step (\ref{eqn:eval-ex1}) unfolds the definition of the |Let| case and the |bind| implementation.
The |bind| for |DName| computes a guarded fixpoint |let d = rhs d in body d|
and the |Let| case of |eval| wraps every future reference to |i| in
|Step (Look "i") d|, so a |Look "i"| event will be emitted at each use of |i|.
Variable lookup becomes observable because it is wired into the environment
at the \emph{binding site}.

Step (\ref{eqn:eval-ex2}) unfolds |eval| for the |App| case ($i~i$) and |Var|
case ($i$) in the application head.
Both cases look up |"i"| in the environment, yielding |Step (Look "i") d| for both
the function and argument positions.
Step (\ref{eqn:eval-ex3}) evaluates the right-hand side:
|eval| dispatches on the |Lam| case for $\Lam{x}{x}$, and |fun| for |DName| wraps
the body denotation in |Ret (Fun ^^ ...)|.
Note the |Step App2| pre-wired inside the
|Fun| value --- it will be emitted whenever this function is applied.
Since $\Lam{x}{x}$ does not mention $i$, the definition of |d| is independent of
its self-reference, and the guarded fixpoint is immediate.

Step (\ref{eqn:eval-ex4}) is the key one: it unfolds |apply| for |DName| using monadic
bind |(>>=)| for |T|.  Recall that |Step ev tau >>= k = Step ev (tau >>= k)|
threads through |Step| constructors, and |Ret v >>= k = k v| dispatches on
the value.  So |(>>=)| replays the |Look "i"| event from the function
denotation, reaches the |Fun| value inside |d|, and calls |(\d -> Step App2 d)| with
argument |Step (Look "i") d| (elided as |...| in the previous line to save space).
Step (\ref{eqn:eval-ex5}) substitutes |d|, and the final line prints the trace
in familiar meta notation, recovering the by-name trace from \Cref{sec:op-sem}.

No single clause sees the full trace; each contributes a fragment, and |(>>=)| for
|T| glues them into a coherent whole.

\subsubsection{Further Examples}
We conclude this subsection with a few input/output pair examples.
First we demonstrate that our interpreter is \emph{productive}:
we can observe prefixes of diverging traces without risking a looping
interpreter.
To observe prefixes, we use a function |takeT :: Int -> T v -> T (Maybe v)|:
|takeT n τ| returns the first |n| steps of |τ| and replaces the final value
with |Nothing| (printed as $...$) if it goes on for longer.

< ghci> takeT 5 (evalName (({-" \Let{x}{x}{x} "-})) emp) :: T (Maybe Value)
$\perform{takeT 5 $ evalName (read "let x = x in x") emp :: T (Maybe Value)}$

< ghci> takeT 9 (evalName (({-" \Let{w}{\Lam{y}{y~y}}{w~w} "-})) emp) :: T (Maybe Value)
$\perform{takeT 9 $ evalName (read "let w = λy. y y in w w") emp :: T (Maybe Value)}$
\\[\belowdisplayskip]
\noindent
The reason |eval| is productive is due to the coinductive nature of |T|'s
definition in Haskell.%
\footnote{In a strict language, we need to introduce a thunk in
the definition of |Step|, \eg @Step of event * (unit -> 'a t)@.}
Productivity requires that the monadic bind operator |(>>=)| for |T|
guards the recursion, as in the delay monad of \citet{Capretta:05}.

Data constructor values are printed as $Con(K)$, where $K$ indicates the
|Tag|.
Data types allow for interesting ways (type errors) to get |Stuck| (\ie the
\textbf{wrong} value of \citet{Milner:78}), printed as $\lightning$:

< ghci> evalName (({-" \Let{\mathit{zro}}{Z}{\Let{\mathit{one}}{S~\mathit{zro}}{\Case{one}{S~\mathit{zz} \rightarrow \mathit{zz}}}} "-})) emp :: DName
$\perform{evalName (read "let zro = Z() in let one = S(zro) in case one of { S(zz) -> zz }") emp :: DName}$

< ghci> evalName (({-" \Let{\mathit{zro}}{Z}{\mathit{zro}~\mathit{zro}} "-})) emp :: DName
$\perform{evalName (read "let zro = Z() in zro zro") emp :: DName}$

\subsection{Call-by-need}
\label{sec:by-need-instance}

By varying the definition of |D| and its domain instance, we can endow our
language |Exp| with different evaluation strategies.
The main focus of this work lies on the call-by-need domain |DNeed| that we
introduce in this subsection.
Its model of memoisation brings with it all the usual semantic complexities
that arise for semantic domains with higher-order state (\ie, that of a strict
functional language with ref cells), so we think it is enlightening to study
even if the reader's main interest lies in strict languages.
Of course, it is also possible to adjust the interpreter for call-by-value,
which requires a separate @let rec@ construct or lazy initialization techniques.
We demonstrate this in the Appendix.

In \Cref{sec:soundness}, we build on |DNeed| to prove usage analysis sound \wrt
by-need evaluation.
It turns out that the interpreter thus derived is the --- to our knowledge ---
first denotational semantics for call-by-need that bisimulates the LK machine
(\Cref{sec:adequacy}).

\begin{figure}
\begin{code}
type Addr = Int; type Heap = Addr :-> DNeed; nextFree :: Heap -> Addr
ifPoly(data Event  =  ... | Upd)
newtype TNeed v = TNeed { unTNeed :: Heap -> T (v, Heap) }

type DNeed = TNeed ValueNeed;
ifPoly(data ValueNeed = Stuck | Fun (DNeed -> DNeed) | Con Tag [DNeed])
evalNeed e ρ μ = unTNeed (eval e ρ :: DNeed) μ

instance Monad TNeed where
  return v = TNeed (\μ -> return (v, μ))
  x >>= f = TNeed (\μ -> unTNeed x μ >>= \(v, μ) -> unTNeed (f v) μ)
getN  :: TNeed Heap;           getN    = TNeed (\ μ -> return (μ, μ))
putN  :: Heap -> TNeed (); ^^  putN μ  = TNeed (\ _ -> return ((), μ))
instance Trace (TNeed v) where step e m = TNeed (step e . unTNeed m)

fetchN :: Addr -> DNeed; fetchN a = getN >>= \μ -> μ ! a

memoN :: Addr -> DNeed -> DNeed
memoN a d = d >>= \v -> TNeed (upd v)
  where  upd StuckNeed  μ = return (StuckNeed :: ValueNeed, μ)
         upd v          μ = step Upd (return (v, ext μ a (memoN a (return v))))

instance Domain DNeed where
  stuck = return StuckNeed
  fun _ _ f = return (FunNeed f)
  apply  d a = d >>= \v -> case v of
    FunNeed f -> f a; _ -> stuck
  con _ k ds = return (ConNeed k ds)
  select dv alts = dv >>= \v -> case v of
    ConNeed k ds | k ∈ dom alts  -> (alts ! k) ds
    _                            -> stuck
  bind # rhs body = do  μ <- getN
                        let a = nextFree μ
                        putN (ext μ a (memoN a (rhs (fetchN a))))
                        body (fetchN a)
\end{code}
%if style == newcode
\begin{code}
nextFree h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

data ValueNeed = StuckNeed | FunNeed (DNeed -> DNeed) | ConNeed Tag [DNeed]

deriving via StateT Heap T instance Functor TNeed
deriving via StateT Heap T instance Applicative TNeed

\end{code}
%endif
\\[-1em]
\caption{Call-by-need}
\label{fig:by-need}
\end{figure}

The use of a stateful heap is essential to the call-by-need evaluation strategy
in order to enable memoisation.
So how do we vary the trace type |τ| such that |τ Value| accommodates state?
We certainly cannot perform the heap update by updating entries in |ρ|,
because those entries are immutable once inserted, and we do not want to change
the generic interpreter.
That rules out $|τ| \cong |T|$ (as for |DName|), because then repeated
occurrences of the variable |x| must yield the same trace |ρ ! x|.
However, the whole point of memoisation is that every evaluation of |x| after
the first one leads to a potentially different, shorter trace.
This implies we have to \emph{paramaterise} every occurrence of |x| over the
current heap |μ| at the time of evaluation, and every evaluation of |x| must
subsequently update this heap with its value, so that the next evaluation
of |x| returns the value directly.
In other words, we need a representation $|DNeed| \cong |Heap -> T (Value,
Heap)|$.

The by-need trace type |TNeed| in \Cref{fig:by-need} solves this type equation.
It's |Monad| instance is that of a standard state transformer monad.
That is, it passes around updated |Heap|s adjoined with semantic values, reusing
the |Monad| instance for |T|.
Its key operations |getN| and |putN| are given in \Cref{fig:by-need}.

So the denotation of an expression is no longer a trace, but rather a
\emph{stateful function returning a trace} with state |Heap| in
which to allocate call-by-need thunks.
The |Trace| instance of |TNeed| forwards to that of |T|, pointwise
over heaps.

The |Domain| instance is mostly the same as for |DName|.
In fact, the implementations of the |stuck|, |lam|, |app|, |con| and |select|
methods are \emph{syntactically identical} to
\Cref{fig:trace-instances}; the different semantics follows entirely from the
new |Monad| and |Trace| instances, and the only concern of those is to thread
the |Heap| around.
However, |bind| is the key method that differs for |DNeed|, because that is the
only place where thunks are allocated.
The implementation of |bind| designates a fresh heap address |a|
to hold the denotation of the right-hand side.
Both |rhs| and |body| are called with |fetchN a|, a denotation that looks up |a|
in the heap and runs it.
If we were to omit the |memo| action explained next, we would thus have
recovered another form of call-by-name semantics based on mutable state instead
of guarded fixpoints such as for |DNeed|.
The whole purpose of the |memo a d| combinator then is to \emph{memoise} the
computation of |d| the first time we run the computation, via |fetchN a| in the
|Var| case of |evalNeed2|.
So |memo a d| yields from |d| until it has reached a value, and then |upd|ates
the heap after an additional |Upd| step, where |Upd| is a new kind of |Event|.
Repeated access to the same variable will run the replacement |memo a (return
v)|, which immediately yields |v| after performing a |step Upd| that does
nothing.%
\footnote{More serious semantics would omit updates after the first
evaluation as an \emph{optimisation}, \ie update with |ext μ a (return v)|,
but doing so complicates relating the semantics to \Cref{fig:lk-semantics},
where omission of update frames for values behaves differently.
For now, our goal is not to formalise this optimisation, but rather to show
adequacy \wrt an established semantics.}

Although the code is carefully written, it is worth stressing how
compact and expressive it is.
We were able to move from traces to stateful traces just by wrapping traces |T|
in a state transformer |TNeed|, isolating the implementation of memoisation to a
single semantic primitive |memo|, with only minimal changes to add the |Upd|
event to the main |eval| function.
The semantic intuition built for the by-name interpreter compositionally carries
over to the by-need interpreter.
We think that this yields a comparatively simple encoding of a denotational
by-need semantics.

\subsubsection{Walkthrough: Memoisation in Action}
\label{sec:walkthrough-need}

Just as \Cref{sec:walkthrough} traced through |eval| for the by-name domain
|DName|, let us now trace through the characteristic by-need example from trace
\labelcref{ex:trace2} in \Cref{sec:op-sem}, $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$,
to build intuition for how the |DNeed| type class instances model memoisation.
The goal is to recover the by-need trace
$\perform{evalNeed (read "let i = (λy.λx.x) i in i i") emp emp}$
in the derivation depicted in \Cref{fig:by-need-trace}, purely by equational
reasoning.
We abbreviate |Step| to |S| as before and write |many (S ev)| to abbreviate a
sequence of |Step| constructors with events |ev|.
We also omit wrapping and unwrapping of |TNeed| constructors,
so that |DNeed| computations can be applied directly as functions of type
|Heap -> T (ValueNeed, Heap)|;
thus the current heap state will often appear as an additional argument.

\begin{figure}
\begin{spec}
   evalNeed (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i} "-})) emp emp
=  let a = nextFree emp in {-" \hfill\textsc{(1)} "-}
   let μ1 = singenv a (memoN a (evalNeed2 (({-" (\Lam{y}{\Lam{x}{x}})~i "-})) (singenv "i" (S (Look "i" (fetchN a)))))) in
   S Let1 (evalNeed (({-" i~i "-})) (singenv "i" (S (Look "i" (fetchN a)))) μ1)
=  S Let1 (evalNeed (({-" i~i "-})) ρ1 μ1) {-" \hfill\textsc{(2)} "-}
=  S Let1 (S App1 (apply (S (Look "i") (fetchN 0)) (S (Look "i") (fetchN 0)) μ1)) {-" \hfill\textsc{(3)} "-}
=  S Let1 (S App1 (S (Look "i") (fetchN 0 μ1) >>= k1)) {-" \hfill\textsc{(4)} "-}
=  S Let1 (S App1 (S (Look "i") (memoN 0 (evalNeed2 (({-" (\Lam{y}{\Lam{x}{x}})~i "-})) ρ1) μ1) >>= k1)) {-" \hfill\textsc{(5)} "-}
=  S Let1 (S App1 (S (Look "i") (evalNeed (({-" (\Lam{y}{\Lam{x}{x}})~i "-})) ρ1 μ1 >>= k2))) {-" \hfill\textsc{(6)} "-}
=  S Let1 (S App1 (S (Look "i") (S App1 (S App2 (evalNeed (({-" \Lam{x}{x} "-})) ρ2 μ1 >>= k2))))) {-" \hfill\textsc{(7)} "-}
=  many (S ev) (evalNeed (({-" \Lam{x}{x} "-})) ρ2 μ1 >>= k2) {-" \hfill\textsc{(8)} "-}
=  many (S ev) (Ret (Fun (\d -> S App2 d), μ1) >>= k2) {-" \hfill\textsc{(9)} "-}
=  many (S ev) (S Upd (Ret (Fun (\d -> S App2 d), μ2) >>= k1)) {-" \hfill\textsc{(10)} "-}
=  many (S ev) (S Upd (S App2 (S (Look "i") (fetchN 0 μ2)))) {-" \hfill\textsc{(11)} "-}
=  many (S ev) (S Upd (S App2 (S (Look "i") (Ret (Fun (\d -> S App2 d), μ2) >>= k3)))) {-" \hfill\textsc{(12)} "-}
=  many (S ev) (S Upd (S App2 (S (Look "i") (S Upd (Ret (Fun (\d -> S App2 d), μ2)))))) {-" \hfill\textsc{(13)} "-}
=  {-" \LetIT\xhookrightarrow{}\!\AppIT\xhookrightarrow{}\!\LookupT(i)\xhookrightarrow{}\!\AppIT\xhookrightarrow{}\!\AppET\xhookrightarrow{}\!\UpdateT\xhookrightarrow{}\!\AppET\xhookrightarrow{}\!\LookupT(i)\xhookrightarrow{}\!\UpdateT\xhookrightarrow{}\!\langle (\lambda,[0\!\! \mapsto \!\! \wild]) \rangle "-}
 where
   ρ1 = singenv "i" (S (Look "i" (fetchN 0)))
   μ1 = singenv 0 (memoN 0 (evalNeed2 (({-" (\Lam{y}{\Lam{x}{x}})~i "-})) ρ1))
   k1 (v, μ') = case v of Fun f -> f (S (Look "i") (fetchN 0)); _ -> stuck
   k2 (v, μ') = upd 0 v μ' >>= k1
   ev = [Let1, App1, Look "i", App1, App2]
   ρ2 = env2 "i" (S (Look "i" (fetchN 0))) "y" (S (Look "i" (fetchN 0)))
   μ2 = singenv 0 (memoN 0 (return (Fun (\d -> S App2 d))))
   k3 (v, μ') = upd 0 v μ'
\end{spec}
\\[-1em]
\caption{Walking through by-need evaluation for $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$}
\label{fig:by-need-trace}
\end{figure}

The compositional unfolding of |eval| proceeds just as in the by-name
walkthrough of \Cref{sec:walkthrough}.
However, the |bind| implementation for |DNeed|, unfolded in Step~(1), is very
different from the guarded fixpoint tied by |DName|.
The monadic operations |>>=|, |getN| and |putN| have been immediately unfolded
and applied to the concrete empty heap |emp|.
The resulting code allocates a fresh heap address |a = 0| and stores the memoised
right-hand side |memoN 0 (...)| at that address, producing heap |μ1|.
Step~(2) inlines |a = 0| and moves |μ1| into the shared |where| clause at the
bottom of the figure.
Environment |ρ1| stores a single binding for $i$, ensuring that every future
reference to $i$ wraps the heap access |fetchN 0| in |S (Look "i")|.
This indirection through the mutable heap takes the place of the guarded fixpoint.

Step~(3) interprets the application $i~i$, as for by-name.
Step~(4) unfolds |apply|, abbreviating the beta-reduction continuation as |k1|,
and Step~(5) further unfolds |fetchN|, reading the heap entry at address~0.
Unfolding |memoN| in Step~(6) exposes the |upd| continuation, abbreviated as |k2|:
evaluate the right-hand side to a value, update the heap, then resume with |k1|.
Step~(7) evaluates the right-hand side through another beta reduction,
and Step~(8) compacts the resulting trace prefix to reclaim horizontal space.
Step~(9) unfolds |eval| for the inner lambda $\Lam{x}{x}$ to arrive at the
|Fun| value of $i$.

Step~(10) is the key one: it passes the |Fun| value to |upd| in
continuation~|k2|, which emits an |Upd| event and replaces the thunk at
address~|0| with |memoN 0 (return v)|, where |v = Fun (\d -> Step App2 d)|,
producing the updated heap |μ2| --- this is memoisation.
Step~(11) then resumes with |k1|, performing beta reduction: the |Fun| value
|\d -> Step App2 d| is called with argument |Step (Look "i") (fetchN 0)|,
emitting |App2| and triggering a second lookup of $i$.

Now the payoff: |fetchN 0| reads the \emph{updated} heap |μ2|, where the entry
is |memoN 0 (return v)|.
Since |return v| produces |v| immediately, no beta reduction occurs --- Step~(12)
simply reaches the cached value.
The |memoN| combinator emits a final |Upd| in Step~(13), a no-op since |v| is
already stored, and returns |v|.
Comparing the two $\LookupT(i)$--$\UpdateT$ brackets makes the effect of
memoisation vivid:
the first bracket ($\LookupT(i) \xhookrightarrow{} \AppIT \xhookrightarrow{} \AppET \xhookrightarrow{} \UpdateT$)
performs a beta reduction to evaluate the thunk;
the second ($\LookupT(i) \xhookrightarrow{} \UpdateT$) returns the cached
result immediately.
The final trace matches LK machine trace~\labelcref{ex:trace2} from \Cref{sec:op-sem}.

As in \Cref{sec:walkthrough}, no single clause of |eval| sees the full trace.
The generic interpreter definition is unchanged from the by-name case; all
memoisation machinery lives in |bind|, |memoN|, and |fetchN|, local to the
|DNeed| type class instances.

\begin{toappendix}
\label{sec:more-eval-strat}

In this Section, we introduce two more concrete semantic domain instances for
call-by-value.
The first by-value instance is as simple as the by-name instance, but we will see
that will not be productive because of recursive |let|.
In order to recover a total by-value semantics accepting the same language as
our lazy evaluation strategies, our second by-value instance augments
call-by-value with a lazy initialisation technique~\citep{Nakata:06} involving a
mutable heap, thus sharing its representation with |DNeed|.

\subsubsection{Call-by-value}

\begin{figure}
\begin{code}
evalValue e ρ = eval e ρ

ifPoly(data Event = ... | Let0)
ifPoly(data ValueValue = Stuck | Fun (DValue -> DValue) | Con Tag [DValue])
type DValue = T ValueValue

getValue :: T v -> v
getValue (Ret v)     = v
getValue (Step _ τ)  = getValue τ

ifPoly(instance Domain DValue where
  ...
  bind # rhs body = DValue $
    step Let0 (do  let  d = rhs (return v)          :: DValue
                        v = getValue (unByValue d)  :: Value
                   v1 <- d; body (return v1)))
\end{code}
%if style == newcode
\begin{code}
data ValueValue = StuckValue | FunValue (DValue -> DValue) | ConValue Tag [DValue]
instance Domain DValue where
  stuck = return StuckValue
  fun _ _ f = return (FunValue f)
  apply  d a = d >>= \v -> case v of
    FunValue f -> f a; _ -> stuck
  con _ k ds = return (ConValue k ds)
  select dv alts = dv >>= \v -> case v of
    ConValue k ds | k ∈ dom alts  -> (alts ! k) ds
    _                            -> stuck
  bind # rhs body =
    step Let0 (do  let  d = rhs (return v)  :: DValue
                        v = getValue d      :: ValueValue
                   v1 <- d
                   body (return v1))
\end{code}
%endif
\\[-1em]
\caption{Call-by-value}
\label{fig:by-value}
\end{figure}

Call-by-value eagerly evaluates a let-bound RHS and then substitutes its
\emph{value}, rather than the reduction trace that led to the value, into every
use site.

The call-by-value evaluation strategy is implemented by the |DValue| domain
shown in \Cref{fig:by-value}.
Function |bind| defines a denotation |d :: DValue| of the right-hand
side by mutual recursion with |v :: Value| that we will discuss
shortly.

As its first action, |bind| yields a brand-new |Let0| event that we assume was
added to the definition of |Event|, announcing in the trace that the right-hand
side of a |Let| is to be evaluated.
Then monadic bind |v1 <- d; body (return v1)| yields steps from the right-hand
side |d| until its value |v1 :: ValueValue| is reached, which is then
passed |return|ed (\ie wrapped in |Ret|) to the let |body|.
Note that the steps in |d| are yielded \emph{eagerly}, and only once, rather
than duplicating the trace at every use site in |body|, as the by-name form
|body d| would.

To understand the recursive definition of the denotation of the right-hand side |d|
and its value |v|,
consider the case |τ = T|.
Then |return = Ret| and we get |d = rhs (Ret v)| for the value |v| at the end of
the trace |d|, as computed by the type class instance method |getValue :: T v ->
v|.
The effect of |Ret (getValue (unByValue d))| is that of stripping all |Step|s from |d|.

Let us trace $\Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i~i}$ for call-by-value:

< ghci> evalValue (read "let i = (λy.λx.x) i in i i") emp
$\perform{evalValue (read "let i = (λy.λx.x) i in i i") emp}$
\\[\belowdisplayskip]
\noindent
The beta reduction of $(\Lam{y}{\Lam{x}{x}})~i$ now happens once within the
$\LetOT$/$\LetIT$ bracket; the two subsequent $\LookupT$ events immediately halt
with a value.

However, care must be taken not to run the interpreter on a right-hand side that
accesses its value before producing one, as in the following example:

< ghci> takeT 5 (evalValue (read "let x = x in x x") emp)
$\LetOT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\LetIT\xhookrightarrow{\hspace{1.1ex}}\AppIT\xhookrightarrow{\hspace{1.1ex}}\LookupT(x)\xhookrightarrow{\hspace{1.1ex}}\texttt{\textasciicircum{}CInterrupted}$
\\[\belowdisplayskip]
\noindent
This loops forever unproductively.
Typically, strict languages work around this semantic singularity in either of
two ways:
They enforce termination of the recursive RHS statically (OCaml, ML), or they
use \emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
The next subsection explores an interpreter instance employing lazy
initialisation.

\begin{figure}
\begin{code}
evalVInit e ρ μ = unTVInit (eval e ρ :: DVInit) μ

ifPoly(data ValueVInit = ...)
type DVInit = TVInit ValueVInit; type HeapVInit = Addr :-> DVInit
newtype TVInit v = TVInit { unTVInit :: HeapVInit -> T (v, HeapVInit) }
ifPoly(instance Domain DVInit where
  ...
  bind # rhs body = do  μ <- getV
                        let a = nextFree μ
                        putV (ext μ a stuck)
                        step Let0 (memoV a (rhs (fetchV a))) >>= body . return)
\end{code}
%if style == newcode
\begin{code}
nextFreeV :: HeapVInit -> Addr
nextFreeV h = case Map.lookupMax h of
  Nothing     -> 0
  Just (k,_)  -> k+1

deriving via StateT HeapVInit T instance Functor TVInit
deriving via StateT HeapVInit T instance Applicative TVInit
deriving via StateT HeapVInit T instance Monad TVInit
data ValueVInit = StuckVInit | FunVInit (DVInit -> DVInit) | ConVInit Tag [DVInit]

getV :: TVInit HeapVInit
getV = TVInit (\ μ -> return (μ, μ))
putV :: HeapVInit -> TVInit ()
putV μ = TVInit (\ _ -> return ((), μ))

instance Trace (TVInit v) where step e m = TVInit (step e . unTVInit m)

fetchV :: Addr -> DVInit
fetchV a = getV >>= \μ -> μ ! a

memoV :: Addr -> DVInit -> DVInit
memoV a d = d >>= \v -> TVInit (upd v)
  where  upd StuckVInit  μ = return (StuckVInit, μ)
         upd v           μ = return (v, ext μ a (memoV a (return v)))

instance Domain DVInit where
  stuck = return StuckVInit
  fun _ _ f = return (FunVInit f)
  apply  d a = d >>= \v -> case v of
    FunVInit f -> f a; _ -> stuck
  con _ k ds = return (ConVInit k ds)
  select dv alts = dv >>= \v -> case v of
    ConVInit k ds | k ∈ dom alts  -> (alts ! k) ds
    _                             -> stuck
  bind # rhs body = do  μ <- getV
                        let a = nextFreeV μ
                        putV (ext μ a stuck)
                        step Let0 (memoV a (rhs (fetchV a))) >>= body . return
\end{code}
%endif
\\[-1em]
\caption{Call-by-value with lazy initialisation}
\label{fig:by-value-init}
\end{figure}

\subsection{Lazy Initialisation and Black-holing}
\label{sec:lazy-init}

Recall that our simple |DValue| domain above yields a potentially looping
interpreter.
Typical strict languages work around this issue in either of two ways:
They enforce termination of the RHS statically (OCaml, ML), or they use
\emph{lazy initialisation} techniques~\citep{Nakata:10,Nakata:06} (Scheme,
recursive modules in OCaml).
We recover a total interpreter using the semantics in \citet{Nakata:10},
building on the same encoding as |DNeed| and initialising the heap with a
\emph{black hole}~\citep{stg} |stuck| in |bind| as in \Cref{fig:by-value-init}.

< ghci> evalVInit (read "let x = x in x x") emp emp :: T (ValueVInit, HeapVInit)
$\perform{evalVInit (read "let x = x in x x") emp emp :: T (ValueVInit, HeapVInit)}$

\end{toappendix}

\medskip
This example suggests that |evalNeed2| agrees with the LK machine on
\emph{many} programs.
The next section proves that |evalNeed2| agrees with the LK machine on
\emph{all} programs, including ones that diverge.
