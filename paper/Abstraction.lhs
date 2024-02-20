%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE LambdaCase #-}

module Abstraction where

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
\end{code}
%endif

\section{Abstraction}
\label{sec:abstraction}

We will now recover a summary-based usage analysis as an instance of our
compositional definition of |eval|.
We demonstrate how our framework can be used both to \emph{instrument} the
dynamic semantics to describe \emph{operational properties} in terms of a
|Trace| instance, as well as \emph{statically approximate} these operational
properties by specifying a summary mechanism (\ie, a |Domain| instance) and
appealing to order theory\sven{Unclear how the first sentence fits to the second.}.
\Cref{sec:soundness} will understand the connection between instrumentation and
static analysis in terms of \emph{abstract interpretation}, where the
abstraction function |α| is completely determined by type class instances.
This enables further simplification of the usual soundness proof obligations |α
d ⊑ hat d|, because |α| can be inlined.
\sg{Is this too much anticipation? Other than that getting the instrumentation
for free is cool, the technical benefits are remarkable, but a bit inscrutible.}

\subsection{Usage Instrumentation}
\label{sec:instrumentation}

\begin{table}
\begin{tabular}{clll}
\toprule
\#  & |d|              & |eval e emp :: d| \\
\midrule
(1) & |D (ByName UT)|  & $\perform{eval (read "let id = λx.x in let t = (λy.y) id in let v = Z() in let u = v in t t") emp :: D (ByName UT)}$ \\
(2) & |D (ByValue UT)| & $\perform{eval (read "let id = λx.x in let t = (λy.y) id in let v = Z() in let u = v in t t") emp :: D (ByValue UT)}$ \\
(3) & |D (ByNeed UT)|  & $\perform{unByNeed (eval (read "let id = λx.x in let t = (λy.y) id in let v = Z() in let u = v in t t") emp) emp :: UT (Value (ByNeed UT), Heap _)}$ \\
\bottomrule
\end{tabular}
\caption{Comparing the usage instrumentation of different evaluation strategies on the expression \\
$e \triangleq \Let{id}{\Lam{x}{x}}{\Let{t}{(\Lam{y}{y})~id}{\Let{v}{Z()}{\Let{u}{v}{t~t}}}}$.}
\label{fig:usage-instrumentation-examples}
\end{table}

\begin{figure}
\begin{minipage}{0.4\textwidth}
\begin{code}
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
\end{code}
\end{minipage}%
\begin{minipage}{0.6\textwidth}
\begin{code}
data UT v = MkUT Uses v
instance Trace (UT v) where
  step (Lookup x)  (MkUT φ v)  = MkUT (ext emp x U1 + φ) v
  step _           τ           = τ
instance Monad UT where
  return a = MkUT emp a
  MkUT φ1 a >>= k = let MkUT φ2 b = k a in MkUT (φ1+φ2) b
\end{code}
%if style == newcode
\begin{code}
instance Extract UT where getValue (MkUT _ v) = v
\end{code}
%endif
\end{minipage}
\\[-1em]
\caption{|Trace| instance for usage analysis and |Monad| instance inducing usage instrumentation}
\label{fig:usg-abs}
\end{figure}

\sven{Add an introductory sentence that explains what this section is about and what problem it solves}
\sven{Add an example trace to this section and show how it is abstracted to usage information}

The gist of usage analysis is that it collects upper bounds for the number of
$\LookupT$ transitions per let-bound variable.
We refer to these upper bounds as \emph{usage cardinality} |U| in
\Cref{fig:usg-abs}, and a |Uses| collects the usage cardinality for each
let-bound variable.
The |U|sage |U0| means ``at most 0 times'', |U1| means ``at most 1 times'',
and |Uω| can be read as ``at most $ω$ times'', where $ω$ is the first limit
ordinal, greater than any natural number.
Usage analysis is a generalisation of absence analysis in \Cref{fig:absence}:
a variable is absent ($\aA$) when it has usage |U0|, otherwise it is used ($\aU$).

\sven{You need to explain what multiplication and addition on usages are used for. If you cannot motivate their usefulness in section 5.1, I would move their definition into the listing of section 5.2}
It is quite natural to define addition on and multiplication with |U|, expressed in
the type class |UVec|.%
\footnote{We think that |UVec| models |U|-modules. It is not a vector
space because |U| lacks inverses, but the intuition is close enough.}
For example, |U0 + u = u| and |U1 + U1 = Uω|, as well as |U0 * u = U0|,
|Uω * U1 = Uω|.
These operations lift to |Uses| pointwise, \eg,
$(|Uω| * [|x| ↦ |U1|]) + [|y| ↦ |U1|] = [|x| ↦ |Uω|, |y| ↦ |U1|]$.

\sven{Start the paragraph with a high-level goal: "To abstract the concrete trace to usage information, we define a custom trace instance ..."}
Compared to the concrete |T| from \Cref{sec:interp}, the |Trace| instance of
the custom trace type |UT| abstracts away all events other than |Lookup|s, and
smashes such lookups into a |Uses|.
The point of wrapping |Uses| in |UT| is to define a |Monad| instance that
aggregates |Uses| via |(+)|.

Astonishingly, the simple |Trace| and |Monad| definitions already induce an
\emph{instrumentation} of our semantics!
\Cref{fig:usage-instrumentation-examples}\sven{Table 1 appears 3 pages earlier. Would be good if it were closer to this section.}\sven{Shouldn't Table 1 contain |ω| instead of |Uω|?} lists the results of running
the instrumented interpreter on the same characteristic expression, but with
three different evaluation strategies |ByName|, |ByValue| and |ByNeed|.%
\footnote{For |ByValue|, we additionally need |instance Extract UT where extract (MkUT _ v) = v|.}
Thus, we finally reap the benefits of having defined |Domain| and |HasBind|
instances in \Cref{sec:interp} polymorphically over the inner trace |τ|.
As can be seen, the by-need strategy only evaluates what is needed.
The by-value strategy additionally uses the unused binding $v$ and the by-name
strategy evaluates $id$ multiple times since the thunk $t$ is evaluated multiple times \sven{You should lead over to the next section by saying that the traces may diverge and are not yet a computable analysis}.

\sven{Why is this important?}
Note that there is \emph{no difference} in instrumenting the interpreter at,
\eg, |D (ByName UT)| and \emph{running} the interpreter at |D (ByName T)|
to produce a finite trace and then replace every |Step :: Event -> T v -> T v|
with |step :: Event -> UT v -> UT v|.
This is the essence of the Galois connection in \Cref{sec:soundness}, which
takes care of |Value|s at the end of the trace as well.
Thus, the instrumentation encodes the most precise abstract representation of
the semantic trace property in question.

%The results of running the instrumentation yields surprising results on nested
%let-bindings:
%< ghci> eval (read "let i = let j = λx.x in j in i i") emp :: D (ByName UT)
%$\perform{eval (read "let i = let j = λx.x in j in i i") emp :: D (ByName UT)}$
%\\[\belowdisplayskip]
%\noindent
%Note that every \emph{activation} of $j$ is only evaluated once, but since there
%is one activation for each of the two lookups of $i$, and both actications were
%looked up once each, the result says that $j$ was looked up many times.
%It is clear that this is not useful, but fortunately the information on outer
%let-bindings such as $i$ is accurate enough to enable useful optimisations.

%\subsection{Operational properties and improvement}
%
%Instrumentation amounts to running the concrete semantics and then folding the
%trace into a |UT|.
%We will understand this instrumentation in a very formal sense as describing
%a safety property of traces in \Cref{sec:soundness}; it is the semantic property
%that the static analysis is supposed to approximate.
%
%The appeal of such a description is that \emph{trace properties are just folds
%over traces}, in contrast to the result of a static analysis approximating
%the property, which is often defined by least fixpoints.
%For example, we can define usage cardinality (``|e| evaluates |x| at most |u|
%times'') as
%\[
%  |forall e1. case eval (Let x e1 e) emp :: D (ByName UT) of ByName (MkUT φ _) -> (φ ! x) ⊑ u|.
%\]
%Since there is no difference (\cf \Cref{sec:adequacy}) between running
%|eval (Let x e1 e) emp| and generating the resulting trace from the small-step
%semantics in \Cref{fig:lk-semantics}, we can use this definition
%to show an observational improvement statement $\forall \pe_1,\pe_2.\
%\Let{x}{\pe_1}{e} \impequiv \Let{x}{\pe_2}{e}$ \citep{MoranSands:99} whenever
%|u| is absent (|U0|), \ie, evaluating $\Let{x}{\pe_1}{e}$ takes the same
%number of steps no matter what $\pe_1$ is or in which syntactic context we put
%the whole expression.%
%\footnote{Similarly, we could prove that update avoidance~\citep{Gustavsson:98}
%is improving when |u ⊑ U1|, but that would take an even more elaborate setup.}

\subsection{Usage analysis}
\label{sec:usage-analysis}

\begin{figure}
\begin{spec}
class Eq a => Lat a where bottom :: a; (⊔) :: a -> a -> a;
kleeneFix :: Lat a => (a -> a) -> a; qquad lub :: Lat a => [a] -> a
kleeneFix f = go bottom where go x = let x' = f x in if x' ⊑ x then x' else go x'
\end{spec}
\\[-1em]
\caption{Order theory and Kleene iteration}
\label{fig:lat}
\end{figure}

\begin{figure}
\begin{minipage}{0.43\textwidth}
\begin{code}
data UValue = UCons U UValue | Rep U
type UD = UT UValue

instance Lat U where {-" ... \iffalse "-}
  bottom = U0
  U0  ⊔  u   = u
  u   ⊔  U0  = u
  U1  ⊔  U1  = U1
  _   ⊔  _   = Uω
{-" \fi "-}
ifPoly (instance Lat Uses where ...)
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
\end{code}
\end{minipage}%
\begin{minipage}{0.57\textwidth}
\begin{code}
instance Domain UD where
  stuck                                  = bottom
  fun x {-" \iffalse "-}_{-" \fi "-} f   = case f (MkUT (ext emp x U1) (Rep Uω)) of
    MkUT φ v -> MkUT (Uω * ext φ x U0) (UCons (φ !? x) v)
  apply (MkUT φ1 v1) (MkUT φ2 _)         = case peel v1 of
    (u, v2) -> MkUT (φ1 + u*φ2) v2
  con {-" \iffalse "-}_{-" \fi "-} _ ds  = foldl apply (MkUT emp (Rep Uω)) ds
  select d fs                            =
    d >> lub  [  f (replicate (conArity k) (MkUT emp (Rep Uω)))
              |  (k,f) <- assocs fs ]

instance HasBind UD where
  bind rhs body = body (kleeneFix rhs)
\end{code}
\end{minipage}
%if style == newcode
\begin{code}
deriving instance Eq U
deriving instance Eq a => Eq (UT a)
deriving instance Functor UT

instance Eq UValue where
  Rep u1 == Rep u2 = u1 == u2
  v1     == v2     = peel v1 == peel v2

instance Show U where
  show U0 = "0"
  show U1 = "1"
  show Uω = "ω"

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
\end{code}
%endif
\caption{Summary-based usage analysis via |Domain| and |HasBind|}
\label{fig:abs-usg}
\end{figure}


\sven{Add an introductory sentence that explains what this section is about and what problem it solves}

Of course, running the instrumented interpreter will diverge whenever the object
program diverges.
If we want to assess usage cardinality statically, we have to find a more
abstract, finite representation of |Value|.%
\footnote{In particular, the negative recursive occurrence in
|Fun :: (τ (highlight Value τ) -> ...) -> Value τ| is disqualifying.}
We address finiteness by defining |UValue| in \Cref{fig:abs-usg} as a copy
of $\Summary$ in \Cref{fig:absence} that lists argument usage |U| instead of
$\Absence$ flags.
Absence types in \Cref{fig:absence} are now called |UD| and constitute
the abstract semantic domain for which we will define |Domain| and |HasBind|
instances.

The analysis is just a slight generalisation of absence analysis \sven{This is downplaying our contribution. I would phrase it as: "The usage analysis is a generalization of the absence analysis in the following ways ..."}.
However, it is formulated as an abstract denotational interpreter, which is
a bit different than absence analysis.
Hence we will start with some examples building on the existing intuition to see
what usage analysis infers before discussing its implementation.
Example (1) of \Cref{fig:usage-analysis-examples} shows that the analysis infers
the same result as the by-name instrumentation on the example from
\Cref{fig:usage-instrumentation-examples}.
Examples (2) and (3) illustrate that usage analysis can precisely infer
second-order |U1| usage on $j$ through the summary mechanism encoded in |apply|
and |fun|, however examples (4) and (5) show that precision declines when there
is another indirect call involved.

As for the implementation: since any |d::UD| is finite, we can no longer use
guarded |fix|points in |HasBind UD| to compute recursive let bindings, so we
will use least fixpoints (computed by |kleeneFix| in \Cref{fig:lat}) instead.%
\footnote{Why is the use of least fixpoints correct?
The fact that we are approximating a safety property~\citep{Lamport:77}
is important. We will discuss this topic in \Cref{sec:safety-extension}.}
The resulting definition of |HasBind| is safe for by-name and by-need semantics.

|kleeneFix| requires us to define an order on |UD|, which is induced
by |U0 ⊏ U1 ⊏ Uω| in the same way that the order
on $\AbsTy$ in \Cref{sec:absence} was induced from the order $\aA ⊏ \aU$
on $\Absence$ flags.
Function |peel| exemplifies the non-syntactic equality |(Rep u) ==
UCons u (Rep u)| at work that is respected by the |Lat UD| instance.%
\footnote{The keen reader may note that the least fixed-point does not
always exist due to infinite ascending chains such as
|UCons U1 (UCons U1 (... Rep U0))|.
This can be easily worked around with appropriate widening measures.
A very simple one is to turn |Rep U0| into |Rep Uω| when the |UValue|
exceeds a certain constant depth.
We simply assume that such a procedure is in effect and hence that all fixpoints
exist.}
The |Domain| instance is responsible for implementing the summary mechanism.
While |stuck| expressions do not evaluate anything and hence are denoted by
|bottom = MkUT emp (Rep U0)|, the |fun| and |apply| functions play exactly the same
roles as $\mathit{fun}_\px$ and $\mathit{app}$ in \Cref{fig:absence}.

Consider again example (3) from \Cref{fig:usage-analysis-examples}.
The summary for the right-hand side $\Lam{x}{x}$ of $i$ is computed as follows
\begin{spec}
   eval (Lam x (Var x)) ρ
=  fun x (\d -> step App2 (eval (Var x) (ext ρ x d)))
=  case step App2 (eval (Var x) (ext ρ x (MkUT (ext emp x U1) (Rep Uω)))) of
     MkUT φ v -> MkUT (Uω * ext φ x U0) (UCons (φ !? x) (Rep Uω))
=  MkUT emp (UCons U1 (Rep Uω))
\end{spec}

That is, the lambda body is applied to a proxy |(MkUT (ext emp x U1) (Rep Uω))|
to summarise how the body uses its argument by way of looking at how it uses |x|,
and returns this usage by prepending it to the summarised value.%
\footnote{As before, the exact identity of |x| is exchangeable; we use it as a
De Bruijn level.}
Occurrences of |x| must make do with the top value |(Rep Uω)| for lack of
knowing the actual argument at call sites, and free-variable uses in the lambda
body are multiplied with |Uω| to anticipate the effect of multiple calls.

The definition of |apply| to concretise such summaries is nearly the same as in
\Cref{fig:absence}, except for the use of |+| instead of $⊔$ to carry over |U1
+ U1 = Uω|, and an explicit |peel| to view a |UValue| in terms of $\sumcons$.
The usage |u| thus pelt from the value determines how often the actual
argument was evaluated, and multiplying the uses of the argument |φ2| with |u|
accounts for that.

Examples (6) and (7) in \Cref{fig:usage-analysis-examples} concern data
constructors and demonstrate the blatant imprecision of the analysis when faced
with manifest beta redexes.
That is because in contrast to \citet{Sergey:14}, we omit a more elaborate
summary mechanism for data constructors for simplicity, and thus assume that any
field of a data constructor is used multiple times.
This is achieved in |con| by repeatedly |apply|ing to the top value |(Rep Uω)|,
as if a data constructor was a lambda-bound variable.
Dually, |select| does not need to track how fields are used and can pass |MkUT
emp (Rep Uω)| as proxies for field denotations.
The result uses anything the scrutinee expression used, plus the upper bound of
uses in case alternatives, one of which will be taken.

\begin{table}
\begin{tabular}{clll}
\toprule
\# & |d|             & |e|                                               & |eval e emp :: d| \\
\midrule
(1) & |UD|            & $\pe$ from \Cref{fig:usage-instrumentation-examples} & $\perform{eval (read "let id = λx.x in let t = (λy.y) id in let v = Z() in let u = v in t t") emp :: UD}$ \\
(2) & |D (ByName UT)| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp :: D (ByName UT)}$ \\
(3) & |UD|            & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i j") emp :: UD}$ \\
(4) & |D (ByName UT)| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i i j") emp :: D (ByName UT)}$ \\
(5) & |UD|            & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~i~j}}$   & $\perform{eval (read "let i = λx.x in let j = λy.y in i i j") emp :: UD}$ \\
(6) & |D (ByName UT)| & $\Let{z}{Z()}{\Case{S(z)}{S(n) → n}}$   & $\perform{eval (read "let z = Z() in case S(z) of { S(n) -> n }") emp  :: D (ByName UT)}$ \\
(7) & |UD|            & $\Let{z}{Z()}{\Case{S(z)}{S(n) → n}}$   & $\perform{eval (read "let z = Z() in case S(z) of { S(n) -> n }") emp :: UD}$ \\
%(8) & |D (ByName UT)| & $\Let{i}{\Let{j}{\Lam{x}{x}}{j}}{i~i}$   & $\perform{eval (read "let i = let j = λx.x in j in i i") emp :: UD}$ \\
\bottomrule
\end{tabular}
\caption{Comparing usage analysis |UD| to the usage instrumentation |D (ByName UT)|.}
\label{fig:usage-analysis-examples}
\end{table}

We have proven usage analysis correct by relating it to the instrumentation
roughly as follows:%
\footnote{Do note that the range types of |ρ| are incompatible; we fix this in
\Cref{thm:usage-correct}.}
\[
  |(eval e ρ :: D (ByName UT))^.φ ⊑ (eval e ρ :: UD)^.φ|,
\]
where we abbreviate the field access |(MkUT φ' v)^.φ := φ'|.
In other words: for an evaluation to weak-head normal form, our analysis never
underapproximates the |Uses| reported by the instrumentation.
For the proof, we need to prove correct the summary mechanism implied by
|apply| and |fun| in the following substitution lemma:

\begin{toappendix}
As in the proof for \Cref{thm:absence-subst}, we will use the following abbreviations:

\begin{abbreviation}
  We abbreviate |(MkUT φ' v)^.φ := φ'|.
\end{abbreviation}

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst-usage}
  We call |abssubst φ x φ' := (Uω * ext φ x U0) + (φ ! x) * φ'| the
  \emph{abstract substitution} operation on |Uses|
  and overload this notation for |UT|, so that
  |abssubst (MkUT φ v) x φ' := MkUT (ext φ x φ') v|.
\end{definition}

\begin{lemma}
  \label{thm:abs-syn-subst-usage}
  |eval (App (Lam x e) y) ρ = abssubst (eval e (ext ρ x (MkUT (ext emp x U1) (Rep Uω)))) x ((ρ ! y) ^. φ)|.
\end{lemma}
\begin{proof}
Follows by unfolding the application and lamda case and then refolding abstract substitution.
\end{proof}


\begin{lemma}
\label{thm:lambda-bound-absent-usage}
Lambda-bound uses do not escape their scope. That is, when $\px$ is lambda-bound in $\pe$, it is
\[
  (\semabs{\pe}_ρ).φ(\px) = \aA.
\]
\end{lemma}
\begin{proof}
By induction on $\pe$. In the lambda case, any use of $\px$ is cleared to $\aA$
when returning.
\end{proof}

\begin{lemma}
\label{thm:lambda-commutes-usage}
$\semabs{(\Lam{\px}{\Lam{\py}{\pe}})~\pz}_ρ = \semabs{\Lam{\py}{((\Lam{\px}{\pe})~\pz)}}_ρ$.
\end{lemma}
\begin{proof}
\begin{DispWithArrows*}[fleqn,mathindent=0em]
      & \semabs{(\Lam{\px}{\Lam{\py}{\pe}})~\pz}_ρ
      \Arrow{Unfold $\semabs{\wild}$, \Cref{thm:abs-syn-subst}} \\
  ={} & (\mathit{fun}_\py(\fn{θ_\py}{\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \aU.. \rangle,\py↦θ_\py]}}))[\px \Mapsto ρ(\pz).φ]
      \Arrow{$ρ(\pz)(\py) = \aA$ by \Cref{thm:lambda-bound-absent}, $\px \not= \py \not= \pz$} \\
  ={} & \mathit{fun}_\py(\fn{θ_\py}{(\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \aU.. \rangle,\py↦θ_\py]})[\px \Mapsto ρ(\pz).φ]})
      \Arrow{Refold $\semabs{\wild}$} \\
  ={} & \semabs{\Lam{\py}{((\Lam{\px}{\pe})~\pz)}}_ρ
\end{DispWithArrows*}
\end{proof}

\begin{lemma}
\label{thm:push-app-usage}
$\semabs{(\Lam{\px}{\pe})~\py~\pz}_ρ = \semabs{(\Lam{\px}{\pe~\pz})~\py}_ρ$.
\end{lemma}
\begin{proof}
\begin{DispWithArrows*}[fleqn,mathindent=0em]
      & \semabs{(\Lam{\px}{\pe})~\py~\pz}_ρ
      \Arrow{Unfold $\semabs{\wild}$, \Cref{thm:abs-syn-subst}} \\
  ={} & \mathit{app}((\semabs{\pe}_{ρ[\langle [\px↦\aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ])(ρ(\pz))
      \Arrow{$ρ(\pz)(\px) = \aA$ by \Cref{thm:lambda-bound-absent}, $\py \not= \px \not= \pz$} \\
  ={} & \mathit{app}(\semabs{\pe}_{ρ[\langle [\px↦\aU], \aU.. \rangle]})(ρ(\pz))[\px \Mapsto ρ(\py).φ]
      \Arrow{Refold $\semabs{\wild}$} \\
  ={} & \semabs{(\Lam{\px}{\pe~\pz})~\py}_ρ
\end{DispWithArrows*}
\end{proof}

\begin{lemma}
\label{thm:push-let-usage}
$\semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ = \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ$.
\end{lemma}
\begin{proof}
The key of this lemma is that it is equivalent to postpone the abstract
substitution from the let RHS $\pe_1$ to the let body $\pe_2$.
This can easily be proved by induction on $\pe_2$, which we omit here, but
indicate the respective step below as ``handwaving''.
Note that we assume the (more general) recursive let semantics as defined at the
begin of this Section.

\begin{DispWithArrows*}[fleqn,mathindent=1em]
      & \semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ
      \Arrow{Unfold $\semabs{\wild}$} \\
  ={} & \semabs{(\Lam{\px}{\pe_2})~\py}_{ρ[\pz↦\lfp(\fn{θ}{\pz \both \semabs{(\Lam{\px}{\pe_1})~\py}_{ρ[\pz ↦ θ]}})]}
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle,\pz↦\lfp(\fn{θ}{\pz \both (\semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle, \pz ↦ θ]})[\px \Mapsto ρ(\py).φ]})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Handwaving above} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle,\pz↦\lfp(\fn{θ}{\pz \both \semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle, \pz ↦ θ]}})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Refold $\semabs{\wild}$} \\
  ={} & (\semabs{\Let{\pz}{\pe_1}{\pe_2}}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ
\end{DispWithArrows*}
\end{proof}
\end{toappendix}

\begin{lemmarep}[Substitution]
\label{thm:usage-subst}
|eval e (ext ρ x (ρ ! y)) ⊑ eval (Lam x e `App` y) ρ|.
\end{lemmarep}
\begin{proof}
We need the following additional freshness assumptions (in that they all relate
to the identity of |x|) that in practice are respected by |eval|:
\begin{itemize}
  \item |x| is absent in |ρ|, otherwise we cannot use |ext emp x U1| as a proxy
    to see how often the binding for |x| was used.
  \item |x| is absent in |d|, otherwise the fixpoint identity (6) below does not hold
\end{itemize}

Furthermore, the statement is too weak as an inductive hypothesis, because the
equivalent of \Cref{thm:lambda-commutes-absence} does not hold.
Witness the following counter-examples, illustrating the lack of an
approximation relationship:
\begin{spec}
    eval (Lam x (Lam y (Var x)) `App` z) ρ
=   MkUT (Uω * ((ρ ! z)^.φ)) (UCons U0 (Rep Uω))
⊐   MkUT ((ρ ! z)^.φ) (UCons U0 (Rep Uω))
=   eval (Lam y (Lam x (Var x) `App` z)) ρ
\end{spec}
\begin{spec}
    eval (Lam x (Lam y (Var y)) `App` z) ρ
=   MkUT emp (UCons U1 (Rep Uω))
⊏   MkUT emp (UCons Uω (Rep Uω))
=   eval (Lam y (Lam x (Var y) `App` z)) ρ
\end{spec}
This would cause trouble in the the lambda case, where we need this equality.

The fix is simple: We prove the substitution lemma for a slightly different
domain, |UD2|, where |fun| is defined as
\begin{spec}
  fun x f = case f (MkUT (ext emp x U1) (Rep Uω)) of
    MkUT φ v -> MkUT (ext φ x U0) (UCons (φ !? x) v)
    MkUT φ v -> MkUT (Uω * ext φ x U0) (UCons (φ !? x) v)
\end{spec}
We gave the original definition in |UD| in the second, dead alternative.
Note the omission of multiplication with |Uω|.
With this definition of |fun|, the above equalities hold.
Why not define |fun| on |UD| like this in the first place?
Because then the results of usage analysis would be invalidated by wrapping
arbitrary evaluation contexts around the expression, rendering the results useless
for program transformation.

Clearly if we can show the substitution lemma for |UD2|, we can show it
for |UD| as well by monotonicity.

The proof below needs to appeal to a couple of commutation lemmas, the proofs of
which would be tedious and hard to follow, hence they are omitted.
Many of these are similar to lemmas we have proven for absence analysis
(\cf \Cref{thm:lambda-commutes-absence}).
All of these apply at |UD2| only.
\begin{lemma}
\label{thm:lambda-commutes-usage}
|eval (Lam x (Lam y e) `App` z) ρ = eval (Lam y ((Lam x e) `App` z)) ρ|.
\end{lemma}
\begin{lemma}
\label{thm:push-app-usage}
|eval (Lam x e `App` y `App` z) ρ = eval (Lam x (e `App` z) `App` y) ρ|.
\end{lemma}
\begin{lemma}
\label{thm:push-select-usage}
|eval (Lam x e `App` y `App` z) ρ = eval (Lam x (e `App` z) `App` y) ρ|.
\end{lemma}
\begin{lemma}
\label{thm:push-let-usage}
|eval (Let z (Lam x e1 `App` y) (Lam x e2 `App` y)) ρ = eval (Lam x (Let z e1 e2) `App` y) ρ|.
\end{lemma}

\sg{I got until here, but then prioritised the pass over Section 5 to make Sven productive.
Will pick up here soon. At any rate, the proof is not wrong but caught in the middle of a refactorign.}

Here is an exhaustive list of them, to isolate handwaving:
\begin{enumerate}
  \item %If |x| is absent in |f (prx x)|, then |f (prx x) = abssubst (f (prx x)) x d|.
  \item |eval (Lam x (Lam y e) `App` z) ρ = eval (Lam y ((Lam x e) `App` z)) ρ|. \Cref{thm:lambda-commutes-absence}.
  \item Similarly for |select|.
  \item |eval (Lam x e `App` y `App` z) ρ = eval (Lam x (e `App` z) `App` y) ρ|. \Cref{thm:push-app-absence}
  \item Similarly for |con|.
  \item \begin{spec}
                       kleeneFix (\d1 -> abssubst (  eval e (ext (ext ρ y (step (Lookup x) d1)) x (prx x))) x φ)
        =  abssubst (  kleeneFix (\d1 ->             eval e (ext (ext ρ y (step (Lookup x) d1)) x (prx x)))) x φ
        \end{spec}
  \item \mbox{If |x| abs in |d| and |ρ|, then |abssubst (eval e (ext (ext ρ x (prx x)) y (abssubst d1 x d))) x d = abssubst (eval e (ext (ext ρ x (prx x)) y d1)) x d|.}
\end{enumerate}
We proceed by induction on |e|.
\begin{itemize}
  \item \textbf{Case }|Var z|:
    When |x //= z|, we have
    \begin{spec}
        eval z (ext ρ x (ρ ! y))
    =   {- |x //= z| -}
        ρ ! z
    =   {- Refold |eval| -}
        eval z (ext ρ x (prx x))
    =   {- |((ρ ! z)^.φ) ! x = U0| -}
        abssubst (eval z (ext ρ x (prx x))) x ((ρ ! y)^.φ)
    =   {- \Cref{thm:abs-syn-subst-usage} -}
        eval (Lam x z `App` y) ρ
    \end{spec}
    Otherwise, we have |x = z|.
    \begin{spec}
        eval z (ext ρ x (ρ ! y))
    =   {- |x = y|, unfold -}
        ρ ! y
    ⊑   {- |v ⊑ (Rep Uω)| -}
        MkUT ((ρ ! y)^.φ) (Rep Uω)
    =   {- Definition of abstract substitution -}
        abssubst (prx x) x ((ρ ! y)^.φ)
    =   {- Refold |eval| -}
        abssubst (eval z (ext ρ x (prx x))) x ((ρ ! y)^.φ)
    =   {- \Cref{thm:abs-syn-subst-usage} -}
        eval (Lam x z `App` y) ρ
    \end{spec}

  \item \textbf{Case} |Lam z e|:
    \begin{spec}
        eval (Lam z e) (ext ρ x (ρ ! y))
    =   {- Unfold |eval| -}
        fun z (\d -> step App2 $ eval e (ext (ext ρ x (ρ ! y)) z d))
    =   {- Rearrange, $|x| \not= |z|$ -}
        fun z (\d -> step App2 $ eval e (ext (ext ρ z d) x (ρ ! y)))
    ⊑   {- Induction hypothesis, $|x| \not= |z|$ -}
        fun z (\d -> step App2 $ eval (Lam x e `App` y) (ext ρ z d))
    =   {- Refold |eval| -}
        eval (Lam z (Lam x e `App` y)) ρ
    =   {- $|x| \not= |z|$, \Cref{thm:lambda-commutes-usage} -}
        eval (Lam x (Lam z e) `App` y) ρ
    \end{spec}

  \item \textbf{Case} |App e z|:
    \begin{spec}
        eval (App e z) (ext ρ x d)
    =   {- Unfold |eval| -}
        apply (eval e (ext ρ x d)) ((ext ρ x d) ! z)
    ⊑   {- Induction hypothesis -}
        apply (abssubst (eval e (ext ρ x (prx x))) x d) ((ext ρ x d) ! z)
    ⊑   {- |Var| case (might also incur actual |⊏|) -}
        apply (abssubst (eval e (ext ρ x (prx x))) x d) (abssubst ((ext ρ x (prx x)) ! z) x d)
    =   {- \Cref{thm:push-app-usage} -}
        abssubst (apply (eval e (ext ρ x (prx x))) ((ext ρ x (prx x)) ! z)) x d
    =   {- Refold |eval| -}
        abssubst (eval (App e z) (ext ρ x (prx x))) x d
    \end{spec}

  \item \textbf{Case} |Con|, |Case|:
    Similar, needs identities (3) and (5).

  \item \textbf{Case} |Let|:
    \begin{spec}
        eval (Let z e1 e2) (ext ρ x d)
    =   {- Unfold |eval|, |HasBind|, |Trace| -}
        eval e2 (ext (ext ρ x d) z (step (Lookup z) (kleeneFix (\d1 -> eval e1 (ext (ext ρ x d) z (step (Lookup z) d1))))))
    ⊑   {- Induction hypothesis, twice. NB: |x| is absent in |d|, hence in |d1| -}
        abssubst (eval e2 (ext (ext ρ x (prx x)) z (step (Lookup z) (kleeneFix (\d1 -> abssubst (eval e1 (ext (ext ρ x (prx x)) z (step (Lookup z) d1))) x d))))) x d
    =   {- Identity (6) -}
        abssubst (eval e2 (ext (ext ρ x (prx x)) z (step (Lookup z) (abssubst (kleeneFix (\d1 -> eval e1 (ext (ext ρ x (prx x)) z (step (Lookup z) d1)))) x d)))) x d
    =   {- Identity (7) -}
        abssubst (eval e2 (ext (ext ρ x (prx x)) z (step (Lookup z) (kleeneFix (\d1 -> eval e1 (ext (ext ρ x (prx x)) z (step (Lookup z) d1))))))) x d
    =   {- Refold |eval| -}
        abssubst (eval (Let z e1 e2) (ext ρ x (prx x))) x d
    \end{spec}
\end{itemize}
\end{proof}

If usage analysis is to be used to inform, \eg, dead code removal in a compiler,
then the results it infers better generalise to arbitrary program contexts
in which the analysed expression |e| occurs.
Thus, it is useful to know the results are invariant under wrapping of
\emph{evaluation contexts} as in \Cref{defn:absence} of Absence.
A precise syntactic definition of by-need evaluation contexts such as in
\citet{MoranSands:99} can be found as part of the proof in the Appendix.

\begin{theoremrep}
  Let |ectx| be an arbitrary by-need evaluation context, where |fillC ectx e|
  fills the hole in |ectx| with |e|.
  Then |((eval e ρ :: UD)^.φ !? x) = ((eval (fillC ectx e) ρ :: UD)^.φ) !? x| for
  every free variable |x| of |e| that does not occur in |ectx|.
\end{theoremrep}
\begin{proof}
  TODO
\end{proof}


%Example (8) shows that the static analysis reports the same surprising
%multi-usage result of the nested let-binder $j$ as the instrumentation.
%As well it should, since that is inherent to the trace property it is
%approximating!
%Of course, a practical implementation would write out annotations in |bind|,
%when it leaves the lexical scope of the let-binding, rather than rerunning
%the analysis for every let-binding in the program separately.
%We have done so as an experiment in the Supplement \sg{as well as the case study
%modifying GHC}, but it complicates the simple correctness relationship the analysis
%enjoys \wrt the instrumentation in \Cref{thm:usage-correct}, so we leave it out
%in this work.

\subsection{Discussion}
%A total description of the \emph{dynamic semantics} of a language requires a
%coinductive domain.
%For \emph{static analysis} we need to find good abstractions that approximate
%the dynamics in an inductive domain.
%The culprit is the use of concrete |Value|s in |D|: its |Fun| constructor is
%decidedly not inductive because it recurses in negative position.

By recovering usage analysis as an abstraction of |eval|, we have achieved an
important goal:
to derive a \emph{compositional} static analysis approximating a property
of a \emph{small-step trace}, with a simple but useful summary mechanism, as
an instance of a generic denotational interpreter, thus sharing most of
its structure with the concrete semantics.
We will see in \Cref{sec:soundness} that this sharing leads to significant
reuse in soundness proofs.

To demonstrate the versatility of our approach, we have also defined
a compositional type analysis with let generalisation as well as
0CFA as an instance of our generic denotational interpreter; you can find
outlines in the Appendix and the complete implementations in the supplied
extract of this document.

\begin{toappendix}
\subsection{Type Analysis}

\begin{figure}
\begin{code}
data Type = Type :->: Type | TyConApp TyCon [Type] | TyVar Name | Wrong
data PolyType = PT [Name] Type; data TyCon = {-" ... \iffalse "-} BoolTyCon | NatTyCon | OptionTyCon | PairTyCon {-" \fi "-}

type Constraint = (Type, Type); type Subst = Name :-> Type
data Cts a = Cts (StateT (Set Name,Subst) Maybe a)
emitCt :: Constraint -> Cts ();                   freshTyVar :: Cts Type
instantiatePolyTy :: PolyType -> Cts Type; ^^ ^^  generaliseTy :: Cts Type -> Cts PolyType
closedType :: Cts PolyType -> PolyType {-" \iffalse "-}
closedType d = runCts (generaliseTy $ d >>= instantiatePolyTy)
{-" \fi "-}

instance Trace (Cts v) where step _ = id
instance Domain (Cts PolyType) where stuck = return (PT [] Wrong); {-" ... \iffalse "-}
                                     fun _ {-" \iffalse "-}_{-" \fi "-} f = do
                                       arg <- freshTyVar
                                       res <- f (return (PT [] arg)) >>= instantiatePolyTy
                                       return (PT [] (arg :->: res))
                                     con {-" \iffalse "-}_{-" \fi "-} k ds = do
                                       con_app_ty <- instantiateCon k
                                       arg_tys <- traverse (>>= instantiatePolyTy) ds
                                       res_ty <- freshTyVar
                                       emitCt (con_app_ty, foldr (:->:) res_ty arg_tys)
                                       return (PT [] res_ty)
                                     apply dv da = do
                                       fun_ty <- dv >>= instantiatePolyTy
                                       arg_ty <- da >>= instantiatePolyTy
                                       res_ty <- freshTyVar
                                       emitCt (fun_ty, arg_ty :->: res_ty)
                                       return (PT [] res_ty)
                                     select dv fs = case Map.assocs fs of
                                       []            -> stuck
                                       fs@((k,_):_)  -> do
                                         con_ty <- dv >>= instantiatePolyTy
                                         res_ty <- snd . splitFunTys <$> instantiateCon k
                                         let TyConApp tc tc_args = res_ty
                                         emitCt (con_ty, res_ty)
                                         ks_tys <- enumerateCons tc tc_args
                                         tys <- forM ks_tys $ \(k,tys) ->
                                           case List.find (\(k',_) -> k' == k) fs of
                                             Just (_,f) -> f (map (fmap (PT [])) tys)
                                             _          -> stuck
                                         traverse instantiatePolyTy tys >>= \case
                                           []      -> stuck
                                           ty:tys' -> traverse (\ty' -> emitCt (ty,ty')) tys' >> return (PT [] ty)

{-" \fi "-}
instance HasBind (Cts PolyType) where
  bind rhs body = generaliseTy (do
    rhs_ty <- freshTyVar
    rhs_ty' <- rhs (return (PT [] rhs_ty)) >>= instantiatePolyTy
    emitCt (rhs_ty, rhs_ty')
    return rhs_ty) >>= body . return

\end{code}
%if style == newcode
\begin{code}
deriving instance Eq TyCon
deriving instance Enum TyCon
deriving instance Bounded TyCon
deriving instance Eq Type
deriving instance Functor Cts

runCts :: Cts PolyType -> PolyType
runCts (Cts m) = case evalStateT m (Set.empty, emp) of Just ty -> ty; Nothing -> PT [] Wrong

instance Applicative Cts where
  pure = Cts . pure
  (<*>) = ap

instance Monad Cts where
  Cts m >>= k = Cts (m >>= unCts . k)

instance Show TyCon where
  show BoolTyCon = "\\texttt{bool}"
  show NatTyCon = "\\texttt{nat}"
  show OptionTyCon = "\\texttt{option}"
  show PairTyCon = "\\times"

instance Show Type where
  showsPrec _ (TyConApp k tys) = showsPrec 0 k . foldr (\t s -> showString "\\;" . showsPrec 1 t . s) id tys
  showsPrec _ (TyVar x)  = showString x
  showsPrec _ Wrong      = showString "\\textbf{wrong}"
  showsPrec p (l :->: r) =
    showParen (p > 0) $ showsPrec 1 l . showString " \\rightarrow " . showsPrec 0 r

instance Show PolyType where
  showsPrec _ (PT [] body) = shows body
  showsPrec _ (PT alphas body) = showString "\\forall" . showSep (showString ",") (map showString alphas) . showString ".\\ " . shows body

freeVars :: Type -> Set Name
freeVars (TyVar x) = Set.singleton x
freeVars (a :->: r) = freeVars a `Set.union` freeVars r
freeVars (TyConApp _ as) = Set.unions (map freeVars as)
freeVars Wrong = Set.empty

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = go [] ty
  where
    go as (a :->: r) = go (a:as) r
    go as ty = (reverse as, ty)

conTy :: Tag -> PolyType
conTy TT = PT [] (TyConApp BoolTyCon [])
conTy FF = PT [] (TyConApp BoolTyCon [])
conTy Z = PT [] (TyConApp NatTyCon [])
conTy S = PT [] (TyConApp NatTyCon [] :->: TyConApp NatTyCon [])
conTy None = PT ["a_none"] (TyConApp OptionTyCon [TyVar "a_none"])
conTy Some = PT ["a_some"] (TyVar "a_some" :->: TyConApp OptionTyCon [TyVar "a_some"])
conTy Pair = PT ["a_pair", "b_pair"]
  (TyVar "a_pair" :->: TyVar "b_pair" :->: TyConApp PairTyCon [TyVar "a_pair", TyVar "b_pair"])

tyConTags :: TyCon -> [Tag]
tyConTags tc =
  [ k | k <- [minBound..maxBound]
      , let PT _ ty = conTy k
      , TyConApp tc' _ <- [snd (splitFunTys ty)]
      , tc == tc' ]

applySubst :: Subst -> Type -> Type
applySubst subst ty@(TyVar y)
  | Just ty <- Map.lookup y subst = ty
  | otherwise                   = ty
applySubst subst (a :->: r) =
  applySubst subst a :->: applySubst subst r
applySubst subst (TyConApp k tys) =
  TyConApp k (map (applySubst subst) tys)
applySubst _ ty = ty

unCts :: Cts a -> StateT (Set Name,Subst) Maybe a
unCts (Cts m) = m

addCt (l,r) subst = case (applySubst subst l, applySubst subst r) of
  (l, r) | l == r -> Just subst
  (TyVar x, ty)
    | not (occurs x ty)
    -> Just (Map.insert x ty subst)
  (_, TyVar _) -> addCt (r,l) subst
  (a1 :->: r1, a2 :->: r2) -> addCt (a1,a2) subst >>= addCt (r1,r2)
  (Wrong, Wrong) -> Just subst
  (TyConApp k1 tys1, TyConApp k2 tys2) | k1 == k2 -> foldrM addCt subst (zip tys1 tys2)
  _ -> Nothing
  where
    occurs x ty = applySubst (ext emp x ty) ty /= ty -- quick and dirty

emitCt ct = Cts $ StateT $ \(names,subst) -> case addCt ct subst of
  Just subst' -> Just ((), (names, subst'))
  Nothing     -> Nothing

freshTyVar = Cts $ state $ \(ns,subst) ->
  let n = "\\alpha_{" ++ show (Set.size ns) ++ "}"
  in (TyVar n,(Set.insert n ns,subst))

freshenVars :: [Name] -> Cts Subst
freshenVars alphas = foldM one emp alphas
  where
    one subst alpha = do
      beta <- freshTyVar
      pure (ext subst alpha beta)

instantiatePolyTy (PT alphas ty) = do
  subst <- freshenVars alphas
  return (applySubst subst ty)

instantiateCon :: Tag -> Cts Type
instantiateCon k = instantiatePolyTy (conTy k)

enumerateCons :: TyCon -> [Type] -> Cts [(Tag,[Cts Type])]
enumerateCons tc tc_arg_tys = forM (tyConTags tc) $ \k -> do
  ty <- instantiateCon k
  let (field_tys,res_ty) = splitFunTys ty
  emitCt (TyConApp tc tc_arg_tys, res_ty)
  return (k, map pure field_tys)

generaliseTy (Cts m) = Cts $ do
  (outer_names,_) <- get
  ty <- m
  (_names',subst) <- get
  let ty' = applySubst subst ty
  let one n = freeVars $ applySubst subst (TyVar n)
  let fvΓ = Set.unions (Set.map one outer_names)
  let alphas = freeVars ty' `Set.difference` fvΓ
  return (PT (Set.toList alphas) ty')
\end{code}
%endif
\caption{Hindley-Milner-style type analysis with Let generalisation}
\label{fig:type-analysis}
\end{figure}

To demonstrate the flexibility of our approach, we have implemented
Hindley-Milner-style type analysis including Let generalisation as an
instance of our abstract denotational interpreter.
The gist is given in \Cref{fig:type-analysis}; we omit large parts of the
implementation and the |Domain| instance for space reasons.
While the full implementation can be found in the extract generated from this
document, the |HasBind| instance is a sufficient exemplar of the approach.

The analysis infers most general |PolyType|s of the
form $\forall \many{\alpha}.\ θ$ for an expression, where $θ$ ranges over a
|Type| that can be either a type variable |TyVar α|, a function type |θ1 :->:
θ2|, or a type constructor application |TyConApp|.
The |Wrong| type is used to indicate a type error.

Key to the analysis is maintenance of a consistent set of type constraints
as a unifying |Subst|itution.
That is why the trace type |Cts| carries the current unifier as state, with the
option of failure indicated by |Maybe| when the unifier does not exist.
Additionally, |Cts| carries a set of used |Name|s with it to satisfy freshness
constraints in |freshTyVar| and |instantiatePolyTy|, as well as to construct a
superset of $\fv(ρ)$ in |generaliseTy|.

While the operational detail offered by |Trace| is ignored by |Cts|, all the
pieces fall together in the implementation of |bind|, where we see yet another
domain-specific fixpoint strategy:
The knot is tied by calling the iteratee |rhs| with a fresh unification variable
type |rhs_ty| of the shape $α_1$.
The result of this call in turn is instantiated to a non-|PolyType| |rhs_ty'|,
perhaps turning a type-scheme $\forall α_2.\ \mathtt{option}\;(α_2 \rightarrow
α_2)$ into the shape $\mathtt{option}\;(α_3 \rightarrow α_3)$ for fresh $α_3$.
Then a constraint is emitted to unify $α_1$ with
$\mathtt{option}\;(α_3 \rightarrow α_3)$.
Ultimately, the type |rhs_ty| is returned and generalised to $\forall α_3.\
\mathtt{option}\;(α_3 \rightarrow α_3)$, because $α_3$ is not a |Name| in use
before the call to |generaliseTy|, and thus it couldn't have possibly leaked
into the range of the ambient type context.
The generalised |PolyType| is then used when analysing the |body|.

\begin{table}
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |closedType (eval e emp)| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{i~i~i~i~i~i}$                  & $\perform{closedType $ eval (read "let i = λx.x in i i i i i i") emp}$ \\
(2) & $\Lam{x}{\Let{y}{x}{y~x}}$                          & $\perform{closedType $ eval (read "λx. let y = x in y x") emp}$ \\
(3) & $\Let{i}{\Lam{x}{x}}{\Let{o}{\mathit{Some}(i)}{o}}$ & $\perform{closedType $ eval (read "let i = λx.x in let o = Some(i) in o") emp}$ \\
(4) & $\Let{x}{x}{x}$                                     & $\perform{closedType $ eval (read "let x = x in x") emp}$ \\
\bottomrule
\end{tabular}
\caption{Examples for type analysis.}
\label{fig:type-examples}
\end{table}

\subsubsection*{Examples}
Let us again conclude with some examples in \Cref{fig:type-examples}.
Example (1) demonstrates repeated instantiation and generalisation.
Example (2) shows that let generalisation does not accidentally generalise the
type of |y|.
Example (3) shows an example involving data types and the characteristic
approximation to higher-rank types, and example (4) shows that type inference
for diverging programs works as expected.

\begin{figure}
\begin{code}
data Pow a = P (Set a); type CValue = Pow Label
type ConCache = (Tag, [CValue]); data FunCache = FC (Maybe (CValue, CValue)) (CD -> CD)
data Cache = Cache (Label :-> ConCache) (Label :-> FunCache)
data CT a = CT (State Cache a); type CD = CT CValue; runCFA :: CD -> CValue

updFunCache :: Label -> (CD -> CD) -> CT (); cachedCall :: Label -> CValue -> CD

instance HasBind CD where{-" ... \iffalse "-}
  bind rhs body = go bottom >>= body . return
    where
      go :: CValue -> CT CValue
      go v = do
        cache <- CT get
        v' <- rhs (return v)
        cache' <- CT get
        if v' ⊑ v && cache' ⊑ cache then do { v'' <- rhs (return v'); if v' /= v'' then error "blah" else return v' } else go v'
{-" \fi "-}; instance Trace (CT v) where step _ = id
instance Domain CD where
  fun _ ell f = do updFunCache ell f; return (P (Set.singleton ell))
  apply dv da = dv >>= \(P ells) -> da >>= \a -> lub <$> traverse (\ell -> cachedCall ell a) (Set.toList ells)
  {-" ... \iffalse "-}
  stuck = return bottom
  con ell k ds = do vs <- sequence ds; updConCache ell k vs; return (P (Set.singleton ell))
  select dv fs = do
    P ells <- dv
    cache <- CT get
    vals <- sequence [ f (map return vs) | ell <- Set.toList ells, Just (k',vs) <- [Map.lookup ell (cCons cache)]
                     , (k,f) <- Map.assocs fs, k == k' ]
    return (lub vals)
{-" \fi "-}
\end{code}

%if style == newcode
\begin{code}
deriving instance Eq a => Eq (Pow a)
deriving instance Ord a => Ord (Pow a)

instance Show (CValue) where
  showsPrec _ (P s) =
    showString "\\{" . showSep (showString ", ") (map showString (Set.toList s)) . showString "\\}"

instance Ord a => Lat (Pow a) where
  bottom = P Set.empty
  P l ⊔ P r = P (Set.union l r)

instance Eq FunCache where
  FC cache1 _ == FC cache2 _ = cache1 == cache2
instance Lat FunCache where
  bottom = FC Nothing (const (return bottom))
  FC cache1 f1 ⊔ FC cache2 f2 = FC cache' f'
    where
      f' d = do
        v <- d
        lv <- f1 (return v)
        rv <- f2 (return v)
        return (lv ⊔ rv)
      cache' = case (cache1,cache2) of
        (Nothing, Nothing)            -> Nothing
        (Just c1, Nothing)            -> Just c1
        (Nothing, Just c2)            -> Just c2
        (Just (in_1,out1), Just (in_2,out2))
          | in_1 ⊑ in_2, out1 ⊑ out2  -> Just (in_2, out2)
          | in_2 ⊑ in_1, out2 ⊑ out1  -> Just (in_1, out1)
          | otherwise                 -> error "uh oh"

instance Show FunCache where
  show (FC Nothing _)           = "[]"
  show (FC (Just (in_, out)) _) = "[" ++ show in_ ++ " \\mapsto " ++ show out ++ "]"

instance Eq Cache where
  c1 == c2 = cFuns c1 == cFuns c2 && cCons c1 == cCons c2

instance Lat Cache where
  bottom = Cache Map.empty Map.empty
  c1 ⊔ c2 = Cache (f cCons) (f cFuns)
    where
      f fld = fld c1 ⊔ fld c2

deriving instance Show Cache

unCT :: CT a -> State Cache a
unCT (CT m) = m

runCFA (CT m) = evalState m (Cache bottom bottom)

deriving instance Functor CT

instance Applicative CT where
  pure = CT . pure
  (<*>) = ap

instance Monad CT where
  CT m >>= k = CT (m >>= unCT . k)

-- | This instance is a huge hack, but it works.
-- If we were serious, we should have used the flat lattice over `Tag`.
instance Lat Tag where
  bottom = error "no bottom Tag"
  k1 ⊔ k2 = if k1 /= k2 then error "k1 /= k2" else k1

instance Lat a => Lat [a] where
  bottom = []
  [] ⊔ ys = ys
  xs ⊔ [] = xs
  (x:xs) ⊔ (y:ys) = x ⊔ y : xs ⊔ ys

cCons :: Cache -> Label :-> ConCache
cCons (Cache cons _) = cons

overCons :: ((Label :-> ConCache) -> (Label :-> ConCache)) -> Cache -> Cache
overCons f (Cache cons funs) = Cache (f cons) funs

cFuns :: Cache -> Label :-> FunCache
cFuns (Cache _ funs) = funs

overFuns :: ((Label :-> FunCache) -> (Label :-> FunCache)) -> Cache -> Cache
overFuns f (Cache cons funs) = Cache cons (f funs)

updConCache :: Label -> Tag -> [CValue] -> CT ()
updConCache ell k vs = CT $ modify $ overCons $ \cons ->
  Map.singleton ell (k, vs) ⊔ cons

updFunCache ell f = CT $ modify $ overFuns $ \funs ->
  Map.singleton ell (FC Nothing f) ⊔ funs

cachedCall ell v = CT $ do
  FC cache f <- gets (Map.findWithDefault bottom ell . cFuns)
  let call in_ out = do
        let in_' = in_ ⊔ v      com merge all Labels that reach the lambda var ell!
        modify $ overFuns (Map.insert ell (FC (Just (in_',out)) f))
        out' <- unCT (f (return in_'))
        modify $ overFuns (Map.insert ell (FC (Just (in_',out')) f))
        return out'
  case cache of
    Just (in_,out)
      | v ⊑ in_   -> return out
      | otherwise -> call in_ out
    Nothing       -> call bottom bottom
\end{code}
%endif
\vspace{-1.5em}
\caption{0CFA}
\label{fig:cfa}
\end{figure}

\subsection{Control-flow Analysis}

In our last example, we will discuss a classic benchmark of abstract
higher-order interpreters: Control-flow analysis (CFA).
CFA calculates an approximation of which values an expression might evaluate to,
so as to narrow down the possible control-flow edges at application sites.
The resulting control-flow graph conservatively approximates the control-flow of
the whole program and can be used to apply classic intraprocedural analyses such
as interval analysis in a higher-order setting.

To facilitate CFA, we have to revise the |Domain| class to pass down a
\emph{label} from allocation sites, which is to serve as the syntactic proxy of
the value's control-flow node:
\begin{spec}
type Label = String
class Domain d where
  con  :: {-" \highlight{ "-}Label -> {-" {}} "-} Tag -> [d] -> d
  fun  :: Name -> {-" \highlight{ "-}Label -> {-" {}} "-} (d -> d) -> d
\end{spec}
\noindent
We omit how to forward labels appropriately in |eval| and how to adjust
|Domain| instances.

\Cref{fig:cfa} gives a rough outline of how we use this extension to define a 0CFA:%
\footnote{As before, the extract of this document contains the full, executable
definition.}
An abstract |CValue| is the usual set of |Label|s standing in for a syntactic
value.
The trace abstraction |CT| maintains as state a |Cache| that approximates the
shape of values at a particular |Label|, an abstraction of the heap.
For constructor values, the shape is simply a pair of the |Tag| and |CValue|s
for the fields.
For a lambda value, the shape is its abstract control-flow transformer, of
type |CD -> CD| (populated by |updFunCache|), plus a single point |(v1,v2)| of
its graph ($k$-CFA would have one point per contour), serving as the transformer's
summary.

At call sites in |apply|, we will iterate over each function label and attempt a
|cachedCall|.
In doing so, we look up the label's transformer and sees if the single point
is applicable for the incoming value |v|, \eg, if |v ⊑ v1|, and if so return the
cached result |v2| straight away.
Otherwise, the transformer stored for the label is evaluated at |v| and the
result is cached as the new summary.
An allocation site might be re-analysed multiple times with monotonically increasing
environment due to fixpoint iteration in |bind|.
Whenever that happens, the point that has been cached for that allocation
site is cleared, because the function might have increased its result.
Then re-evaluating the function at the next |cachedCall| is mandatory.

Note that a |CD| transitively (through |Cache|) recurses into |CD -> CD|, thus
introducing vicious cycles in negative position, rendering the encoding
non-inductive.
This highlights a common challenge with instances of CFA: The obligation to
prove that the analysis actually terminates on all inputs; an obligation that we
will gloss over in this work.

\begin{table}
\begin{tabular}{cll}
\toprule
\#  & |e|                                               & |runCFA (eval e emp)| \\
\midrule
(1) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$   & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i j") emp}$ \\
(2) & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$ & $\perform{runCFA $ eval (read "let i = λx.x in let j = λy.y in i i j") emp}$ \\
(3) & $\Let{ω}{\Lam{x}{x~x}}{ω~ω}$                      & $\perform{runCFA $ eval (read "let ω = λx. x x in ω ω") emp}$ \\
(4) & $\Let{x}{\Let{y}{S(x)}{S(y)}}{x}$                 & $\perform{runCFA $ eval (read "let x = let y = S(x) in S(y) in x") emp}$ \\
\bottomrule
\end{tabular}
\caption{Examples for control-flow analysis.}
\label{fig:cfa-examples}
\end{table}

\subsubsection*{Examples}
The first two examples of \Cref{fig:cfa-examples} demonstrate a precise and an
imprecise result, respectively. The latter is due to the fact that both |i| and
|j| flow into |x|.
Examples (3) and (4) show that the |HasBind| instance guarantees termination for
diverging programs and cyclic data.
\end{toappendix}

\begin{comment}
\subsection{Bonus: Higher-order Cardinality Analysis}

In the style of \citet{Sergey:14}.
\sg{Flesh out, move to Appendix or remove. I left this section in for Ilya to
have a look. |call 2| means ``assume an evaluation context that applies 2
arguments'', |anyCtx| means ``evaluate in any evaluation context'' (top).}

\begin{tabular}{clll}
\toprule
\#  & |f|      & |e|                                                                    & |f e| \\
\midrule
(1) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j~j}}$                      & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j j"}$ \\
(2) & |anyCtx| & $\Let{i}{\Lam{x}{x}}{\Let{j}{\Lam{y}{y}}{i~j}}$                        & $\perform{anyCtx "let i = λx.x in let j = λy.y in i j"}$ \\
(3) & |call 2| & $\Let{i}{\Lam{x}{x}}{i}$                                               & $\perform{call 2 "let i = λx.x in i"}$ \\
(4) & |call 2| & $\Let{\mathit{const}}{\Lam{x}{\Lam{y}{y}}}{\mathit{const}}$            & $\perform{call 2 "let const = λx.λy.y in const"}$ \\
(5) & |call 2| & $\Let{f}{\Lam{a}{\Lam{g}{\Let{t}{g~a}{t~t}}}}{\mathit{f}}$ & $\scriptstyle \perform{call 2 "let f = λa. λg. let t = g a in t t in f"}$ \\
%(6) & |anyCtx| & $\Let{z}{Z()}{\Let{o}{S(z)}{\Let{\mathit{plus}}{\Lam{a}{\Lam{b}{...S(\mathit{plus}~(a-1)~b)...}}}{\mathit{plus}~z~o}}}$
%               & $\perform{anyCtx "let z = Z() in let o = S(z) in let plus = λa.λb. case a of { Z() -> b; S(n) -> let plusn = plus n b in S(plusn) } in plus z o"}$ \\
\bottomrule
\end{tabular}
\end{comment}
