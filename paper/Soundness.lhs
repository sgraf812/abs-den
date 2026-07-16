%options ghci -ihs -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures

%if style == newcode
%include custom.fmt
\begin{code}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Soundness where

import Prelude hiding ((+), (*))
import Data.Set (Set)
import qualified Data.Set as Set
import Interpreter

instance Eq DName where
  (==) = undefined
instance Ord DName where
  compare = undefined
data Pow a = P (Set a) deriving (Eq, Ord)
powMap :: (a -> b) -> Pow a -> Pow b
powMap f (P s) = P $ undefined $ map f $ Set.toList s
set = P . Set.singleton
\end{code}
%endif

\section{Generic Abstract By-Need Interpretation}
\label{sec:soundness}

\begin{toappendix}
\label{sec:soundness-detail}

So far, we have seen how to \emph{use} the abstraction
\Cref{thm:abstract-by-need}, but not proved it.
Proving this theorem correct is the goal of this section,
and we approach the problem from the bottom up.

We will discuss why it is safe to approximate guarded fixpoints with
least fixpoints and why the definition of the Galois connection in
\Cref{fig:abstract-name-need} as a fold over the trace is well-defined
in \Cref{sec:safety-extension}.
Then we will prove sound abstract by-need interpretation in
\Cref{sec:by-need-soundness}.

%include soundness-appendix.lhs
\end{toappendix}

\begin{figure}
\[\ruleform{\begin{array}{c}
  α_{\mathcal{S}} : (|(Name :-> DNeed) -> DNeed|) \to (|(Name :-> hat D) -> hat D|)
  \\
  α_{\Environments} : \pow{|Heap| \times (|Name :-> DNeed|)} \rightleftarrows (|Name :-> hat D|) : γ_{\Environments}
  \\
  α_{\Domain{}} : |Heap| \to (\pow{|DNeed|} \rightleftarrows |hat D|) : γ_{\Domain{}}
  \\
  α_\Traces : \pow{|T (ValueNeed, Heap)|} \rightleftarrows |hat D| : γ_\Traces
  \qquad
  β_\Traces : |T (ValueNeed, Heap)| \to |hat D|
  \qquad
\end{array}}\]
\belowdisplayskip=0pt
\arraycolsep=2pt
\[\begin{array}{lcl}
α_{\mathcal{S}}(S)(\widehat{ρ}) & = & α_\Traces(\{\  S(ρ)(μ) \mid (μ,ρ) ∈ γ_{\Environments}(\widehat{ρ}) \ \}) \\
α_{\Environments}(E)(x) & = & α_\Traces(\{\  ρ(x)(μ) \mid (μ,ρ) ∈ E \ \}) \\
α_{\Domain{}}(μ)(D) & = & α_\Traces(\{\  d(μ) \mid d ∈ D \ \}) \\
α_\Traces(T) & = & \Lub \{\ β_\Traces(τ) \mid τ ∈ T \ \} \\
\\[-0.75em]
β_\Traces(|τ|) & = & \begin{cases}
  |step e (βT ^ (τ'))| & \text{if |τ = Step e τ'|} \\
  |stuck|                         & \text{if |τ = Ret (Stuck, μ)|} \\
  |fun (αD^(μ) . powMap f . γD^(μ))| & \text{if |τ = Ret (Fun f, μ)|} \\
  |con k (map (αD^(μ) . set) ds)| & \text{if |τ = Ret (Con k ds, μ)|} \\
  \end{cases} \\
\end{array}\]
\caption{Galois connection $α_{\mathcal{S}}$ for by-need abstraction derived from |Domain| and |Lat| instances on |hat D|}
\label{fig:abstract-name-need}
\end{figure}

Recall that usage analysis is supposed to infer the semantic property of
absence (\Cref{defn:absence}) in order to inform dead code elimination.
In this section, we prove that usage analysis indeed infers absence.
This is the second half of the proof split described in \Cref{sec:introduction}:
\Cref{sec:adequacy} discharged the analysis-free congruence with the machine, and
what remains is to relate the analysis to the interpreter.
That relation is well understood via abstract
interpretation~\citep{Cousot:77}, and we capture it in a generalised statement of
the form
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
This statement can be read as follows:
For an expression |e|, the \emph{static analysis} |evalD2 (hat D) e|
on the right-hand side \emph{overapproximates} ($⊒$) a property of the by-need
\emph{semantics} |evalNeed1 e| on the left-hand side.
The abstraction function $α_{\mathcal{S}}$, given in
\Cref{fig:abstract-name-need}, defines the semantic property of interest in
terms of the abstract domain |hat D| of |evalD (hat D) e ρ|, which is
short for |eval e ρ :: hat D|.
That is: the type class instances on |hat D| determine $α_{\mathcal{S}}$, and
hence the semantic property that is soundly abstracted by |evalD (hat D) e ρ|.%
\footnote{Again, note that |evalD (hat D) e ρ| is a decidable algorithm, in
contrast to $α_{\mathcal{S}}(|evalNeed1 e|)$.
To give just one example, computing the latter diverges whenever the evaluation
of |e| diverges.}

We will instantiate this statement at |UD| in order to prove that usage analysis
|evalUsg e ρ = evalD UD e ρ| infers absence.
The complicated step-indexed heap reasoning is confined to the reusable abstract
interpretation theorem, so the analysis-specific part of the proof stays small.

\begin{figure}
  \belowdisplayskip=0pt
  \[\resizebox{\textwidth}{!}{$\begin{array}{cc}
    \multicolumn{2}{c}{\inferrule[\textsc{Mono}]
      {}
      {\text{|step|, |stuck|, |fun|, |apply|, |con|, |select|, |bind| monotone}}} \\
    \\[-0.5em]
    \inferrule[\textsc{Step-App}]{}{%
      |step ev (apply d a) ⊑ apply (step ev d) a|}
    &
    \inferrule[\textsc{Step-Sel}]{}{%
      |step ev (select d alts) ⊑ select (step ev d) alts|} \\
    \\[-0.5em]
    \multicolumn{2}{c}{\inferrule[\textsc{Stuck-App}]
      {|d ∈ set (stuck, con k ds)|}
      {|stuck ⊑ apply d a|}} \\
    \\[-0.5em]
    \multicolumn{2}{c}{\inferrule[\textsc{Stuck-Sel}]
      {|d ∈ set (stuck, fun x f) ∪ set (con k ds || k {-"\not"-}∈ dom alts ∨ length ds //= conArity k)|}
      {|stuck ⊑ select d alts|}} \\
    \\[-0.5em]
    \inferrule[\textsc{App-Fun}]
      {|f| \text{ polymorphic} \\ |x|\text{ fresh}}
      {|f a ⊑ apply (fun x f) a|}
    &
    \inferrule[\textsc{Sel-Con}]
      {|alts| \text{ polymorphic} \\ |k ∈ dom alts| \\ |length ds = conArity k|}
      {|(alts ! k) ds ⊑ select (con k ds) alts|} \\
    \\[-0.5em]
    \inferrule[\textsc{Bind-Prefix}]
      {}
      {|rhs (bind rhs id) ⊑ bind rhs id|}
    &
    \inferrule[\textsc{Bind-Lazy}]
      {}
      {|body (bind rhs id) ⊑ bind rhs body|} \\
    \\[-0.5em]
    \multicolumn{2}{c}{\fcolorbox{lightgray}{white}{$\begin{array}{c}
      \inferrule[\textsc{Step-Inc}]{}{|d ⊑ step ev d|}
      \qquad
      \inferrule[\textsc{Update}]{}{|step Upd d = d|}
    \end{array}$}}
  \end{array}$}\]
  \caption{Abstraction laws for type class instances of abstract domain |hat D|; the \fcolorbox{lightgray}{white}{highlighted} laws capture by-need memoisation}
  \label{fig:abstraction-laws}
\end{figure}

\subsection{A Reusable Abstract By-Need Interpretation Theorem}

In this subsection, we explain \Cref{thm:abstract-by-need} for
abstract by-need interpretation, the reusable fundamental theorem promised in
\Cref{sec:introduction}, which we will apply to prove usage analysis
sound in \Cref{sec:usage-sound}.
The theorem corresponds to the following derived inference rule, referring to
the \emph{abstraction laws} in \Cref{fig:abstraction-laws} by name:
\[\begin{array}{c}
  \inferrule{%
    \textsc{Mono} \\ \textsc{Step-App} \\ \textsc{Step-Sel} \\ \textsc{Stuck-App} \\
    \textsc{Stuck-Sel} \\ \textsc{App-Fun} \\ \textsc{Sel-Con} \\ \textsc{Bind-Prefix} \\
    \textsc{Bind-Lazy} \\ \textsc{Step-Inc} \\ \textsc{Update}
  }{%
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|
  }
\end{array}\]
\noindent
In other words: prove the abstraction laws for an abstract domain |hat D| of
your choosing (such as |UD|) and we give you a proof of sound abstract by-need
interpretation for the static analysis |evalD2 (hat D)|!

This statement can be read in three ways, each rooted in a different tradition.
It is a \emph{sound abstract interpretation}~\citep{Cousot:77}: the analysis
over-approximates the best abstraction of the concrete semantics.
It is a \emph{step-indexed logical relation}~\citep{AppelMcAllester:01} between the
concrete and abstract denotations, indexed by the length of the trace prefix under
consideration; the object language is untyped, yet this is a genuine logical relation,
with Löb induction on the step index in the role that induction on type structure
ordinarily plays.
And it is a \emph{preservation} proof~\citep{WrightFelleisen:94}, following one reduction
step and showing the abstraction bound is maintained.
The three are one and the same obligation.

Note that \emph{we} get to determine the abstraction function $α_{\mathcal{S}}$ based
on the |Domain| and |Lat| instances on \emph{your} |hat D|.
\Cref{fig:abstract-name-need} defines how $α_{\mathcal{S}}$ is thus derived.

Let us calculate |αS| for the closed example expression
$\pe \triangleq \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i}$:
\begin{align}
    & |αS^(evalNeed1 (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})))^(emp)| \notag \\
={} & |βT^(evalNeed (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})) emp emp)| \label{eqn:abs-ex1} \\
={} & |βT|(\perform{evalNeed (read "let i = (λy.λx.x) i in i") emp emp :: T (ValueNeed, Heap)}) \label{eqn:abs-ex2} \\
={} & \textstyle|step Let1 (step (Look "i") (... (fun (\(hat d) -> Lub (βT^({-" \AppET \smallstep \varid{d}([0\!\!↦\!\!\wild]) "-}space) || d ∈ γD^({-"[0\!\!↦\!\!\wild]"-}space)^((hat d)))))))| \notag \\
⊑{} & \textstyle|step Let1 (step (Look "i") (... (fun (\(hat d) -> step App2 (hat d)))))| \label{eqn:abs-ex3} \\
={} & |MkUT (singenv "i" U1) (UCons U1 (Rep Uω)) :: UD| \label{eqn:abs-ex4} \\
={} & |evalUsg (({-" \Let{i}{(\Lam{y}{\Lam{x}{x}})~i}{i} "-})) emp| \notag
\end{align}
\noindent
In (\ref{eqn:abs-ex1}), $α_{\mathcal{S}}(|evalNeed1 e|)(|emp|)$ simplifies to |βT^(evalNeed e emp
emp)|.
Function |βT| then folds the by-need trace (\ref{eqn:abs-ex2}) into an abstract
domain element in |hat D|.
It does so by eliminating every |Step ev| in the trace with a call to
|step ev|, and every concrete |Value| at the end of the trace with a
call to the corresponding |Domain| method, following the structure of
types as in \citet{Backhouse:04}.
Since |hat D| has a |Lat| instance, |βT| is a \emph{representation
function}~\citep[Section 4.3]{Nielson:99}, giving rise to Galois connections
$α_\Traces \rightleftarrows γ_\Traces$ and
$α_\Domain(μ) \rightleftarrows γ_\Domain(μ)$.
This implies that $α_\Domain(μ) \circ γ_\Domain(μ) ⊑ \mathit{id}$,
justifying the approximation step $(⊑)$ in (\ref{eqn:abs-ex3}).
For the concrete example, we instantiate |hat D| to |UD| in step
(\ref{eqn:abs-ex4}) to see that the resulting usage type indeed
coincides with the result of |evalUsg1|, as predicted by the abstract
interpretation theorem.

The abstraction function |αD| for by-need elements |d| is a bit unusual because
it is \emph{indexed} by a heap to give meaning to addresses referenced by |d|.
Our framework is carefully set up so that |αD^(μ)| is preserved when |μ|
is modified by memoisation ``in the future'', reminiscent of
\citeauthor{Kripke:63}'s possible worlds.
For similar reasons, the abstraction function for environments is defined on
pairs |(μ,ρ)| of a heap and a definable by-need environment, the entries of
which are of the form |step (Look y) (fetch a)|.

Thanks to fixing $α_{\mathcal{S}}$, we can prove the following abstraction theorem,
corresponding to the inference rule at the beginning of this subsection:

\begin{theorem}[Abstract By-need Interpretation]
\label{thm:abstract-by-need}
Let |e| be an expression, |hat D| a domain with instances for |Domain| and
|Lat|, and let $α_{\mathcal{S}}$ be the abstraction function from \Cref{fig:abstract-name-need}.
If the abstraction laws in \Cref{fig:abstraction-laws} hold,
then |evalD2 (hat D)| is an abstract interpreter that is sound \wrt $α_{\mathcal{S}}$,
that is,
\[
  α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalD2 (hat D) e|.
\]
\end{theorem}
\noindent
The proof is given in the extended version.
In Lean, this theorem is mechanised as |byNeed_sound| (\Cref{sec:mechanisation}), the
fundamental lemma of the by-need logical relation.

Let us unpack law $\textsc{App-Fun}$ to see how the abstraction laws in
\Cref{fig:abstraction-laws} are to be understood.
To prove $\textsc{App-Fun}$, one has to show that
|forall f a x. f a ⊑ apply (fun x f) a| in the abstract domain |hat D|.
This states that summarising |f| through |fun|, then |apply|ing the summary to
|a| must approximate a direct call to |f|;
it amounts to proving correct the summary mechanism.
The ``$|f|\text{ polymorphic}$'' premise asserts that |f| is definable at
polymorphic type |forall d. Domain d => d -> d|, which is
important to prove \textsc{App-Fun} (in \Cref{sec:mod-subst}).

Law \textsc{Sel-Con} states a similar property for data constructor redexes.
Laws \textsc{Bind-Prefix} and \textsc{Bind-Lazy} govern the abstract |bind|: the value
|bind rhs id| it computes is a pre-fixpoint of |rhs| (\textsc{Bind-Prefix}), and |bind|
passes that same value to any body (\textsc{Bind-Lazy}).
The remaining laws are congruence rules involving |step| and |stuck| as well as
a monotonicity requirement for all involved operations.
These laws follow the mantra ``evaluation improves approximation''; for
example, law \textsc{Stuck-App} expresses that applying a stuck term
or constructor evaluates to (and thus approximates) a stuck term, and
\textsc{Stuck-Sel} expresses the same for |select| stack frames.
Laws \textsc{Step-Inc} and \textsc{Update} capture by-need memoisation; all other
laws are independent of the evaluation strategy.

Note that none of the laws mention the concrete semantics or the abstraction
function $α_{\mathcal{S}}$.
This is how fixing the concrete semantics and $α_{\mathcal{S}}$ pays off; the usual
abstraction laws such as
|αD^(μ)^(apply d a) ⊑ hat apply (αD^(μ)^(d)) (αD^(μ)^(a))| further
decompose into \textsc{App-Fun}.
We think this is a nice advantage of our approach, because the author of
the analysis does not need to reason about by-need heaps in order to soundly
approximate a semantic trace property expressed via a |Domain| instance!

\subsection{A Modular Proof for \textsc{App-Fun}}
\label{sec:mod-subst}

\begin{toappendix}
\subsection{Usage Analysis Proofs}

Here we give the usage analysis proofs for the main body, often deferring to
\Cref{sec:by-need-soundness}.
\end{toappendix}

In order to instantiate \Cref{thm:abstract-by-need} for usage analysis in
\Cref{sec:usage-sound}, we need to prove in particular that |UD| satisfies the
abstraction law \textsc{App-Fun} in \Cref{fig:abstraction-laws}.
\textsc{App-Fun} is where the correctness of the summary mechanism lives, so it
is worth dwelling on how to prove it.

A direct proof would unfold the complete definition of the interpreter and reason
about each case, so its complexity scales with the size of the interpreter and it
must be redone whenever |eval| changes.
Such non-modular proofs become unmanageable on pen and paper for large
denotational interpreters such as the one for WebAssembly~\citep{Brandl:23}.

For \textsc{App-Fun}, dubbed \emph{semantic substitution}, we can do much better:
\begin{toappendix}
\begin{abbreviation}[Field access]
  |(MkUT φ' v')^.φ := φ'|, |(MkUT φ' v')^.v = v'|.
\end{abbreviation}
\end{toappendix}

\begin{lemma}[\textsc{App-Fun}, Semantic substitution]
\label{thm:usage-subst-sem}
Let |f :: forall d. Domain d => d -> d|, |x :: Name| fresh and |a :: UD|.
Then |f a ⊑ apply (fun x f) a| in |UD|.
\end{lemma}

As can be seen, its statement does not refer to the interpreter definition
|eval| \emph{at all}.
Instead, the complexity of its proof scales with the number of \emph{abstract
operations} supported in the semantic domain, not with the size of the
interpreter; that is what makes it \emph{modular}.
This modular proof appeals to parametricity~\citep{Reynolds:83} of |f|'s
polymorphic type |forall d. Domain d => d -> d|.
Of course, any function defined by the generic interpreter satisfies this
requirement.
The proof instantiates |f|'s free theorem at a relation
that calls |f| with the proxy |MkUT (singenv x U1) (Rep Uω)| that
the implementation of |fun x| supplies; the obligation then reduces to one lemma
per type class method that is easily discharged.
\textsc{App-Fun} for |UD| is mechanised in Lean (\Cref{sec:mechanisation}).

The polymorphism premise is essential: without it, \textsc{App-Fun} fails for
usage analysis.
\begin{example}
\label{ex:syntactic-beta-app}
Let |z //= x //= y|.
The monotone but non-polymorphic |f| defined as follows
\begin{center}
\begin{spec}
  f :: UD -> UD
  f (MkUT φ _) = if φ !? y ⊑ U0 then MkUT emp (Rep Uω) else MkUT (singenv z U1) (Rep Uω)
\end{spec}
\end{center}
violates |f a ⊑ apply (fun x f) a|.
To see that, let |a := MkUT (singenv y U1) (Rep Uω) :: UD| and consider
\[
  |f a = MkUT (singenv z U1) (Rep Uω) {-" \not⊑ "-} (MkUT emp (Rep Uω)) = apply (fun x f) a|.
\]
\end{example}
Next, we will use \Cref{thm:usage-subst-sem} to instantiate
\Cref{thm:abstract-by-need} for usage analysis.

\subsection{Usage Analysis Infers Absence}
\label{sec:usage-sound}

Equipped with the generic abstract interpretation \Cref{thm:abstract-by-need},
we will prove in this subsection that usage analysis from \Cref{sec:abstraction}
infers absence (\Cref{defn:absence}).

\Cref{thm:abstract-by-need} does the work of relating
by-need semantics to usage analysis, taking the place of the hand-crafted
logical relation over machine configurations that a conventional proof
re-establishes for each analysis:

\begin{corollary}[|evalUsg1| abstracts |evalNeed1|]
\label{thm:usage-abstracts-need}
Let |e| be an expression and $α_{\mathcal{S}}$ the abstraction function from
\Cref{fig:abstract-name-need}.
Then $α_{\mathcal{S}}(|evalNeed1 e|) ⊑ |evalUsg1 e|$.
\end{corollary}
\noindent
Its proof discharges the premises of \Cref{thm:abstract-by-need}: \textsc{App-Fun}
is \Cref{thm:usage-subst-sem}, and the remaining abstraction laws for |UD| follow
by routine calculation.
The corollary is mechanised in Lean as |usage_abstracts_need|
(\Cref{sec:mechanisation}).

The next step is to leave behind the definition of absence in terms of the LK
machine in favour of one using |evalNeed2|.
That is a welcome simplification because it leaves us with a single semantic
artefact, the denotational interpreter, instead of an operational
semantics and a separate static analysis.
Thanks to bisimilarity (\Cref{thm:need-adequacy-bisimulation}), this new notion is not a
redefinition but provably equivalent to \Cref{defn:absence}:
\begin{lemma}[Denotational absence]
  \label{thm:absence-denotational}
  Variable |x| is used in |e| if and only if there exists a by-need evaluation context
  |ectxt| and expression |e'| such that the trace
  |evalNeed (fillC ectxt (Let x e' e)) emp emp| contains a |Look x| event.
  Otherwise, |x| is absent in |e|.
\end{lemma}
\noindent
Here, |fillC ectxt (Let x e' e)| plugs the let-binding into the hole of the
by-need evaluation context |ectxt|; the extended version defines these contexts
precisely.

Thus insulated from the LK machine, we may state that usage analysis
infers absence (\Cref{defn:absence}).

\begin{theorem}[|evalUsg| infers absence]
  \label{thm:usage-absence}
  Let |ρe := singenvmany y (MkUT (singenv y U1) (Rep Uω))| be the initial
  environment with an entry for every free variable |y| of an expression |e|.
  If |evalUsg e ρe = MkUT φ v| and |φ !? x = U0|,
  then |x| is absent in |e|.
\end{theorem}
\begin{proofsketch}
If |x| is used in |e|, there is a trace |evalNeed (fillC ectxt (Let x e' e)) emp emp| containing a |Look x| event.
The abstraction function $α_{\mathcal{S}}$ induced by |UD| aggregates lookups in the
trace into a |φ' :: Uses|, \eg
  $β_\Traces(\LookupT(i) \smallstep \LookupT(x) \smallstep \LookupT(i) \smallstep \langle ... \rangle)
    = |MkUT [ i {-" ↦ "-} Uω, x {-" ↦ "-} U1 ] (...)|$.
Clearly |φ' !? x ⊒ U1|, because there is at least one |Look x|.
\Cref{thm:usage-abstracts-need} and a context-invariance property prove that the computed
|φ| approximates |φ'|, so |φ !? x ⊒ φ' !? x ⊒ U1 //= U0|.
This is mechanised in Lean as |absence| (\Cref{sec:mechanisation}).
\end{proofsketch}

We have therefore proved that usage analysis correctly infers the semantic property
of absence, as defined in \Cref{defn:absence}.
From this result, one could further prove that dead code elimination constitutes
an optimisation that \emph{improves} the program in the sense of \citet{MoranSands:99}.
However, such a proof is typically best carried out in a high-level syntactic
inequational theory; we do not anticipate that the denotational interpreter
perspective offers a significant advantage in that context.

\subsection{A Decomposed Soundness Proof}

The soundness proof rests on a single semantic artefact: the denotational
interpreter, instantiated at |UD| and at the by-need domain. The proof is still
substantial, but it decomposes into three layers, each removing one source of
difficulty.

\begin{enumerate}
\item \emph{Adequacy removes the machine.} \Cref{sec:adequacy} relates the
  interpreter to the LK machine once, with no analysis involved. The soundness
  proof then speaks only of the interpreter's denotations, at |UD| and at the
  by-need domain. No machine configuration occurs in its step-indexed logical
  relation.
\item \emph{Lining up the definitions removes the interpreter.} Analysis and
  semantics are the same interpreter, so the two instances line up. One structural
  induction over the expression proves \Cref{thm:abstract-by-need}. The proof then
  reasons about domain elements and how |UD| abstracts a by-need denotation, no
  longer about the interpreter's definition.
\item \emph{The abstraction laws remove the by-need domain and its step-indexing.}
  What is left is to prove those laws (\Cref{fig:abstraction-laws}). They say
  nothing of the by-need domain, its step-indexing, or its Galois connection, so the
  reasoning stays entirely in the analysis's own semantic domain, which is what the
  author of an analysis prefers to think in.
\end{enumerate}

The advantage of this decomposition is that the proof stays intellectually
manageable, because each layer isolates one difficulty. A conventional proof, by
contrast, relates analysis and machine in a single step-indexed logical relation
over machine configurations. That relation is the creative core of the argument,
and its difficulty grows with both the semantics and the analysis. Here the first two layers handle the
machine and the interpreter without reference to the analysis, and the
analysis-specific work is confined to the abstraction laws of the third. Even the
hardest law, \textsc{App-Fun}, has a \emph{modular} proof by parametricity whose size
does not grow with the interpreter. All three layers are mechanised in Lean
(\Cref{sec:mechanisation}).

\begin{toappendix}
In the proof for \Cref{thm:usage-absence} we exploit that usage analysis is
somewhat invariant under wrapping of \emph{by-need evaluation contexts}, roughly
|Uω * evalUsg e ρe = evalUsg (fillC ectxt e) emp|. To prove that, we first
need to define what the by-need evaluation contexts of our language are.

\citet[Lemma 4.1]{MoranSands:99} describe a principled way to derive the
call-by-need evaluation contexts $\pE$ from machine contexts $(\hole,μ,κ)$ of
the Sestoft Mark I machine; a variant of \Cref{fig:lk-semantics} that uses
syntactic substitution of variables instead of delayed substitution and
addresses, so $μ ∈ \Var \pfun \Exp$ and no closures are needed.

We follow their approach, but inline applicative contexts,%
\footnote{The result is that of \citet[Figure 3]{Ariola:95} in A-normal form and
extended with data types.}
thus defining the by-need evaluation contexts with hole $\hole$ for our language as
\[\begin{array}{lcl}
  \pE ∈ \EContexts & ::= & \hole \mid \pE~\px \mid \Case{\pE}{\Sel} \mid \Let{\px}{\pe}{\pE} \mid \Let{\px}{\pE}{\pE[\px]} \\
\end{array}\]
The correspondence to Mark I machine contexts $(\hole,μ,κ)$ is encoded by the
following translation function $\mathit{trans}$ that translates from mark I
machine contexts  $(\hole,μ,κ)$ to evaluation contexts $\pE$.
\[\begin{array}{lcl}
  \mathit{trans} & : & \EContexts \times \Heaps \times \Continuations \to \EContexts \\
  \mathit{trans}(\pE,[\many{\px ↦ \pe}],κ) & = & \Letmany{\px}{\pe}{\mathit{trans}(\pE,[],κ)} \\
  \mathit{trans}(\pE,[],\ApplyF(\px) \pushF κ) & = & \mathit{trans}(\pE~\px,[],κ) \\
  \mathit{trans}(\pE,[],\SelF(\Sel) \pushF κ) & = & \mathit{trans}(\Case{\pE}{\Sel},[],κ) \\
  \mathit{trans}(\pE,[],\UpdateF(\px) \pushF κ) & = & \Let{\px}{\pE}{\mathit{trans}(\hole, [], κ)[\px]} \\
  \mathit{trans}(\pE,[],\StopF) & = & \pE \\
\end{array}\]
Certainly the most interesting case is that of $\UpdateF$ frames, encoding
by-need memoisation.
This translation function has the following property:
\begin{lemma}[Translation, without proof]
  \label{thm:translation}
  $\init(\mathit{trans}(\hole,μ,κ)[\pe]) \smallstep^* (\pe,μ,κ)$,
  and all transitions in this trace are search transitions ($\AppIT$, $\CaseIT$,
  $\LetIT$, $\LookupT$).
\end{lemma}
In other words: every machine configuration $σ$ corresponds to an evaluation
context $\pE$ and a focus expression $\pe$ such that there exists a trace
$\init(\pE[\pe]) \smallstep^* σ$ consisting purely of search transitions,
which is equivalent to all states in the trace except possibly the last being
search states.

We encode evaluation contexts in Haskell as follows, overloading hole filling notation |fillC|:
\begin{spec}
data ECtxt  =  Hole | Apply ECtxt Name | Select ECtxt Alts
            |  ExtendHeap Name Expr ECtxt | UpdateHeap Name ECtxt Expr
fillC :: ECtxt -> Expr -> Expr
fillC Hole e                      = e
fillC (Apply ectxt x) e           = App (fillC ectxt e) x
fillC (Select ectxt alts) e       = Case (fillC ectxt e) alts
fillC (ExtendHeap x e1 ectxt) e2  = Let x e1 (fillC ectxt e2)
fillC (UpdateHeap x ectxt e1) e2  = Let x (fillC ectxt e1) e2
\end{spec}

\begin{lemma}[Used variables are free]
  \label{thm:used-free}
  If |x| does not occur in |e| and in |ρ| (that is, |forall y. (ρ ! y)^.φ !?
  x = U0|), then |(evalUsg e ρ)^.φ !? x = U0|.
\end{lemma}
\begin{proof}
  By induction on |e|.
\end{proof}

For concise notation, we define the following abstract substitution operation:

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst-usage}
  We call |abssubst φ x φ' := (ext φ x U0) + (φ !? x) * φ'| the
  \emph{abstract substitution} operation on |Uses|
  and overload this notation for |UT|, so that
  |abssubst (MkUT φ v) x φ' := MkUT (abssubst φ x φ') v|.
\end{definition}

From \Cref{thm:usage-subst-sem}, we can derive the following auxiliary lemma:
\begin{lemma}
  \label{thm:usage-subst-abs}
  If |x| does not occur in |ρ|, then
  |evalUsg e (ext ρ x d) ⊑ abssubst (evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) x (d^.φ)|.
\end{lemma}
\begin{proof}
  Define |f (hat d) := evalUsg e (ext ρ x (hat d))| and |a := d|.
  Note that |f| could be defined polymorphically as
  |f d = eval e (ext ρ x d)|, for suitably polymorphic |ρ|.
  Furthermore, |x| could well be lambda-bound, since it does not occur in the
  range of |ρ| (and that is really what we need).
  Hence we may apply \Cref{thm:usage-subst-sem} to get
  \begin{spec}
    evalUsg e (ext ρ x d)
  ⊑   {- \Cref{thm:usage-subst-sem} -}
    apply (fun x (\(hat d) -> evalUsg e (ext ρ x (hat d)))) d
  =   {- Inline |apply|, |fun| -}
    let MkUT φ v = evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω))) in MkUT (ext φ x U0 + (φ !? x) * d^.φ) v
  =   {- Refold |abssubst| -}
    abssubst (evalUsg e (ext ρ x (MkUT (singenv x U1) (Rep Uω)))) x d^.φ
  \end{spec}
\end{proof}

\begin{lemma}[Context closure]
\label{thm:usage-bound-vars-context}
Let |e| be an expression and |ectxt| be a by-need evaluation context in which
|x| does not occur.
Then |(evalUsg (fillC ectxt e) ρE)^.φ ?! x ⊑ Uω * ((evalUsg e ρe)^.φ !? x)|,
where |ρE| and |ρe| are the initial environments that map free variables |z|
to their proxy |MkUT (singenv z U1) (Rep Uω)|.
\end{lemma}
\begin{proof}
We will sometimes need that if |y| does not occur free in |e1|, we have
By induction on the size of |ectxt| and cases on |ectxt|:
\begin{itemize}
  \item \textbf{Case }|Hole|:
    \begin{spec}
        (evalUsg (fillC Hole e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg e ρE)^.φ !? x
    ⊑   {- |ρe = ρE| -}
        Uω * (evalUsg e ρE)^.φ !? x

    \end{spec}
    By reflexivity.
  \item \textbf{Case }|Apply ectxt y|:
    Since |y| occurs in |ectxt|, it must be different to |x|.
    \begin{spec}
        (evalUsg (fillC (Apply ectxt y) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (App (fillC ectxt e) y) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (apply (evalUsg (fillC ectxt e) ρE) (ρE !? y))^.φ !? x
    =   {- Definition of |apply| -}
        let MkUT φ v = evalUsg (fillC ectxt e) ρE in
        case peel v of (u,v2) -> ((MkUT (φ + u*((ρE!?y)^.φ)) v2)^.φ !? x)
    =   {- Unfold |(MkUT φ v)^.φ = φ|, |x| absent in |ρE !? y| -}
        let MkUT φ v = evalUsg (fillC ectxt e) ρE in
        case peel v of (u,v2) -> φ !? x
    =   {- Refold |(MkUT φ v)^.φ = φ| -}
        (evalUsg (fillC ectxt e) ρE)^.φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|Select ectxt alts|:
    Since |x| does not occur in |alts|, it is absent in |alts| as well
    by \Cref{thm:used-free}.
    (Recall that |select| analyses |alts| with |MkUT emp (Rep Uω)| as
    field proxies.)
    \begin{spec}
        (evalUsg (fillC (Select ectxt alts) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Case (fillC ectxt e) alts) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (select (evalUsg (fillC ectxt e) ρE) (cont << alts))^.φ !? x
    =   {- Definition of |select| -}
        (evalUsg (fillC ectxt e) ρE >> lub (... alts ...))^.φ !? x
    =   {- |x| absent in |lub (... alts ...)| -}
        (evalUsg (fillC ectxt e) ρE)^.φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|ExtendHeap y e1 ectxt|:
    Since |x| does not occur in |e1|, and the initial environment
    is absent in |x| as well, we have |(evalUsg e1 ρE)^.φ !? x = U0| by
    \Cref{thm:used-free}.
    \begin{spec}
        (evalUsg (fillC (ExtendHeap y e1 ectxt) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Let y e1 (fillC ectxt e)) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (evalUsg (fillC ectxt e) (ext ρE y (step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))))))^.φ !? x
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst-abs} -}
        (abssubst (evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω)))) y (
          step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))))) ^.φ !? x
    =   {- Unfold |abssubst|, |(MkUT φ v)^.φ = φ| -}
        let MkUT φ  _ = evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg e1 (ext ρE y (step (Look y) d)))) in
        (ext φ y U0 + (φ !? y)*φ2) !? x
    =   {- |x| absent in |φ2|, see above -}
        let MkUT φ  _ = evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        φ !? x
    ⊑   {- Induction hypothesis -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
  \item \textbf{Case }|UpdateHeap y ectxt e1|:
    Since |x| does not occur in |e1|, and the initial environment
    is absent in |x| as well, we have
    |(evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω))))^.φ !? x = U0| by
    \Cref{thm:used-free}.
    \begin{spec}
        (evalUsg (fillC (UpdateHeap y ectxt e1) e) ρE)^.φ !? x
    =   {- Definition of |fillC| -}
        (evalUsg (Let y (fillC ectxt e) e1) ρE)^.φ !? x
    =   {- Definition of |evalUsg| -}
        (evalUsg e1 (ext ρE y (step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))))^.φ !? x
    ⊑   {- Abstract substitution; \Cref{thm:usage-subst-abs} -}
        (abssubst (evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω)))) y (
          step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))) ^.φ !? x
    =   {- Unfold |abssubst|, |(MkUT φ v)^.φ = φ| -}
        let MkUT φ  _ = evalUsg e1 (ext ρE y (MkUT (singenv y U1) (Rep Uω))) in
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))) in
        (ext φ y U0 + (φ !? y)*φ2) !? x
    =   {- |φ !? y ⊑ Uω|, |x| absent in |φ|, see above -}
        let MkUT φ2 _ = step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))) in
        Uω * φ2 !? x
    =   {- Refold |(MkUT φ v)^.φ| -}
        Uω * (step (Look y) (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y (step (Look y) d)))))^.φ !? x
    =   {- |x //= y| -}
        Uω * (kleeneFix (\d -> evalUsg (fillC ectxt e) (ext ρE y d)))^.φ !? x
    =   {- Argument below -}
        Uω * (evalUsg (fillC ectxt e) (ext ρE y (MkUT (singenv y U1) (Rep Uω))))^.φ !? x
    ⊑   {- Induction hypothesis, |Uω * Uω = Uω| -}
        Uω * (evalUsg e ρe)^.φ !? x
    \end{spec}
    The rationale for removing the |kleeneFix| is that under the assumption that
    |x| is absent in |d| (such as is the case for |d := MkUT (singenv y U1)
    (Rep Uω)|), then it is also absent in |fillC ectxt e (ext ρE y d)| per
    \Cref{thm:used-free}.
    Otherwise, we go to |Uω| anyway.

    |UpdateHeap| is why it is necessary to multiply with |Uω| above;
    in the context $\Let{x}{\hole}{x~x}$, a variable $y$ put in the hole
    would really be evaluated twice under call-by-name (where
    $\Let{x}{\hole}{x~x}$ is \emph{not} an evaluation context).

    This unfortunately means that the used-once results do not generalise
    to arbitrary by-need evaluation contexts and it would be unsound
    to elide update frames for $y$ based on the inferred use of $y$ in
    $\Let{y}{...}{\pe}$; for $\pe \triangleq y$ we would infer that $y$
    is used at most once, but that is wrong in context $\Let{x}{\hole}{x~x}$.
\end{itemize}
\end{proof}
\end{toappendix}

\subsection{Scope and Limitations}

The framework's reach has limits worth stating plainly.
The decomposition just described keeps the soundness proof manageable, but we have
exercised it on a single analysis. Whether its advantages carry over to a range of
analyses is so far a claim, not a result.
We expect few analyses beyond usage analysis to satisfy the abstraction laws of
\Cref{fig:abstraction-laws} unchanged, and a different source language may call for a
different domain. A different set of sufficient laws would still reuse the proof of
\Cref{thm:abstract-by-need} as its starting point.
The evaluation strategy constrains less than it appears: the challenge the framework
meets, soundly abstracting higher-order mutable state, is not specific to laziness.
Call-by-need memoisation reads, evaluates, and updates a heap of closures, the same
structure presented by strict languages with mutable references (ML) and by stateful
object-oriented interfaces (Java).
We chose call-by-need because it is the semantics GHC's static analyses approximate, and
expect the pattern to transfer to other paradigms that share this structure.
