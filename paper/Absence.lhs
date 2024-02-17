%if style == newcode
> module Problem where
%endif

\section{The Problem We Solve}
\label{sec:problem}

What is so difficult about proving a compositional, summary-based analysis sound
\wrt a non-compositional small-step operational semantics?
We will demonstrate the challenges in this section, by way of a simplified \emph{absence
analysis}~\citep{SPJ:94}, a higher-order form of neededness analysis to inform
removal of dead bindings in a compiler.

\subsection{Object Language}

To set the stage, we start by defining the object language of this work, a
lambda calculus with \emph{recursive} let bindings and algebraic data types:
\[
\arraycolsep=3pt
\begin{array}{rrclcrrclcl}
  \text{Variables}    & \px, \py & ∈ & \Var        &     & \quad \text{Constructors} &        K & ∈ & \Con        &     & \text{with arity $α_K ∈ ℕ$} \\
  \text{Values}       &      \pv & ∈ & \Val        & ::= & \highlight{\Lam{\px}{\pe}} \mid K~\many{\px}^{α_K} \\
  \text{Expressions}  &      \pe & ∈ & \Exp        & ::= & \multicolumn{6}{l}{\highlight{\px \mid \pv \mid \pe~\px \mid \Let{\px}{\pe_1}{\pe_2}} \mid \Case{\pe}{\SelArity}}
\end{array}
\]
This language is very similar to that of \citet{Launchbury:93} and \citet{Sestoft:97}.
It is factored into \emph{A-normal form}, that is, the arguments of applications
are restricted to be variables, so the difference between lazy and eager
semantics is manifest in the semantics of $\mathbf{let}$.
Note that $\Lam{x}{x}$ (with an overbar) denotes syntax, whereas $\fn{x}{x+1}$
denotes an anonymous mathematical function.
In this Section, only the highlighted parts are relevant, but the interpreter
definition in \Cref{sec:interp} supports data types as well.
Throughout the paper we assume that all bound program variables are distinct.
% Rationale for this:
% While shadowing is fine for the semantics, the analyses don't cope well with
% shadowing. Also Lookup events carry a Name and it becomes more complicated to
% explain when Lookup events might alias.
% It's not an uncommon assumption anyway, but we should state it IMO.

\subsection{Absence Analysis}
\label{sec:absence}

\begin{figure}
  %\fboxsep=0pt\fbox{%
  \[\ruleform{ \semabs{\wild}_{\wild} \colon \Exp → (\Var \pfun \AbsTy) → \AbsTy }\]
  \\[-0.5em]
  \begin{minipage}[t]{0.47\textwidth}
  \arraycolsep=0pt
  \abovedisplayskip=0pt
  \[\begin{array}{rcl}
    \semabs{\px}_ρ & {}={} & ρ(\px) \\
    \semabs{\Lam{\px}{\pe}}_ρ & {}={} & \mathit{fun}_{\px}( \fn{θ}{\semabs{\pe}_{ρ[\px ↦ θ]}}) \\
    \semabs{\pe~\px}_ρ & {}={} & \mathit{app}(\semabs{\pe}_{ρ})(ρ(\px)) \\
    \semabs{\Let{\px}{\pe_1}{\pe_2}}_ρ & {}={} & \semabs{\pe_2}_{ρ[\px ↦ \px \both \semabs{\pe_1}_ρ]} \\
    \\[-0.8em]
    \multicolumn{3}{c}{\mathit{fun}_{\px}( f) {}={} \langle φ[\px↦\aA], φ(\px) \sumcons \varsigma \rangle} \\
    \multicolumn{3}{c}{\qquad\qquad\text{where } \langle φ, \varsigma \rangle = f(\langle [\px↦\aU], \aU.. \rangle)} \\
    \multicolumn{3}{c}{\mathit{app}(\langle φ_f, a \sumcons \varsigma \rangle)(\langle φ_a, \wild \rangle) = \langle φ_f ⊔ (a * φ_a), \varsigma \rangle} \\
  \end{array}\]
  \end{minipage}%
  %}%
  \hfill
  %\fboxsep=0pt\fbox{%
  \begin{minipage}[t]{0.50\textwidth}
  \arraycolsep=0pt
  \abovedisplayskip=0pt
  \[\begin{array}{c}
  \begin{array}{rclcl}
    a & {}∈{} & \Absence & {}::={} & \aA \mid \aU \\
    φ & {}∈{} & \Uses    & {}={} & \Var \to \Absence \\
    \varsigma & {}∈{}    & \Summary & {}::={} & \aA.. \mid a \sumcons \varsigma \mid \aU.. \\
    θ & {}∈{} & \AbsTy   & {}::={} & \langle φ, \varsigma \rangle \\
    \\[-0.9em]
    \multicolumn{5}{c}{\aA.. \equiv \aA \sumcons \aA.. \quad \aU.. \equiv \aU \sumcons \aU..} \\
  \end{array} \\
  \\[-0.9em]
  \begin{array}{l}
    \aA * φ = [] \quad
    \aU * φ = φ  \\
    \px \both \langle φ, \varsigma \rangle = \langle φ[\px↦\aU], \varsigma \rangle
  \end{array}
  \\[-0.5em]
  \end{array}\]
  \end{minipage}%
  %}%
  \caption{Absence analysis}
  \label{fig:absence}
\end{figure}

Semantically, a variable $\px$ is \emph{absent} in an expression $\pe$ when
$\px$ is never evaluated by $\pe$, regardless of the context in which $\pe$
appears.
Otherwise, the variable $\px$ is \emph{used} in $\pe$.
%SG: Note the emphasis on context; indeed, absent means absent in all contexts,
%not just in a WHNF evaluation of $\pe$.

\Cref{fig:absence} defines an absence analysis $\semabs{\pe}_ρ$ for lazy
program semantics that conservatively approximates semantic absence.%
\footnote{For illustrative purposes, our analysis definition only works for
the special case of non-recursive let.
The generalised definition for recursive as well as non-recursive let is
$\semabs{\Let{\px}{\pe_1}{\pe_2}}_ρ = \semabs{\pe_2}_{ρ[\px ↦ \lfp(\fn{θ}{\px \both \semabs{\pe_1}_{ρ[\px↦θ]}})]}$.}
It takes an environment $ρ \in \Var \pfun \Absence$ containing absence
information about the free variables of $\pe$ and returns
an \emph{absence type} $\langle φ, \varsigma \rangle \in \AbsTy$; an abstract
representation of $\pe$.
The \emph{free variable uses} $φ \in \Uses$ captures how $\pe$ uses its free
variables by associating an $\Absence$ flag with each.
When $φ(\px) = \aA$, then $\px$ is absent in $\pe$; otherwise, $φ(\px) = \aU$
and $\px$ might be used in $\pe$.
The \emph{argument summary} $\varsigma \in \Summary$ describes how $\pe$ uses
actual arguments supplied at application sites.

Clearly if $\px$ is not free in $\pe$, then $\px$ is absent in $\pe$, but our
analysis does a bit better.\\
Consider the expression $\pe \triangleq \Let{f}{\Lam{x}{y}}{f~v}$.
Here, $v$ is a free variable of $\pe$, but it is absent because $f$ discards it.
The analysis figures out the same, by recording a summary $\varsigma$ in the
absence type for $f$ stored in the environment $ρ$.
For this particular example, the summary is $\aA \sumcons \aU..$, indicating
that $f$ is absent in its first argument but potentially uses any further
arguments.
The summary $\aU..$ can be thought of as a finite representation of an infinite
list of $\aU$, as expressed by the non-syntactic equality $\aU \equiv \aU
\sumcons \aU..$, and likewise for $\aA.. \equiv \aA \sumcons \aA..$.
Since $f$ also uses $y$, the absence type recorded in the environment at the
call site of $f$ looks like $ρ(f) = \langle [f ↦ \aU, y ↦ \aU], \aA
\sumcons aU.. \rangle$, indicating that the call $f~v$ uses the free variables
$f$ and $y$, \emph{but not} $v$.
(Note that the literal notation $[f ↦ \aU, y ↦ \aU] ∈ \Uses$ maps any
variable other than $f$ and $y$ to $\aA$.)

%When $\semabs{\pe}_{ρ_{\pe}} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
%then $\px$ is absent in $\pe$, where $ρ_{\pe}$ is the free variable environment
%defined as
%\[
%  ρ_{\pe}(\px) \triangleq \langle [\px ↦ \aU], \aU.. \rangle, \quad \text{(if $\px ∈ \fv(\pe)$)}.
%\]

%In a slight extension of function update syntax, $[\px ↦ \aU]$ denotes a $φ$
%where $φ(\px) = \aU$ and $φ(\py) = \aA$ for $\px \not= \py$.
%Now we can understand $ρ_{\pe}$ to say that evaluation of each free variable
%$\px$ uses only $\px$, and that any actual argument it is applied to is used,
%indicated by argument summary $\aU..$\ .

We illustrate the analysis at the example expression
$\Let{x_2}{x_1}{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}$, where the initial
environment for $\pe$, $ρ_\pe(\px) \triangleq \langle [\px ↦ \aU], \aU.. \rangle$,
declares the free variables of $\pe$ with a pessimistic summary $\aU..$.
\begin{DispWithArrows}[fleqn,mathindent=0em]
      & \semabs{\Let{x_2}{x_1}{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}}_{ρ_{\pe}} \label{eq:abs-ex1}
        \Arrow{Unfold $\semabs{\Let{\px}{\pe_1}{\pe_2}}$. NB: Lazy Let!} \\
  ={} & \semabs{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}_{ρ_{\pe}[x_2↦x_2 \both \semabs{x_1}_{ρ_{\pe}}]} \label{eq:abs-ex2}
        \Arrow{Unfold $\semabs{\wild}$, $ρ_x \triangleq ρ_{\pe}[x_2 ↦ x_2 \both \semabs{x_1}_{ρ_{\pe}}]$} \\
  ={} & \semabs{k~x_3~x_2}_{ρ_x[k↦k \both \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x}]}
        \Arrow{$ρ_{xk} \triangleq ρ_x[k↦k \both \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x}]$} \\
  ={} & \semabs{k~x_3~x_2}_{ρ_{xk}}
        \Arrow{Unfold $\semabs{\pe~\px}$ twice, $\semabs{\px}$} \\
  ={} & \mathit{app}(\mathit{app}(ρ_{xk}(k),ρ_{xk}(x_3)))(ρ_{xk}(x_2))
        \Arrow{Unfold $ρ_{xk}(k)$} \\
  ={} & \mathit{app}(\mathit{app}(k \both \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x})(ρ_{xk}(x_3)))(ρ_{xk}(x_2))
        \Arrow{Unfold $\semabs{\Lam{\px}{\pe}}$ twice, $\semabs{\px}$} \\
  ={} & \mathit{app}(\mathit{app}(k \both \mathit{fun}_{y}(\fn{θ_y}{\mathit{fun}_{z}(\fn{θ_z}{θ_y})}))(...))(...) \label{eq:abs-ex3}
        \Arrow{Unfold $\mathit{fun}$ twice, simplify} \\
  ={} & \mathit{app}(\mathit{app}(\langle [k ↦ \aU], \highlight{\aU} \sumcons \aA \sumcons \aU.. \rangle)(\highlight{ρ_{xk}(x_3)}))(...) \label{eq:abs-ex4}
        \Arrow{Unfold $\mathit{app}$, $ρ_{xk}(x_3)=ρ_{\pe}(x_3)$, simplify} \\
  ={} & \mathit{app}(\langle [k ↦ \aU,x_3↦\aU], \highlight{\aA} \sumcons \aU.. \rangle)(\highlight{ρ_{xk}(x_2)}) \label{eq:abs-ex5}
        \Arrow{Unfold $\mathit{app}$, simplify} \\
  ={} & \langle [k ↦ \aU,x_3↦\aU], \aU.. \rangle
\end{DispWithArrows}
The $\Uses$ component of the absence type returned by the analysis lists
$k$ and $x_3$ as potentially used.
On the other hand, $x_1$ and $x_2$ are inferred absent, \emph{despite} $x_2$
occuring in argument position.
This is thanks to the summary mechanism; we have highlighted the interacting
information in grey.

Let us look at the steps in a bit more detail.
Steps \labelcref{eq:abs-ex1,eq:abs-ex2} extend the environment with
absence types for the let right-hand sides.
For space reasons, we have not simplified the extended environment entries, but
for $x_2$ we would get $x_2 \both \semabs{x_1}_{ρ_{\pe}} = x_2 \both
ρ_\pe(x_1) = \langle [x_1 ↦ \aU, x_2 ↦ \aU], \aU.. \rangle$,
via unfolding the variable case, $\both$ and $ρ_\pe(x_1)$.
The steps up until \labelcref{eq:abs-ex3} are simple to follow, successively exposing
applications of the $\mathit{app}$ and $\mathit{fun}$ helper functions applied
to environment entries for the involved variables.
Step \labelcref{eq:abs-ex3} then evaluates $\mathit{fun}_y(\fn{θ_y}{\mathit{fun}_z(\fn{θ_z}{θ_y})})$, which unfolds
\[
\langle (([y↦\aU])[z↦\aA])[y↦\aA], (([y↦\aU])[z↦\aA])(y) \sumcons [y↦\aU](z) \sumcons \aU.. \rangle
\]
(mind the difference between literal notation $[y ↦ \aU]$ and function update $\wild [ z ↦ \aA]$),
and that simplifies to $\langle [], \aU \sumcons \aA \sumcons \aU.. \rangle$, an
absence type abstracting the expression $\Lam{y}{\Lam{z}{y}}$.
The $\mathit{app}$ steps \labelcref{eq:abs-ex4,eq:abs-ex5} simply zip up
the uses of $ρ_{xk}(x_3)$ and $ρ_{xk}(x_2)$ with the $\Absence$ flags
in the summary $\aU \sumcons \aA \sumcons \aU..$, adding (with join
$⊔$ defined momentarily) the $\Uses$ from $ρ_{xk}(x_3) = \langle [x_3 ↦ \aU], \aU.. \rangle$
but not from $ρ_{xk}(x_2)$, because the first actual argument ($x_3$) is used
whereas the second ($x_2$) is absent.
The join on $\Uses$ follows pointwise from the order $\aA ⊏ \aU$, \ie, $(φ_1
⊔ φ_2)(\px) \triangleq φ_1(\px) ⊔ φ_2(\px)$.
For the final result, these $\Uses$ are combined with the use on $k$ stemming
from the variable lookup in the application head.

%Since $\semabs{\wild}$ computes least fixpoints at recursive let bindings,
%$\AbsTy$ is equipped with a semi-lattice structure, induced by the order $\aA
%⊏ \aU$ on $\Absence$ flags.
%The order on $\Uses$, $φ_1 ⊑ φ_2$, is defined pointwise, and the order on
%$\AbsTy$ is the product order.
%The order on $\Summary$ is non-structural:
%The inequations $\aA.. ⊑ a \sumcons \varsigma ⊑ \aU..$ and the
%product ordering on $a \sumcons \varsigma$ define a smallest preorder,
%and the partial order on $\Summary$ is this preorder modulo the non-syntactic
%equivalences $\aA \sumcons \aA.. \equiv \aA..$, $\aU \sumcons \aU.. \equiv
%\aU..$, with $\aA..$ as the bottom element.

%In general, we can make the following \emph{soundness statement}:
%$\px$ is absent in $\pe$ when $\px \not∈ \semabs{\pe}_{\tr_\pe}$.
%Thus, $\semabs{\wild}$ can be used in a compiler to enable absent code removal.

\subsection{Function Summaries, Compositionality and Modularity}

Let us clarify that by a \emph{summary mechanism}, we mean a mechanism for
approximating the semantics of a function call in terms of the domain of a
static analysis, often yielding a symbolic, finite representation.
In the definition of $\semabs{\wild}$, we took care to explicate the mechanism
via $\mathit{fun}$ and $\mathit{app}$.
The former approximates a functional $(\fn{θ}{...}) : \AbsTy \to \AbsTy$ into
a finite $\AbsTy$, and $\mathit{app}$ encodes the adjoint (``reverse'')
operation.%
\footnote{Proving that $\mathit{fun}$ and $\mathit{app}$ form a Galois connection
is indeed important for a correctness proof and corresponds to a substitution
\Cref{thm:subst-absence}.}

To support efficient separate compilation, a compiler analysis must be
\emph{modular}, and summaries are indispensable to achieving that.
Let us say that our example function $k = (\Lam{y}{\Lam{z}{y}})$ is defined in
module A and there is a use site $(k~x_1~x_2)$ in module B.
Then a \emph{modular analysis} must not reanalyse A.$k$ at its use site in B.
Our analysis $\semabs{\wild}$ facilitates that easily, because it can
serialise the summarised $\AbsTy$ for $k$ into module A's signature file.
Do note that this would not have been possible for the functional
$(\fn{θ_y}{\fn{θ_z}{θ_y}}) : \AbsTy \to \AbsTy \to \AbsTy$ that describes the
inline expansion of $k$.

The same way summaries enable efficient \emph{inter}-module compilation,
they enable efficient \emph{intra}-module compilation for \emph{compositional}
static analyses such as $\semabs{\wild}$.%
\footnote{\citet{Cousot:02} understand modularity as degrees of compositionality.}
Compositionality implies that $\semabs{\Let{f}{\Lam{x}{\pe_{\mathit{big}}}}{f~f~f~f}}$
is a function of $\semabs{\Lam{x}{\pe_{\mathit{big}}}}$, itself a function of
$\semabs{\pe_{\mathit{big}}}$.
In order to satisfy the scalability requirements of a compiler and
guarantee termination of the analysis in the first place, it is
important not to repeat the work of analysing $\semabs{\pe_{\mathit{big}}}$
at every use site of $f$.
Thus, it is necessary to summarise $\semabs{\Lam{x}{\pe_{\mathit{big}}}}$ into
a finite $\AbsTy$, rather than to call the inline expansion
of type $\AbsTy \to \AbsTy$ multiple times.

\sg{We also say the next sentence in Related Work, but it seems a fitting place
to bring the following point. Would you agree? Otherwise we can remove it or
turn it into a footnote.}
While a compositional analysis appears to \emph{need} a summary mechanism,
it is certainly possible to equip a non-compositional, call string-based
analysis such as control-flow analysis with symbolic summaries to enable
modularity, as discussed in \citet[Section 3.8.2 and 11.3.2]{Shivers:91}.

%This summary mechanism is manifest in the $\mathit{fun}$ and $\mathit{app}$
%functions we deliberately extracted out, encoding a contract between function
%definitions and their call sites.
%
%We can give a more formal definition of what a summary mechanism is in terms of
%abstract interpretation~\citep{Cousot:21}:
%In this work, a \emph{function summary} is an approximation to, or abstraction
%of, the function's abstract transformer implied by the considered analysis.
%
%In case of $\semabs{\Lam{\px}{\pe}}$, the implied abstract transformer is the
%function $f^\sharp_{ρ,\pe,\px} \triangleq \fn{θ}{\semabs{\pe}_{ρ[\px ↦
%θ]}}$ passed to $\mathit{fun}_\px$,%
%\footnote{Note that in contrast to let-bound names, the syntactic parameter
%$\px$ is used as a convenient proxy for a De Bruijn level, if you wonder about
%the scoping semantics.}
%which \emph{summarises} (\ie, abstracts)
%$f^\sharp_{ρ,\pe,\px}$ into something finite (\ie, not a function).
%The produced summary is concretised back in $\semabs{\pe~\px}$ through
%$\mathit{app}$ which encodes the adjoint (``reverse'') operation.
%More concretely, $f^\sharp_{ρ,\pe,\px}(θ) ⊑
%\mathit{app}(\mathit{fun}_\px(f^\sharp_{ρ,\pe,\px}))(θ)$ for any choice of
%$ρ$, $\pe$, $\px$ and $θ$, suggesting a Galois connection between abstract
%transformers in $\AbsTy \to \AbsTy$ and $\AbsTy$.%
%\footnote{We will see at the end of \Cref{sec:by-name-soundness} why it is
%important to restrict the Galois connection to syntactic $f^\sharp_{ρ,\pe,\px}$
%and not arbitrary monotone functions in $\AbsTy \to \AbsTy$.}
%
%If we unfold $f^\sharp_{ρ,\pe,\px}$ and refold $\semabs{\wild}$ twice in
%the above statement, we can recognise it as a \emph{substitution lemma},
%so called because the (delayed) substitution carried out when beta reducing
%$(\Lam{\px}{\pe})~\py$ to $\pe[\px:=\py]$ preserves analysis results:%
%\footnote{All proofs can be found in the Appendix; in case of the extended
%version via clickable links.}
%\footnote{An inconsequential observation: The other half of the Galois connection
%proof, $\mathit{fun}_\px \circ \mathit{app} \mathbin{\ddot{⊑}} \mathit{id}$,
%corresponds to eta expansion $\semabs{\Lam{\px}{\pe~\px}}_ρ ⊑
%\semabs{\pe}_ρ$.}

%We conjecture that every substitution lemma has a summary mechanism it proves
%correct; that is why they are capstone lemmas in type system soundness
%proofs~\citep{tapl} and a crucial part in proving $\semabs{\wild}$ correct.

\subsection{Soundness}

It should be clear now that compositional, summary-based compiler analyses offer
significant advantages, yet we lack ergonomic ways to prove them correct, as we
will see next.

Suppose that we were to prove $\semabs{\wild}$ correct.
The following statement will do:

\begin{theoremrep}[Correct absence analysis]
  \label{thm:absence-correct}
  If $\semabs{\pe}_{ρ_\pe} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
  then $\px$ is absent in $\pe$.
\end{theoremrep}
\begin{proof}
  See \hyperlink{proof:absence-correct}{the proof at the end of this Section}.
\end{proof}

What are the main obstacles to prove it?
As the first step, we must define what absence \emph{means}, in a formal sense.
There are many ways to do so, and it is not at all clear which is best.
One plausible definition is in terms of the standard operational semantics in
\Cref{sec:op-sem}:

\begin{definitionrep}[Absence]
  \label{defn:absence}
  A variable $\px$ is \emph{used} in an expression $\pe$
  if and only if there exists a trace
  $(\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],\wild,\wild) \smallstep^* (\py,ρ'[\py↦\pa],\wild,\wild)$
  that is about to evaluate $\px$, \ie, look up its heap entry.
  Otherwise, $\px$ is \emph{absent} in $\pe$.
\end{definitionrep}

\begin{toappendix}
The elaborate setup of this definition ensures that $\pa$, the address that
$\px$ binds, does not alias with anything defined in the initial heap $μ$ and
thus not with anything in $ρ$ or $κ$.
Unsurprisingly, the no-alias property is easily defeated during evaluation, as
soon as $\px$ is passed as an argument, hence $\py$ can be chosen differently to
$\px$ in \Cref{defn:absence}.

It is quite important that this definition is closed under arbitrary evaluation
contexts $(ρ,μ,κ)$, so that absence is compatible with a contextual
equivalence relation such as contextual improvement~\citep{MoranSands:99}.
\end{toappendix}

The Appendix explains why this is a good definition.
Furthermore, we must prove correct the summary mechanism, captured in the
following \emph{substitution lemma}~\citep{tapl}:%
\footnote{This statement amounts to $id ⊑ \mathit{app} \circ \mathit{fun}_x$,
one half of a Galois connection.
The other half $\mathit{fun}_x \circ \mathit{app} ⊑ id$ is eta-expansion
$\semabs{\Lam{\px}{\pe~\px}}_ρ ⊑ \semabs{\pe}_ρ$.}

\begin{toappendix}
Note that for the proofs we assume the recursive let definition
$\semabs{\Let{\px}{\pe_1}{\pe_2}}_ρ = \semabs{\pe_2}_{ρ[\px ↦ \lfp(\fn{θ}{\px \both \semabs{\pe_1}_{ρ[\px↦θ]}})]}$.
The partial order on $\AbsTy$ necessary for computing the least fixpoint $\lfp$
follows structurally from $\aA ⊏ \aU$ (\ie, product order, pointwise order).

\begin{abbreviation}
  The syntax $θ.φ$ for an $\AbsTy$ $θ = \langle φ, \varsigma \rangle$
  returns the $φ$ component of $θ$.
  The syntax $θ.\varsigma$
  returns the $\varsigma$ component of $θ$.
\end{abbreviation}

\begin{definition}[Abstract substitution]
  \label{defn:abs-subst}
  We call $φ[\px \Mapsto φ'] \triangleq φ[\px↦\aA] ⊔ (φ(\px) * φ')$ the
  \emph{abstract substitution} operation on $\Uses$
  and overload this notation for $\AbsTy$, so that
  $(\langle φ, \varsigma \rangle)[\px \Mapsto φ_\py] \triangleq \langle φ[\px \Mapsto φ_\py], \varsigma \rangle$.
\end{definition}

Abstract substitution is useful to give a concise description of the effect of
syntactic substitution:
\begin{lemma}
  \label{thm:abs-syn-subst}
  $\semabs{(\Lam{\px}{\pe})~\py}_ρ = (\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]$.
\end{lemma}

\begin{lemma}
\label{thm:lambda-bound-absent}
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
\label{thm:lambda-commutes}
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
\label{thm:push-app-absence}
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
\label{thm:push-let-absence}
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
\label{thm:subst-absence}
$\semabs{\pe}_{ρ[\px↦ρ(\py)]} ⊑ \semabs{(\Lam{\px}{\pe})~\py}_ρ$.
\end{lemmarep}
\begin{proof}
By induction on $\pe$.
\begin{itemize}
  \item \textbf{Case }$\pz$:
    When $\px \not= \pz$, then $\pz$ is bound outside the lambda and can't
    possibly use $\px$, so $ρ(\pz).φ(\px) = \aA$.
    We have
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{$\px \not= \pz$} \\
    ={} & ρ(\pz)
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]}
        \Arrow{$ρ(\pz).φ(\px) = \aA$} \\
    ={} & (\semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]
        \Arrow{\Cref{thm:abs-syn-subst}} \\
    ={} & \semabs{(\Lam{\px}{\pz})~\py}_ρ
    \end{DispWithArrows*}
    Otherwise, we have $\px = \pz$,
    thus $ρ(\px) = \langle [\px ↦ \aU], \varsigma = \aU.. \rangle$,
    and thus
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{$\px = \pz$} \\
    ={} & ρ(\py)
        \Arrow{$\varsigma ⊑ \aU..$} \\
    ⊑{} & \langle ρ(\py).φ, \aU.. \rangle
        \Arrow{Definition of $\wild[\wild\Mapsto\wild]$} \\
    ={} & (\langle [\px ↦ \aU], \aU.. \rangle)[\px ↦ ρ(\py).φ]
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & (\semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]
        \Arrow{\Cref{thm:abs-syn-subst}} \\
    ={} & \semabs{(\Lam{\px}{\pz})~\py}_ρ
    \end{DispWithArrows*}

  \item \textbf{Case }$\Lam{\pz}{\pe'}$:
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\Lam{\pz}{\pe'}}_{ρ[\px↦ρ(\py)]}
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \mathit{fun}_\pz(\fn{θ_\pz}{\semabs{\pe'}_{ρ[\pz↦θ_\pz, \px↦ρ(\py)]}})
        \Arrow{Induction hypothesis, monotonicity} \\
    ⊑{} & \mathit{fun}_\pz(\fn{θ_\pz}{\semabs{(\Lam{\px}{\pe'})~\py}_{ρ[\pz↦θ_\pz]}})
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{\Lam{\pz}{((\Lam{\px}{\pe'})~\py)}}_ρ
        \Arrow{\Cref{thm:lambda-commutes}} \\
    ={} & \semabs{(\Lam{\px}{\Lam{\pz}{\pe'}})~\py}_ρ
    \end{DispWithArrows*}

  \item \textbf{Case }$\pe'~\pz$:
    When $\px = \pz$:
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pe'~\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \mathit{app}(\semabs{\pe'}_{ρ[\px↦ρ(\py)]})(ρ(\py))
        \Arrow{Induction hypothesis, monotonicity} \\
    ⊑{} & \mathit{app}(\semabs{(\Lam{\px}{\pe'})~\py}_ρ)(ρ(\py))
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{(\Lam{\px}{\pe'})~\py~\py}_ρ
        \Arrow{\Cref{thm:push-app-absence}} \\
    ={} & \semabs{(\Lam{\px}{\pe'~\py})~\py}_ρ
        \Arrow{Compositionality in $(\Lam{\px}{\pe'~\hole})~\py$} \\
    ={} & \semabs{(\Lam{\px}{\pe'~\px})~\py}_ρ
        \Arrow{$\px = \pz$} \\
    ={} & \semabs{(\Lam{\px}{\pe'~\pz})~\py}_ρ
    \end{DispWithArrows*}
    When $\px \not= \pz$:
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pe'~\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \mathit{app}(\semabs{\pe'}_{ρ[\px↦ρ(\py)]})(ρ(\pz))
        \Arrow{Induction hypothesis, monotonicity} \\
    ⊑{} & \mathit{app}(\semabs{(\Lam{\px}{\pe'})~\py}_ρ)(ρ(\pz))
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{(\Lam{\px}{\pe'})~\py~\pz}_ρ
        \Arrow{\Cref{thm:push-app-absence}} \\
    ={} & \semabs{(\Lam{\px}{\pe'~\pz})~\py}_ρ
    \end{DispWithArrows*}

  \item \textbf{Case }$\Let{\pz}{\pe_1}{\pe_2}$:
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\Let{\pz}{\pe_1}{\pe_2}}_{ρ[\px↦ρ(\py)]}
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \semabs{\pe_2}_{ρ[\px↦ρ(\py),\pz↦\lfp(\fn{θ}{\pz \both \semabs{\pe_1}_{ρ[\px↦ρ(\py),\pz ↦ θ]}})]}
        \Arrow{Induction hypothesis, monotonicity} \\
    ⊑{} & \semabs{(\Lam{\px}{\pe_2})~\py}_{ρ[\pz↦\lfp(\fn{θ}{\pz \both \semabs{(\Lam{\px}{\pe_1})~\py}_{ρ[\pz ↦ θ]}})]}
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ
        \Arrow{\Cref{thm:push-let-absence}} \\
    ={} & \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

\begin{toappendix}
Whenever there exists $ρ$ such that $ρ(\px).φ \not⊑ (\semabs{\pe}_ρ).φ$
(recall that $θ.φ$ selects the $\Uses$ in the first field of the pair $θ$),
then also $ρ_\pe(\px).φ \not⊑ \semabs{\pe}_{ρ_\pe}$.
The following lemma captures this intuition:

\begin{lemma}[Diagonal factoring]
\label{thm:diag-fact}
Let $ρ$ and $ρ_Δ$ be two environments such that
$\forall \px.\ ρ(\px).\varsigma = ρ_Δ(\px).\varsigma$.

If $ρ_Δ.φ(\px) ⊑ ρ_Δ.φ(\py)$ if and only if $\px = \py$,
then every instantiation of $\semabs{\pe}$ factors through $\semabs{\pe}_{ρ_Δ}$,
that is,
\[
  \semabs{\pe}_ρ = (\semabs{\pe}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}]
\]
\end{lemma}
\begin{proof}
By induction on $\pe$.
\begin{itemize}
  \item \textbf{Case $\pe = \py$}:
    We assert $\semabs{\py}_ρ = ρ(\py) = ρ_Δ(\py)[\py \Mapsto ρ(\py).φ]$ by simple unfolding.

  \item \textbf{Case $\pe = \pe'~\py$}:
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
          & \semabs{\pe'~\py}_ρ
          \Arrow{Unfold $\semabs{\wild}$} \\
      ={} & \mathit{app}(\semabs{\pe'}_ρ,ρ(\py))
          \Arrow{Induction hypothesis, variable case} \\
      ={} & \mathit{app}((\semabs{\pe'}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}], ρ_Δ(\py)[\many{\px \Mapsto ρ(\px).φ}]).
          \Arrow{$⊔$ and $*$ commute with $\wild[\wild\Mapsto\wild]$} \\
      ={} & \mathit{app}(\semabs{\pe'}_{ρ_Δ},ρ_Δ(\py))[\many{\px \Mapsto ρ(\px).φ}]
          \Arrow{Refold $\semabs{\wild}$} \\
      ={} & (\semabs{\pe'~\py}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}]
    \end{DispWithArrows*}

  \item \textbf{Case $\pe = \Lam{\py}{\pe'}$}:
    Note that $\px \not= \py$ because $\py$ is not free in $\pe$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
          & \semabs{\Lam{\py}{\pe'}}_ρ
          \Arrow{Unfold $\semabs{\wild}$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{\semabs{\pe'}_{ρ[\py↦θ]}})
          \Arrow{Property of $\mathit{lam}_\py$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})})
        \Arrow{Induction hypothesis} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ_Δ}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})[\many{\px \Mapsto ρ(\px).φ}, \py \Mapsto [\py ↦ \aU]]})
          \Arrow{$θ[\py \Mapsto [\py ↦ \aU]] = θ$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ_Δ}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})[\many{\px \Mapsto ρ(\px).φ}]})
          \Arrow{$θ[\py \Mapsto [\py ↦ \aU]] = θ$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ_Δ}[\py↦θ]})[\many{\px \Mapsto ρ(\px).φ}]})
          \Arrow{Property of $\mathit{lam}_\py$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{\semabs{\pe'}_{{ρ_Δ}[\py↦θ]}})[\many{\px \Mapsto ρ(\px).φ}]
          \Arrow{Refold $\semabs{\wild}$} \\
      ={} & (\semabs{\Lam{\py}{\pe'}}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}]
    \end{DispWithArrows*}

  \item \textbf{Case }$\Let{\py}{\pe_1}{\pe_2}$:
    Note that $\px \not= \py$ because $\py$ is not free in $\pe$.
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\Let{\py}{\pe_1}{\pe_2}}_ρ
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \semabs{\pe_2}_{ρ[\py↦\lfp(\fn{θ}{\py \both \semabs{\pe_1}_{ρ[\py ↦ θ]}})]}
        \Arrow{Induction hypothesis} \\
    ={} & \semabs{\pe_2}_{ρ[\py↦\lfp(\fn{θ}{\py \both (\semabs{\pe_1}_{{ρ_Δ}[\py ↦ \langle [\py ↦ \aU], θ.\varsigma \rangle]})[\many{\px \Mapsto ρ(\px).φ}, \py \Mapsto θ.φ]})]}
        \Arrow{Again, backwards} \\
    ={} & \semabs{\pe_2}_{ρ[\py↦\lfp(\fn{θ}{\py \both (\semabs{\pe_1}_{{ρ_Δ}[\py ↦ θ]})[\many{\px \Mapsto ρ(\px).φ}]})]} \\
        & \text{\emph{Similarly for $\pe_2$, handwaving to push out the subst as in \Cref{thm:push-let-absence}}} \\
    ={} & (\semabs{\pe_2}_{ρ_Δ[\py↦\lfp(\fn{θ}{\py \both \semabs{\pe_1}_{{ρ_Δ}[\py ↦ θ]}})]})[\many{\px \Mapsto ρ(\px).φ}]
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & (\semabs{\Let{\py}{\pe_1}{\pe_2}}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}]
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

For the purposes of the preservation proof, we will write $\tr$ with a tilde to
denote that abstract environment of type $\Var \to \AbsTy$, to disambiguate it
from a concrete environment $ρ$ from the LK machine.

We need to presume that every heap entry is annotated with the let-bound
variable from whence it was allocated; otherwise there is no way to map
addresses to syntax.
Hence we will write heap entries as triples $\pa↦(\px,ρ,\pe)$, where
$\px$ is from the unique let binding $\Let{\px}{...}{...}$ in the program
that allocated the heap entry.
This information is born redundant, because $\px$ is the unique variable for
which $\pa = ρ(\px)$, but it becomes non-redudant after heap update potentially
replaces $(ρ,\pe)$ with the value.

\begin{figure}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semabsS{\wild} \colon \States → \AbsTy } } \\
  \\[-0.5em]
  \semabsS{(\pe,ρ,μ,κ)} & {}={} & \mathit{apps}_μ(κ,\semabs{\pe}_{α(μ) \circ ρ}) \\
                   α(μ) & {}={} & \lfp(\fn{\tm}{[ \pa ↦ \px \both \semabs{\pe'}_{\tm \circ ρ'} \mid μ(\pa) = (\px,ρ',\pe') ]}) \\
             \mathit{apps}_μ(\StopF,θ) & {}={} & θ \\
             \mathit{apps}_μ(\ApplyF(\pa) \pushF κ,θ) & {}={} & \mathit{apps}_μ(κ,\mathit{app}(θ,α(μ)(\pa))) \\
             \mathit{apps}_μ(\UpdateF(\pa) \pushF κ,θ) & {}={} & \mathit{apps}_μ(κ,θ)
  \\[-0.5em]
\end{array}\]
\caption{Absence analysis extended to small-step configurations}
  \label{fig:absence-ext}
\end{figure}

In \Cref{fig:absence-ext}, we give the extension of $\semabsS{\wild}$ to whole
machine configurations $σ$.
Although $\semabsS{\wild}$ looks like an entirely new definition, it is
actually derivative of $\semabs{\wild}$ via a context lemma à la
\citet[Lemma 3.2]{MoranSands:99}:
The environments $ρ$ simply govern the transition from syntax to
operational representation in the heap.
The bindings in the heap are to be treated as mutually recursive let bindings,
hence a fixpoint is needed.
For safety properties such as absence, a least fixpoint is appropriate.
Apply frames on the stack correspond to the application case of $\semabs{\wild}$
and invoke the summary mechanism.
Update frames are ignored because our analysis is not heap-sensitive.

Now we can prove that $\semabsS{\wild}$ is preserved/improves during reduction:

\begin{lemma}[Preservation of $\semabsS{\wild}$]
\label{thm:preserve-absent}
If $σ_1 \smallstep σ_2$, then $\semabsS{σ_1} ⊒ \semabsS{σ_2}$.
\end{lemma}
\begin{proof}
By cases on the transition.
\begin{itemize}
  \item \textbf{Case }$\LetIT$: Then $\pe = \Let{\py}{\pe_1}{\pe_2}$ and
    \[
      (\Let{\py}{\pe_1}{\pe_2},ρ,μ,κ) \smallstep (\pe_2,ρ[\py↦\pa],μ[\pa↦(\py,ρ[\py↦\pa],\pe_1)],κ).
    \]
    Abbreviating $ρ_1 \triangleq ρ[\py↦\pa], μ_1 \triangleq μ[\pa ↦ (\py,ρ_1,\pe_1)$, we have
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\Let{\py}{\pe_1}{\pe_2}}_{α(μ) \circ ρ}) \Arrow{Unfold $\semabs{\Let{\py}{\pe_1}{\pe_2}}$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pe_2}_{(α(μ) \circ ρ)[\py↦\py \both \lfp(\fn{θ}{\semabs{\pe_1}_{(α(μ) \circ ρ)[\py↦θ]}})]}) \Arrow{Move fixpoint outwards, refold $α$} \\
      {}={}& \mathit{apps}_{μ_1}(κ)(\semabs{\pe_2}_{α(μ_1) \circ ρ_1}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\AppIT$:
    Then $(\pe'~\py,ρ,μ,κ) \smallstep (\pe',ρ,μ,\ApplyF(ρ(\py)) \pushF κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pe'~\py}_{α(μ) \circ ρ}) \Arrow{Unfold $\semabs{\pe'~\py}_{(α(μ) \circ ρ)}$} \\
      {}={}& \mathit{apps}_μ(κ)(\mathit{app}(\semabs{\pe'}_{α(μ) \circ ρ}, α(μ)(ρ(\py)))) \Arrow{Rearrange} \\
      {}={}& \mathit{apps}_μ(\ApplyF(ρ(\py)) \pushF κ)(\semabs{\pe'}_{α(μ) \circ ρ}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\AppET$:
    Then $(\Lam{\py}{\pe'},ρ,μ,\ApplyF(\pa) \pushF κ) \smallstep (\pe',ρ[\py↦\pa],μ,κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(\ApplyF(\pa) \pushF κ)(\semabs{\Lam{\py}{\pe'}}_{α(μ) \circ ρ}) \Arrow{Unfold $\mathit{apps}$} \\
      {}={}& \mathit{apps}_μ(κ)(\mathit{app}(\semabs{\Lam{\py}{\pe'}}_{α(μ) \circ ρ}, α(μ)(\pa))) \Arrow{Unfold RHS of \Cref{thm:subst-absence}} \\
      {}⊒{}& \mathit{apps}_μ(κ)(\semabs{\pe'}_{(α(μ) \circ ρ)[\py↦α(μ)(\pa)]}) \Arrow{Rearrange} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pe'}_{(α(μ) \circ ρ[\py↦\pa])}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\LookupT$:
    Then $\pe = \py$, $\pa \triangleq ρ(\py)$, $(\pz,ρ',\pe') \triangleq μ(\pa)$ and
    $(\py,ρ,μ,κ) \smallstep (\pe',ρ',μ,\UpdateF(\pa) \pushF κ)$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\py}_{α(μ) \circ ρ}) \Arrow{Unfold $\semabs{\py}$} \\
      {}={}& \mathit{apps}_μ(κ)((α(μ) \circ ρ)(\py)) \Arrow{Unfold $α$} \\
      {}={}& \mathit{apps}_μ(κ)(\pz \both \semabs{\pe'}_{α(μ) \circ ρ'}) \Arrow{Drop $[\pz↦\aU]$} \\
      {}⊒{}& \mathit{apps}_μ(κ)(\semabs{\pe'}_{α(μ) \circ ρ'}) \Arrow{Definition of $\mathit{apps}_μ$} \\
      {}={}& \mathit{apps}_μ(\UpdateF(\pa) \pushF κ)(\semabs{\pe'}_{α(μ) \circ ρ'}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\UpdateT$:
    Then $(\pv, ρ, μ[\pa↦(\py,ρ',\pe')], \UpdateF(\pa) \pushF κ) \smallstep (\pv,ρ,μ[\pa↦(\py,ρ,\pv)],κ)$.

    This case is a bit hand-wavy and shows how heap update during by-need
    evaluation is dreadfully complicated to handle, even though
    $\semabs{\wild}$ is heap-less and otherwise correct \wrt by-name
    evaluation.
    The culprit is that in order to show $\semabsS{σ_2} ⊑ \semabsS{σ_1}$, we
    have to show
    \begin{equation}
      \semabs{\pv}_{α(μ) \circ ρ} ⊑ \semabs{\pe'}_{α(μ') \circ ρ'}. \label{eqn:absent-upd}
    \end{equation}

    Intuitively, this is somewhat clear, because $μ$ ``evaluates to'' $μ'$ and
    $\pv$ is the value of $\pe'$, in the sense that there exists
    $σ'=(\pe',ρ',μ',κ)$ such that $σ' \smallstep^* σ_1 \smallstep σ_2$.

    Alas, who guarantees that such a $σ'$ actually exists?
    We would need to rearrange the lemma for that and argue by step indexing
    (a.k.a. coinduction) over prefixes of \emph{maximal traces} (to be
    rigorously defined later).
    That is, we presume that the statement
    \[
      \forall n.\ σ_0 \smallstep^n σ_2 \Longrightarrow \semabsS{σ_2} ⊑ \semabsS{σ_0}
    \]
    has been proved for all $n < k$ and proceed to prove it for $n = k$.
    So we presume $σ_0 \smallstep^{k-1} σ_1 \smallstep σ_2$ and $\semabsS{σ_1} ⊑ \semabsS{σ_0}$
    to arrive at a similar setup as before, only with a stronger assumption
    about $σ_1$.
    Specifically, due to the balanced stack discipline we know that
    $σ_0 \smallstep^{k-1} σ_1$ factors over $σ'$ above.
    We may proceed by induction over the balanced stack discipline (we will see
    in \Cref{sec:adequacy} that this amounts to induction over the big-step
    derivation) of the trace $σ' \smallstep^* σ_1$ to show \Cref{eqn:absent-upd}.

    This reasoning was not specific to $\semabs{\wild}$ at all.
    We will show a more general result in Lemma \labelcref{thm:memo-improves}
    that can be reused across many more analyses.

    Assuming \Cref{eqn:absent-upd} has been proved, we proceed
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(\UpdateF(\pa) \pushF κ)(\semabs{\pv}_{α(μ) \circ ρ}) \Arrow{Definition of $\mathit{apps}_μ$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pv}_{α(μ) \circ ρ}) \Arrow{Above argument that $\semabs{\pv}_{α(μ) \circ ρ} ⊑ \semabs{\pe'}_{α(μ') \circ ρ'}$} \\
      {}⊒{}& \mathit{apps}_{μ[\pa↦(\py,ρ,\pv)]}(κ)(\semabs{\pv}_{α(μ[\pa↦(\py,ρ,\pv)]) \circ ρ}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

\noindent
We conclude with the \hypertarget{proof:absence-correct}{proof} for \Cref{thm:absence-correct}:
\begin{proof}
We show the contraposition, that is,
if $\px$ is used in $\pe$, then $φ(\px) = \aU$.

Since $\px$ is used in $\pe$, there exists a trace
\[
  (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],μ[\pa↦(\px,ρ[\px↦\pa],\pe')],κ) \smallstep^* (\py,ρ'[\py↦\pa],μ',κ').
\]
Let us abbreviate $ρ_1 \triangleq ρ[\px↦\pa]$, $μ_1 \triangleq μ[\pa↦(\px,ρ[\px↦\pa],\pe')]$.
Without loss of generality, we assume the trace prefix ends at the first lookup
at $\pa$, so $μ'(\pa) = μ_1(\pa) = (\px, ρ_1,\pe')$.
If that was not the case, we could just find a smaller prefix with this property.

Let us abbreviate $\tr \triangleq (α(μ_1) \circ ρ_1)$.
Under the above assumptions, $\tr(\py).φ(\px) = \aU$ implies $\px = \py$ for all
$\py$, because $μ_1(\pa)$ is the only heap entry in which $\px$ occurs by our
shadowing assumptions on syntax.
By unfolding $\semabsS{\wild}$ and $\semabs{\py}$ we can see that
\[
  [\px ↦ \aU] ⊑ α(μ_1)(\pa).φ = α(μ')(\pa).φ = \semabs{\py}_{α(μ') \circ ρ'[\py↦\pa]}.φ ⊑ (\semabsS{(\py,ρ'[\py↦\pa],μ',κ')}).φ.
\]
By \Cref{thm:preserve-absent}, we also have
\[
  (\semabsS{(\py,ρ'[\py↦\pa],μ',κ')}).φ ⊑ (\semabsS{(\pe,ρ_1,μ_1,κ)}).φ.
\]
And with transitivity, we get $[\px ↦ \aU] ⊑ (\semabsS{(\pe,ρ_1,μ_1,κ)}).φ$.
Since there was no other heap entry for $\px$ and $\pa$ cannot occur in $κ$ or
$ρ$ due to well-addressedness, we have $[\px ↦ \aU] ⊑ (\semabsS{(\pe,ρ_1,μ_1,κ)}).φ$ if
and only if $[\px ↦ \aU] ⊑ (\semabs{\pe}_{\tr}).φ$.
With \Cref{thm:diag-fact}, we can decompose
\begin{DispWithArrows*}[fleqn,mathindent=1em]
       & [\px ↦ \aU] \Arrow{Above result} \\
  {}⊑{}& (\semabs{\pe}_{\tr}).φ \Arrow{$\tr_Δ(\px) \triangleq \langle [\px ↦ \aU], \tr(\px).\varsigma \rangle$, \Cref{thm:diag-fact}} \\
  {}={}& ((\semabs{\pe}_{\tr_Δ})[\many{\py \Mapsto \tr(\py).φ}]).φ \Arrow{$\varsigma ⊑ \aU..$, hence $\tr_Δ ⊑ \tr_\pe$} \\
  {}⊑{}& ((\semabs{\pe}_{\tr_\pe})[\many{\py \Mapsto \tr(\py).φ}]).φ \Arrow{Definition of $\wild[\wild \Mapsto \wild]$} \\
  {}={}& \Lub \{ \tr(\py).φ \mid \semabs{\pe}_{\tr_\pe}.φ(\py) = \aU \}
\end{DispWithArrows*}
But since $\tr(\py).φ(\px) = \aU$ implies $\px = \py$ (refer to definition of
$\tr$), we must have $(\semabs{\pe}_{\tr_\pe}).φ(\px) = \aU$, as required.
\end{proof}
\end{toappendix}

Now we may finally attempt the proof for \Cref{thm:absence-correct}.
We suggest for the reader to have a cursory look by clicking on the theorem
number, linking to the Appendix.
The proof is exemplary of even more ambitious proofs such as in
\citet{Sergey:14} and \citet[Section 4]{Breitner:16}.
Though seemingly disparate, these proofs all follow an established
preservation-style proof technique at heart.%
\footnote{A ``mundane approach`` according to \citet[Section
4.1]{Nielson:99}, applicable to \emph{trace properties}, but not to
\emph{hyperproperties}~\citep{ClarksonSchneider:10}.}
The proof of \citet{Sergey:14} for a generalisation of $\semabs{\wild}$
is roughly structured as follows (non-clickable references to Figures
and Lemmas below reference \citet{Sergey:14}):

\begin{enumerate}
  \item Instrument a standard call-by-need semantics (a variant of our reference
    in \Cref{sec:op-sem}) such that heap lookups decrement a per-address
    counter; when heap lookup is attempted and the counter is 0, the machine is stuck.
    In \Cref{defn:absence}, no instrumentation is needed because absence is rather simple.
  \item Give a declarative type system that characterises the results of the
    analysis (\ie, $\semabs{\wild}$) in a lenient (upwards closed) way, a unary
    \emph{logical relation}~\citep{Nielson:99}.
    In case of \Cref{thm:absence-correct}, we define an analysis function on
    machine configurations for the proof.
  \item Prove that evaluation of well-typed terms in the instrumented
    semantics is bisimilar to evaluation of the term in the standard semantics,
    \ie, does not get stuck when the standard semantics would not.
    In our case, we prove that evaluation preserves the analysis result.
\end{enumerate}
Alas, the effort in comprehending such a proof in detail, let alone formulating
it, is enormous.
\begin{itemize}
  \item
    The instrumentation (1) is non-trivial; for example the semantics becomes
    non-deterministic.
    Does this instrumentation still express the desired semantic property?
  \item Step (2) all but duplicates a complicated analysis
    definition (\ie, $\semabs{\wild}$) into a type system (in Figure 7) with
    subtle adjustments expressing invariants for the preservation proof.
  \item
    Furthermore, step (2) extends this type system to small-step machine
    configurations (in Figure 13), \ie, stacks and heaps, the scoping of which
    is mutually recursive.%
    \footnote{We believe that this extension can always be derived systematically from a
    context lemma~\citep[Lemma 3.2]{MoranSands:99} and imitating what the type
    system does on the closed expression derivable from a configuration via the
    context lemma.}
    Another page worth of Figures; the amount of duplicated proof artifacts is
    staggering.
    In our case, the analysis function on machine configurations is about as
    long as on expressions.
  \item
    This is all setup before step (3) proves interesting properties about the
    semantic domain of the analysis.
    Among the more interesting properties is the \emph{substitution lemma} A.8
    to be applied during beta reduction; exactly as in our proof.
  \item
    While proving that a single step $σ_1 \smallstep σ_2$ preserves analysis
    information in step (3), we noticed that we actually got stuck in the $\UpdateT$
    case, and would need to redo the proof using step-indexing~\citep{AppelMcAllester:01}.
    In our experience this case hides the thorniest of surprises; that was
    our experience while proving \Cref{thm:soundness-by-need} which gives a
    proper account.

    Although the proof in \citet{Sergey:14} is perceived as detailed and
    rigorous, it is quite terse in the corresponding \textsc{EUpd} case of the
    single-step safety proof in lemma A.6.
\end{itemize}


The main takeaway:
Although analysis and semantics might be reasonably simple, the correctness
proof that relates both is \emph{not}; it necessitates an explosion in formal
artefacts and the parts of the proof that concern the domain of the analysis are
drowned in coping with semantic subtleties that ultimately could be shared with
similar analyses.
Furthermore, the inevitable hand-waving in proofs of this size around said
semantic subtleties diminishes confidence in the correctness of the proof
to the point where trust can only be recovered by full mechanisation.

It would be preferable to find a framework to \emph{prove these distractions
rigorously and separately}, once and for all, and then instantiate this
framework for absence analysis or cardinality analysis, so that only the
highlights of the preservation proof such as the substitution lemma need to be
shown.

Abstract interpretation provides such a framework.
Alas, the book of \citet{Cousot:21} starts from a \emph{compositional} semantics
to derive compositional analyses, but small-step operational semantics are
non-compositional!
This begs the question if we could have started from a compositional
denotational semantics.
While we could have done so for absence or strictness analysis, denotational
semantics is insufficient to express \emph{operational properties} such as
\emph{usage cardinality}, \ie, ``$\pe$ evaluates $\px$ at most $u$ times'',
but usage cardinality is the entire point of the analysis in \citet{Sergey:14}.%
\footnote{Useful applications of the ``at most once'' cardinality are given in
\citet{Turner:95,Sergey:14}, motivating inlining into function bodies that are
called at most once, for example.}

For these reasons, we set out to find a \textbf{\emph{compositional semantics
that exhibits operational detail}} just like the trace-generating semantics of
\citet{Cousot:21}, and were successful.
The example of usage analysis in \Cref{sec:abstraction} (generalising
$\semabs{\wild}$, as suggested above) demonstrates that we can
\textbf{\emph{derive summary-based analyses as an abstract interpretation}} from
our semantics.
Since both semantics and analysis are derived from the same compositional
generic interpreter, the correctness proof for usage analysis in
\Cref{thm:usage-correct} takes no more than a substitution lemma and a bit of
plumbing.
Hence our \emph{Denotational Interpreter} does not only enjoy useful
compositional semantics and analyses as instances, the soundness proofs become
compositional as well, building on reusable evaluation-order-specific theorems
such as \Cref{thm:soundness-by-name}.
