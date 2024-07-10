%if style == newcode
%include custom.fmt
> module Problem where
%endif

\section{The Problem We Solve}
\label{sec:problem}

What is so difficult about proving a compositional, summary-based analysis sound
\wrt a non-compositional small-step operational semantics?
We will demonstrate the challenges in this section, by way of a simplified \emph{absence
analysis}~\citep{SPJ:94}, a higher-order form of neededness analysis to inform
removal of dead code in a compiler.

\subsection{Object Language}
\label{sec:lang}

To set the stage, we start by defining the object language of this work, an
untyped lambda calculus with \emph{\textbf{recursive}} let bindings and
algebraic data types:
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
Note that $\Lam{x}{x}$ (with an overline) denotes syntax, whereas $\fn{x}{x+1}$
denotes an anonymous mathematical function.
In this section, only the highlighted parts are relevant and $\mathbf{let}$ is
considered non-recursive, but the interpreter definition in \Cref{sec:interp}
supports data types and recursive $\mathbf{let}$ as well.
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
    \multicolumn{3}{c}{\qquad\qquad\text{where } \langle φ, \varsigma \rangle = f(\langle [\px↦\aU], \repU \rangle)} \\
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
    \varsigma & {}∈{}    & \Summary & {}::={} & a \sumcons \varsigma \mid \rep{a} \\
    θ & {}∈{} & \AbsTy   & {}::={} & \langle φ, \varsigma \rangle \\
    \\[-0.9em]
    \multicolumn{5}{c}{\rep{a} \equiv a \sumcons \rep{a}} \\
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

In order to define and explore absence analysis in this subsection, we must
clarify what absence means, semantically.
A variable $\px$ is \emph{absent} in an expression $\pe$ when
$\pe$ never evaluates $\px$, regardless of the context in which $\pe$
appears.
Otherwise, the variable $\px$ is \emph{used} in $\pe$.
%SG: Note the emphasis on context; indeed, absent means absent in all contexts,
%not just in a WHNF evaluation of $\pe$.

\Cref{fig:absence} defines an absence analysis $\semabs{\pe}_ρ$ for lazy
program semantics that conservatively approximates semantic absence.
For illustrative purposes, our analysis definition only works for
the special case of non-recursive $\mathbf{let}$, but later sections will assume
recursive let semantics.%
\footnote{Given an order that we will define in due course, the
generalised definition for recursive as well as non-recursive let is
$\semabs{\Let{\px}{\pe_1}{\pe_2}}_ρ = \semabs{\pe_2}_{ρ[\px ↦
\lfp(\fn{θ}{\px \both \semabs{\pe_1}_{ρ[\px↦θ]}})]}$.}
It takes an environment $ρ \in \Var \pfun \AbsTy$ containing absence
information about the free variables of $\pe$ and returns
an \emph{absence type} $\langle φ, \varsigma \rangle \in \AbsTy$; an abstract
representation of $\pe$.
The first component $φ \in \Uses$ of the absence type captures how $\pe$ uses its free
variables by associating an $\Absence$ flag with each variable.
When $φ(\px) = \aA$, then $\px$ is absent in $\pe$; otherwise, $φ(\px) = \aU$
and $\px$ might be used in $\pe$.
The second component $\varsigma \in \Summary$ of the absence type summarises how $\pe$ uses
actual arguments supplied at application sites.
For example, function $f \triangleq \Lam{x}{y}$ has absence type $\langle [y ↦ \aU], \aA \sumcons \repU \rangle$.
Mapping $[y ↦ \aU]$ indicates that $f$ may use its free variable $y$.
The literal notation $[y ↦ \aU]$ maps any variable other than $y$ to $\aA$.
Furthermore, summary $\aA \sumcons \repU$ indicates that $f$'s first argument is absent and all further arguments are potentially used.
The summary $\repU$ denotes an infinite repetition of $\aU$, as expressed by the
non-syntactic equality $\repU \equiv \aU \sumcons \repU$.

% \sven{You don't need to convince readers that the absence analysis is meaningful. Better focus on giving an example of summeries.}
% Clearly if $\px$ is not free in $\pe$, then $\px$ is absent in $\pe$, but our
% analysis does a bit better:
% Consider the expression $\pe \triangleq \Let{f}{\Lam{x}{y}}{f~v}$.
% Here, $v$ is a free variable of $\pe$, but it is absent because $f$ discards it.
% The analysis figures out the same, by recording a summary $\varsigma$ in the
% absence type for $f$ stored in the environment $ρ$.
% The summary $\varsigma = \aA \sumcons \repU$ indicates
% that $f$ is absent in its first argument \sven{This sounds weird. Perhaps: "$f$'s first argument $x$ is absent"} but potentially uses any further arguments\sven{What does this mean? Looks like $f$ only has one argument: $x$}.
% The summary $\repU$ can be thought of as a finite representation of an infinite
% list of $\aU$, as expressed by the non-syntactic equality $\aU \equiv \aU
% \sumcons \repU$, and likewise for $\repA \equiv \aA \sumcons \repA$.
% Since $f$ also uses $y$, the absence type recorded in the environment at the
% call site of $f$ looks like $ρ(f) = \langle [f ↦ \aU, y ↦ \aU], \aA
% \sumcons aU.. \rangle$, indicating that the call $f~v$ uses the free variables
% $f$ and $y$, \emph{but not} $v$.
% (Note that the literal notation $[f ↦ \aU, y ↦ \aU] ∈ \Uses$ maps any
% variable other than $f$ and $y$ to $\aA$.)

%When $\semabs{\pe}_{ρ_{\pe}} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
%then $\px$ is absent in $\pe$, where $ρ_{\pe}$ is the free variable environment
%defined as
%\[
%  ρ_{\pe}(\px) \triangleq \langle [\px ↦ \aU], \repU \rangle, \quad \text{(if $\px ∈ \fv(\pe)$)}.
%\]

%In a slight extension of function update syntax, $[\px ↦ \aU]$ denotes a $φ$
%where $φ(\px) = \aU$ and $φ(\py) = \aA$ for $\px \not= \py$.
%Now we can understand $ρ_{\pe}$ to say that evaluation of each free variable
%$\px$ uses only $\px$, and that any actual argument it is applied to is used,
%indicated by argument summary $\repU$\ .

We illustrate the analysis at the example expression
$\pe \triangleq \Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2}$, where the initial
environment for $\pe$, $ρ_\pe(\px) \triangleq \langle [\px ↦ \aU], \repU \rangle$,
declares the free variables of $\pe$ with a pessimistic summary $\repU$.
\begin{DispWithArrows}[fleqn,mathindent=0em]
      & \semabs{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_1~x_2}}_{ρ_{\pe}} \label{eq:abs-ex-let}
        \Arrow{Unfold $\semabs{\Let{\px}{\pe_1}{\pe_2}}$. NB: Lazy Let!} \\
  ={} & \semabs{k~x_1~x_2}_{ρ_\pe[k↦k \both \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_\pe}]}
        \Arrow{Unf. $\semabs{\wild}$, $ρ_1 \triangleq ρ_\pe[k↦k \! \both \! \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_\pe}]$} \\
  ={} & \mathit{app}(\mathit{app}(ρ_1(k))(ρ_1(x_1)))(ρ_1(x_2))
        \Arrow{Unfold $ρ_1(k)$} \\
  ={} & \mathit{app}(\mathit{app}(k \both \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_1})(ρ_1(x_1)))(ρ_1(x_2))
        \Arrow{Unfold $\semabs{\Lam{\px}{\pe}}$ twice, $\semabs{\px}$} \\
  ={} & \mathit{app}(\mathit{app}(k \both \mathit{fun}_{y}(\fn{θ_y}{\mathit{fun}_{z}(\fn{θ_z}{θ_y})}))(...))(...) \label{eq:abs-ex-summarise}
        \Arrow{Unfold $\mathit{fun}$ twice, simplify} \\
  ={} & \mathit{app}(\mathit{app}(\langle [k ↦ \aU], \highlight{\aU} \sumcons \aA \sumcons \repU \rangle)(\highlight{ρ_1(x_1)}))(...) \label{eq:abs-apply1}
        \Arrow{Unfold $\mathit{app}$, $ρ_1(x_1)=ρ_{\pe}(x_1)$, simplify} \\
  ={} & \mathit{app}(\langle [k ↦ \aU,x_1↦\aU], \highlight{\aA} \sumcons \repU \rangle)(\highlight{ρ_1(x_2)}) \label{eq:abs-apply2}
        \Arrow{Unfold $\mathit{app}$, simplify} \\
  ={} & \langle [k ↦ \aU,x_1↦\aU], \repU \rangle
\end{DispWithArrows}
Let us look at the steps in a bit more detail.
Step \labelcref{eq:abs-ex-let} extends the environment with
an absence type for the let right-hand side of $k$.
The steps up until \labelcref{eq:abs-ex-summarise} successively expose
applications of the $\mathit{app}$ and $\mathit{fun}$ helper functions applied
to environment entries for the involved variables.
Step \labelcref{eq:abs-ex-summarise} then computes the summary as part of the absence type
$\mathit{fun}_y(\fn{θ_y}{\mathit{fun}_z(\fn{θ_z}{θ_y})}) = \langle [], \aU \sumcons \aA \sumcons \repU \rangle$.
The $\Uses$ component is empty because $\Lam{y}{\Lam{z}{y}}$ has no free variables,
and $k \both ...$ will add $[k↦\aU]$ as the single use.
The $\mathit{app}$ steps \labelcref{eq:abs-apply1,eq:abs-apply2} simply zip up
the uses of arguments $ρ_1(x_1)$ and $ρ_1(x_2)$ with the $\Absence$ flags
in the summary $\aU \sumcons \aA \sumcons \repU$ as highlighted, adding the
$\Uses$ from $ρ_1(x_1) = \langle [x_1 ↦ \aU], \repU \rangle$ but \emph{not}
from $ρ_1(x_2)$, because the first actual argument ($x_1$) is used whereas the
second ($x_2$) is absent.
The join on $\Uses$ follows pointwise from the order $\aA ⊏ \aU$, \ie $(φ_1
⊔ φ_2)(\px) \triangleq φ_1(\px) ⊔ φ_2(\px)$.

The analysis result $[k ↦ \aU,x_1↦\aU]$ infers $k$ and $x_1$ as
potentially used and $x_2$ as absent, despite it occurring in argument position,
thanks to the summary mechanism.

%Since $\semabs{\wild}$ computes least fixpoints at recursive let bindings,
%$\AbsTy$ is equipped with a semi-lattice structure, induced by the order $\aA
%⊏ \aU$ on $\Absence$ flags.
%The order on $\Uses$, $φ_1 ⊑ φ_2$, is defined pointwise, and the order on
%$\AbsTy$ is the product order.
%The order on $\Summary$ is non-structural:
%The inequations $\repA ⊑ a \sumcons \varsigma ⊑ \repU$ and the
%product ordering on $a \sumcons \varsigma$ define a smallest preorder,
%and the partial order on $\Summary$ is this preorder modulo the non-syntactic
%equivalences $\aA \sumcons \repA \equiv \repA$, $\aU \sumcons \repU \equiv
%\repU$, with $\repA$ as the bottom element.

%In general, we can make the following \emph{soundness statement}:
%$\px$ is absent in $\pe$ when $\px \not∈ \semabs{\pe}_{\tr_\pe}$.
%Thus, $\semabs{\wild}$ can be used in a compiler to enable absent code removal.

\subsection{Function Summaries, Compositionality and Modularity}
\label{sec:summaries}

%\sven{I don't understand the purpose of this section. This section motivates why summery-based analyses are useful, but this doesn't motivate the problem we are solving. The problem we solve is to prove summary-based analyses sound illustrated in Section 2.4. I would drop this section entirely.}
%
%\sg{Section 2 is about substantiating the claim in the Introduction that we
%have two established alternatives that are \emph{unappealing}:
%Alt (1): Proof despite structural mismatch. Implies complicated proofs. The bulk
%of this section is about substantiating this claim.
%Alt (2): Reformulate the analysis in terms of AAM/CFA. But then we give up on
%summaries and lose modularity. That's what I want to substantiate in this subsection.
%So I added the following paragraph.
%Perhaps I should move this entire subsection to Related Work and point to that at the end of 2.2?}


Instead of coming up with a summary mechanism, we could simply have ``inlined''
$k$ during analysis of the example above to see that $x_2$ is absent in a simple
first-order sense.
The \emph{call strings} approach to interprocedural program
analysis~\citep{SharirPnueli:78} turns this idea into a static analysis,
and the AAM recipe could be used to derive an absence analysis based on call
strings that is sound by construction.
In this subsection, we argue that following this paths gives up on modularity,
and thus leads to scalability problems in a compiler.

Let us clarify that by a \emph{summary mechanism}, we mean a mechanism for
approximating the semantics of a function call in terms of the domain of a
static analysis, often yielding a symbolic, finite representation.
In the definition of $\semabs{\wild}$, we took care to explicate the mechanism
via $\mathit{fun}$ and $\mathit{app}$.
The former approximates a functional $(\fn{θ}{...}) : \AbsTy \to \AbsTy$ into
a finite $\AbsTy$, and $\mathit{app}$ encodes the adjoint (``reverse'')
operation.%
%\footnote{Proving that $\mathit{fun}$ and $\mathit{app}$ form a Galois connection
%is indeed important for a soundness proof and corresponds to a substitution
%\Cref{thm:absence-subst}.}

To support efficient separate compilation, a compiler analysis must be
\emph{modular}, and summaries are indispensable in achieving that.
Let us say that our example function $k = (\Lam{y}{\Lam{z}{y}})$ is defined in
module A and there is a use site $(k~x_1~x_2)$ in module B.
Then a \emph{modular analysis} must not reanalyse A.$k$ at its use site in B.
Our analysis $\semabs{\wild}$ facilitates that easily, because it can
serialise the summarised $\AbsTy$ for $k$ into module A's signature file.
Do note that this would not have been possible for the functional
$(\fn{θ_y}{\fn{θ_z}{θ_y}}) : \AbsTy \to \AbsTy \to \AbsTy$ that describes the
inline expansion of $k$, which a call-strings-based absence analysis would need
to invoke at every use site.

The same way summaries enable efficient \emph{inter}-module compilation,
they enable efficient \emph{intra}-module compilation for \emph{compositional}
static analyses such as $\semabs{\wild}$.
%\footnote{\citet{Cousot:02} understand modularity as degrees of compositionality;
%a compositional analysis is thus modular.}
Compositionality implies that $\semabs{\Let{f}{\Lam{x}{\pe_{\mathit{big}}}}{f~f~f~f}}$
is a function of $\semabs{\Lam{x}{\pe_{\mathit{big}}}}$, and the summary mechanism
prevents having to reanalyse $\pe_{\mathit{big}}$ repeatedly for each call of $f$.
%In order to satisfy the scalability requirements of a compiler and
%guarantee termination of the analysis in the first place, it is
%important not to repeat the work of analysing $\semabs{\pe_{\mathit{big}}}$
%at every use site of $f$.
%Thus, it is necessary to summarise $\semabs{\Lam{x}{\pe_{\mathit{big}}}}$ into
%a finite $\AbsTy$, rather than to call the inline expansion
%of type $\AbsTy \to \AbsTy$ multiple times, ruling out an analysis that is
%purely based on call strings.

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
%which \emph{summarises} (\ie abstracts)
%$f^\sharp_{ρ,\pe,\px}$ into something finite (\ie not a function).
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

\subsection{Problem: Proving Soundness of Summary-Based Analyses}

In this subsection, we demonstrate the difficulty of proving summary-based
analyses sound.

%\sven{The storyline can be streamlined. Right now the story is:
%\begin{itemize}
%\item To prove the absence analysis sound, we need to show Theorem 1.
%\item Why is it difficult to prove?
%\item But before we explain the difficulty, we must first define absence in Definition 2.
%\item Furthermore, before we explain the difficulty, we must also prove substitution in Lemma 3.
%\item Now we look at some existing proofs of such analyses and why they are difficult...
%\end{itemize}
%I propose the following storyline:
%\begin{itemize}
%\item To prove the absence analysis sound, we need to show Theorem 1.
%\item Theorem 1 (Combine theorem 1 and definition 2):
%  If $\semabs{\pe}_{ρ_\pe} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$, implies $\px$ is absent in $\pe$.
%  $\px$ is absent in $\pe$ if there exists no trace ... that evaluates $\px$.
%\item The proof is in the appendix. The proof is exemplary for more ambitious proofs such as ...
%\item Here are the reasons why such proofs are difficult (1) ... (2) ... (3) ...
%\end{itemize}
%In the last point you can incorporate the substitution lemma and why it is difficult}
%
%\sg{We refer to Def 2 and Lemma 3 later on; they are a recurring scheme.
%Lemma 3 is not too difficult to prove and always necessary for a summary-based analysis.
%I tried to leave some forward references to clarify.}

\begin{theoremrep}[$\semabs{\wild}$ infers absence]
  \label{thm:absence-correct}
%  \sven{There must be "soundness" somewhere in the title}
%  \sg{The problem is that there is not a single notion of "soundness".
%  Later chapters silently assume that the analysis is sound if $α (\denot{\pe}) ⊑ \semabs{\pe}$.
%  But absence is stronger than that!
%  Absence means that $α (\denot{\pE[\pe]}) ⊑ \semabs{\pe}$ for every
%  evaluation context $\pE$ (corresponding to machine triples $(ρ,μ,κ)$), so
%  that we may do dead code elimination anywhere in the program.
%  That is a subtle point that I don't want to expand on here;
%  it is distracting for newcomers and somewhat obvious to experts of modular
%  analyses and program transformations.}
  If $\semabs{\pe}_{ρ_\pe} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
  then $\px$ is absent in $\pe$.
\end{theoremrep}
\begin{proof}
  See \hyperlink{proof:absence-correct}{the proof at the end of this section}.
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
  $(\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep^* ... \smallstep[\LookupT(\px)] ...$
  that looks up the heap entry of $\px$, \ie it evaluates $\px$.
  Otherwise, $\px$ is \emph{absent} in $\pe$.
\end{definitionrep}

Note that absence is a property of many different traces, each embedding the
expression $\pe$ in different machine contexts so as to justify rewrites via
contextual improvement~\citep{MoranSands:99}.
Furthermore, we must prove sound the summary mechanism, captured in the
following \emph{substitution lemma}~\citep{tapl}:%
%\footnote{This statement amounts to $id ⊑ \mathit{app} \circ \mathit{fun}_x$,
%one half of a Galois connection.
%The other half $\mathit{fun}_x \circ \mathit{app} ⊑ id$ is eta-expansion
%$\semabs{\Lam{\px}{\pe~\px}}_ρ ⊑ \semabs{\pe}_ρ$.}

\begin{toappendix}
Note that for the proofs we assume the recursive let definition
\[
  \semabs{\Let{\px}{\pe_1}{\pe_2}}_ρ = \semabs{\pe_2}_{ρ[\px ↦ \lfp(\fn{θ}{\px \both \semabs{\pe_1}_{ρ[\px↦θ]}})]}.
\]
The partial order on $\AbsTy$ necessary for computing the least fixpoint $\lfp$
follows structurally from $\aA ⊏ \aU$ (\ie product order, pointwise order).

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
  $\semabs{(\Lam{\px}{\pe})~\py}_ρ = (\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \repU \rangle]})[\px \Mapsto ρ(\py).φ]$.
\end{lemma}
\begin{proof}
Follows by unfolding the application and lambda case and then refolding abstract substitution.
\end{proof}

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
\label{thm:lambda-commutes-absence}
$\semabs{(\Lam{\px}{\Lam{\py}{\pe}})~\pz}_ρ = \semabs{\Lam{\py}{((\Lam{\px}{\pe})~\pz)}}_ρ$.
\end{lemma}
\begin{proof}
\begin{DispWithArrows*}[fleqn,mathindent=0em]
      & \semabs{(\Lam{\px}{\Lam{\py}{\pe}})~\pz}_ρ
      \Arrow{Unfold $\semabs{\wild}$, \Cref{thm:abs-syn-subst}} \\
  ={} & (\mathit{fun}_\py(\fn{θ_\py}{\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \repU \rangle,\py↦θ_\py]}}))[\px \Mapsto ρ(\pz).φ]
      \Arrow{$ρ(\pz)(\py) = \aA$ by \Cref{thm:lambda-bound-absent}, $\px \not= \py \not= \pz$} \\
  ={} & \mathit{fun}_\py(\fn{θ_\py}{(\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \repU \rangle,\py↦θ_\py]})[\px \Mapsto ρ(\pz).φ]})
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
  ={} & \mathit{app}((\semabs{\pe}_{ρ[\langle [\px↦\aU], \repU \rangle]})[\px \Mapsto ρ(\py).φ])(ρ(\pz))
      \Arrow{$ρ(\pz)(\px) = \aA$ by \Cref{thm:lambda-bound-absent}, $\py \not= \px \not= \pz$} \\
  ={} & \mathit{app}(\semabs{\pe}_{ρ[\langle [\px↦\aU], \repU \rangle]})(ρ(\pz))[\px \Mapsto ρ(\py).φ]
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
indicate the respective step below as ``hand-waving''.
Note that we assume the (more general) recursive let semantics as defined at the
begin of this section.

\begin{DispWithArrows*}[fleqn,mathindent=1em]
      & \semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ
      \Arrow{Unfold $\semabs{\wild}$} \\
  ={} & \semabs{(\Lam{\px}{\pe_2})~\py}_{ρ[\pz↦\lfp(\fn{θ}{\pz \both \semabs{(\Lam{\px}{\pe_1})~\py}_{ρ[\pz ↦ θ]}})]}
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle,\pz↦\lfp(\fn{θ}{\pz \both (\semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle, \pz ↦ θ]})[\px \Mapsto ρ(\py).φ]})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Hand-waving above} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle,\pz↦\lfp(\fn{θ}{\pz \both \semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle, \pz ↦ θ]}})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Refold $\semabs{\wild}$} \\
  ={} & (\semabs{\Let{\pz}{\pe_1}{\pe_2}}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle]})[\px \Mapsto ρ(\py).φ]
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ
\end{DispWithArrows*}
\end{proof}
\end{toappendix}

\begin{lemmarep}[Substitution]
\label{thm:absence-subst}
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
    ={} & \semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle]}
        \Arrow{$ρ(\pz).φ(\px) = \aA$} \\
    ={} & (\semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle]})[\px \Mapsto ρ(\py).φ]
        \Arrow{\Cref{thm:abs-syn-subst}} \\
    ={} & \semabs{(\Lam{\px}{\pz})~\py}_ρ
    \end{DispWithArrows*}
    Otherwise, we have $\px = \pz$,
    thus $ρ(\px) = \langle [\px ↦ \aU], \varsigma = \repU \rangle$,
    and thus
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{$\px = \pz$} \\
    ={} & ρ(\py)
        \Arrow{$\varsigma ⊑ \repU$} \\
    ⊑{} & \langle ρ(\py).φ, \repU \rangle
        \Arrow{Definition of $\wild[\wild\Mapsto\wild]$} \\
    ={} & (\langle [\px ↦ \aU], \repU \rangle)[\px ↦ ρ(\py).φ]
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & (\semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \repU \rangle]})[\px \Mapsto ρ(\py).φ]
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
        \Arrow{\Cref{thm:lambda-commutes-absence}} \\
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
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ}[\py↦\langle [\py ↦ \aU], \repU \rangle]})})
        \Arrow{Induction hypothesis} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ_Δ}[\py↦\langle [\py ↦ \aU], \repU \rangle]})[\many{\px \Mapsto ρ(\px).φ}, \py \Mapsto [\py ↦ \aU]]})
          \Arrow{$θ[\py \Mapsto [\py ↦ \aU]] = θ$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{ρ_Δ}[\py↦\langle [\py ↦ \aU], \repU \rangle]})[\many{\px \Mapsto ρ(\px).φ}]})
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
        & \text{\emph{Similarly for $\pe_2$, hand-waving to push out the subst as in \Cref{thm:push-let-absence}}} \\
    ={} & (\semabs{\pe_2}_{ρ_Δ[\py↦\lfp(\fn{θ}{\py \both \semabs{\pe_1}_{{ρ_Δ}[\py ↦ θ]}})]})[\many{\px \Mapsto ρ(\px).φ}]
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & (\semabs{\Let{\py}{\pe_1}{\pe_2}}_{ρ_Δ})[\many{\px \Mapsto ρ(\px).φ}]
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

For the purposes of the preservation proof, we will write $\tr$ with a tilde to
denote that abstract environment of type $\Var \to \AbsTy$, to disambiguate it
from a concrete environment $ρ$ from the LK machine.

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
      {}={}& \mathit{apps}_μ(κ)(\mathit{app}(\semabs{\Lam{\py}{\pe'}}_{α(μ) \circ ρ}, α(μ)(\pa))) \Arrow{Unfold RHS of \Cref{thm:absence-subst}} \\
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
    We will show a more general result in \Cref{thm:abstract-by-name}
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
  (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ_1,μ_1,κ) \smallstep^* (\py,ρ'[\py↦\pa],μ',κ') \smallstep[\LookupT(\px)] ...,
\]
where $ρ_1 \triangleq ρ[\px↦\pa]$, $μ_1 \triangleq μ[\pa↦(\px,ρ[\px↦\pa],\pe')]$.
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
  {}={}& ((\semabs{\pe}_{\tr_Δ})[\many{\py \Mapsto \tr(\py).φ}]).φ \Arrow{$\varsigma ⊑ \repU$, hence $\tr_Δ ⊑ \tr_\pe$} \\
  {}⊑{}& ((\semabs{\pe}_{\tr_\pe})[\many{\py \Mapsto \tr(\py).φ}]).φ \Arrow{Definition of $\wild[\wild \Mapsto \wild]$} \\
  {}={}& \Lub \{ \tr(\py).φ \mid \semabs{\pe}_{\tr_\pe}.φ(\py) = \aU \}
\end{DispWithArrows*}
But since $\tr(\py).φ(\px) = \aU$ implies $\px = \py$ (refer to definition of
$\tr$), we must have $(\semabs{\pe}_{\tr_\pe}).φ(\px) = \aU$, as required.
\end{proof}
\end{toappendix}

\Cref{defn:absence} and the substitution \Cref{thm:absence-subst} will make
a reappearance in \Cref{sec:soundness}.
They are necessary components in a soundness proof, and substitution is not
too difficult to prove for a simple summary mechanism.
Building on these definitions, we may finally attempt the proof for
\Cref{thm:absence-correct}.
We suggest for the reader to have a cursory look by clicking on the theorem
number, linking to the Appendix.
The proof is exemplary of far more ambitious proofs such as in
\citet{Sergey:14} and \citet[Section 4]{Breitner:16}.
Though seemingly disparate, these proofs all follow an established
preservation-style proof technique at heart.
%\footnote{A ``mundane approach`` according to \citet[Section
%4.1]{Nielson:99}, applicable to \emph{trace properties}, but not to
%\emph{hyperproperties}~\citep{ClarksonSchneider:10}.}
The proof of \citet{Sergey:14} for a generalisation of $\semabs{\wild}$
is roughly structured as follows (non-clickable references to Figures
and Lemmas below reference \citet{Sergey:14}):

\begin{enumerate}
  \item Instrument a standard call-by-need semantics (a variant of our reference
    in \Cref{sec:op-sem}) such that heap lookups decrement a per-address
    counter; when heap lookup is attempted and the counter is 0, the machine is stuck.
    For absence, the instrumentation is simpler: the $\LookupT$
    transition in \Cref{fig:lk-semantics} carries the let-bound variable that is
    looked up.
  \item Give a declarative type system that characterises the results of the
    analysis (\ie $\semabs{\wild}$) in a lenient (upwards closed) way.
    In case of \Cref{thm:absence-correct}, we define an analysis function on
    machine configurations for the proof (\Cref{fig:absence-ext}).
  \item Prove that evaluation of well-typed terms in the instrumented
    semantics is bisimilar to evaluation of the term in the standard semantics,
    \ie does not get stuck when the standard semantics would not.
    A classic \emph{logical relation}~\citep{Nielson:99}.
    In our case, we prove that evaluation preserves the analysis result.
\end{enumerate}
Alas, the effort in comprehending such a proof in detail, let alone formulating
it, is enormous.
\begin{itemize}
  \item
    The instrumentation (1) can be semantically non-trivial; for example the
    semantics in \citet{Sergey:14} becomes non-deterministic.
    Does this instrumentation still express the desired semantic property?
  \item Step (2) all but duplicates a complicated analysis
    definition (\ie $\semabs{\wild}$) into a type system (in Figure 7) with
    subtle adjustments expressing invariants for the preservation proof.
  \item
    Furthermore, step (2) extends this type system to small-step machine
    configurations (in Figure 13), \ie stacks and heaps, the scoping of which
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
    This case mutates the heap and thus is notoriously difficult; we give a
    proper account in \Cref{thm:abstract-by-need}.

    Although the proof in \citet{Sergey:14} is perceived as detailed and
    rigorous, it is quite terse in the corresponding \textsc{EUpd} case of the
    single-step safety proof in lemma A.6.
\end{itemize}


The main takeaway:
Although analysis and semantics might be reasonably simple, the soundness
proof that relates both is \emph{not}; it necessitates an explosion in formal
artefacts and the parts of the proof that concern the domain of the analysis are
drowned in coping with semantic subtleties that ultimately could be shared with
similar analyses.
Furthermore, the inevitable hand-waving in proofs of this size around said
semantic subtleties diminishes confidence in the soundness of the proof
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
\emph{usage cardinality}, \ie ``$\pe$ evaluates $\px$ at most $u$ times'',
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
generic interpreter, the equivalent of the preservation proof for usage analysis
in \Cref{thm:usage-abstracts-need} takes no more than a substitution
lemma and a bit of plumbing.
Hence our \emph{denotational interpreter} does not only enjoy useful
compositional semantics and analyses as instances, the soundness proofs become
compositional in the semantic domain as well.
