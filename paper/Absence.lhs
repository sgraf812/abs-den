%if style == newcode
> module Problem where
%endif

\section{The Problem We Solve}
\label{sec:problem}

What does it take to prove a compositional, summary-based analysis sound \wrt a
non-compositional small-step operational semantics?
We will recall so in this section, by way of a simplified \emph{absence
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
The form is reminiscent of \citet{Launchbury:93} and \citet{Sestoft:97} because
it is factored into \emph{A-normal form}, that is, the arguments of applications
are restricted to be variables, so the difference between lazy and eager
semantics is manifest in the semantics of $\mathbf{let}$.
Note that $\Lam{x}{x}$ (with an overbar) denotes syntax, whereas $\fn{x}{x+1}$
denotes a function in math.
In this section, only the highlighted parts are relevant, but the interpreter
definition in \Cref{sec:interp} supports data types as well.
Throughout the paper we assume that all bound program variables are distinct.

\subsection{Absence Analysis}
\label{sec:absence}

\begin{figure}
%\fboxsep=0pt\fbox{%
\begin{minipage}{0.50\textwidth}
\arraycolsep=0pt
\abovedisplayskip=0pt
\[\begin{array}{c}
 \begin{array}{rclcl}
  a & {}∈{} & \Absence     & {}::={} & \aA \mid \aU \\
  φ & {}∈{} & \Uses & {}={} & \Var \to \Absence \\
  \varsigma & {}∈{} & \Summary & {}::={} & \aA.. \mid a \sumcons \varsigma \mid \aU.. \\
  θ & {}∈{} & \AbsTy & {}::={} & \langle φ, \varsigma \rangle \\
  \\[-0.9em]
  \multicolumn{5}{c}{\aA \sumcons \aA.. \equiv \aA.. \quad \aU \sumcons \aU.. \equiv \aU..} \\
 \end{array} \\
 \\[-0.5em]
 \begin{array}{l}
  a * φ = \begin{cases} (\fn{\wild}{\aA}) & a = \aA \\ φ & a = \aU \\ \end{cases} \\
  \mathit{fun}_{\px}( f) {}={} \langle φ[\px↦\aA], φ(\px) \sumcons \varsigma \rangle \\
  \qquad\text{where } \langle φ, \varsigma \rangle = f(\langle [\px↦\aU], \aU.. \rangle) \\
  \mathit{app}(\langle φ_f, a \sumcons \varsigma \rangle)(\langle φ_a, \wild \rangle) = \langle φ_f ⊔ (a * φ_a), \varsigma \rangle \\
 \end{array}
 \\[-0.5em]
\end{array}\]
\end{minipage}%
%}%
\quad
%\fboxsep=0pt\fbox{%
\begin{minipage}{0.47\textwidth}
\arraycolsep=0pt
\abovedisplayskip=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semabs{\wild}_{\wild} \colon \Exp → (\Var \pfun \AbsTy) → \AbsTy } } \\
  \\[-0.5em]
  \semabs{\px}_ρ & {}={} & ρ(\px) \\
  \semabs{\Lam{\px}{\pe}}_ρ & {}={} & \mathit{fun}_{\px}( \fn{θ}{\semabs{\pe}_{ρ[\px ↦ θ]}}) \\
  \semabs{\pe~\px}_ρ & {}={} & \mathit{app}(\semabs{\pe}_{ρ})(ρ(\px)) \\
  \semabs{\Letsmall{\px}{\pe_1}{\pe_2}}_ρ & {}={} & \semabs{\pe_2}_{ρ[\px ↦ θ]} \\
  \text{where} \hspace{1.5em} θ &{}={}& \lfp(\fn{θ}{\px + \semabs{\pe_1}_{ρ[\px ↦ θ]}}) \\
  \px + \langle φ, \varsigma \rangle & = & \langle φ[\px↦\aU], \varsigma \rangle
  \\[-0.5em]
\end{array}\]
\end{minipage}%
%}%
\caption{Absence analysis}
  \label{fig:absence}
\end{figure}

Absence analysis for lazy programs is defined in \Cref{fig:absence}.
We informally say that $\px$ is \emph{absent} in $\pe$ when $\px$ is never
evaluated by $\pe$, regardless of the context in which $\pe$ appears.
Otherwise, $\px$ is \emph{used} in $\pe$.

The idea for $\semabs{\pe}_ρ$ is to conservatively approximate which variables are
absent ($\aA$) in $\pe$, rather than possibly used ($\aU$), given an environment
$ρ$ containing absence information about its free variables. Clearly if $\px$ is not
free in $\pe$ then $\px$ is absent in $\pe$, but our analysis does a bit better.
Consider
$$ \Let{f}{\Lam{x}{y}}{f~v}$$
Here $v$ is free in the expression, but it is absent because $f$ discards it.
The analysis records a \emph{summary} $\varsigma$ for $f$ in the environment $\rho$.
For this particular case the summary is $\aA \sumcons ??$.   \slpj{complete the example, in
particular talking about the other component of the AbsTy.  I found this whole
section hard going, given that it's such a simple analysis!}

When $\semabs{\pe}_{ρ_Δ} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
then $\px$ is absent in $\pe$, where $ρ_Δ$ is the free variable environment
defined as
\[
  ρ_Δ(\px) \triangleq \langle [\px ↦ \aU], \aU.. \rangle, \quad \text{(if $\px$ free variable of $\pe$)}.
\]
The $\langle φ, \varsigma \rangle$ syntactic form denotes an \emph{absence
type}; an abstraction of an expression.
The $φ$ captures how an expression \emph{uses} its free variables by
associating an $\Absence$ flag with each, whereas the \emph{argument summary}
$\varsigma$ describes how it uses actual arguments supplied at application
sites.
In a slight extension of function update syntax, $[\px ↦ \aU]$ denotes a $φ$
where $φ(\px) = \aU$ and $φ(\py) = \aA$ for $\px \not= \py$.
We will occasionally write $\langle φ, \varsigma \rangle[\px ↦ a]$ to mean
the same as $\langle φ[\px ↦ a], \varsigma \rangle$.
Now we can understand $ρ_Δ$ to say that evaluation of each free variable
$\px$ uses only $\px$, and that any actual argument it is applied to is used,
indicated by argument summary $\aU..$\ .

Since $\semabs{\wild}$ computes least fixpoints at recursive let bindings,
$\AbsTy$ is equipped with a semi-lattice structure, induced by the order $\aA
⊏ \aU$ on $\Absence$ flags.
The order on $\Uses$, $φ_1 ⊑ φ_2$, is defined pointwise, and the order on
$\AbsTy$ is the product order.
The order on $\Summary$ is non-structural:
The inequations $\aA.. ⊑ a \sumcons \varsigma ⊑ \aU..$ and the
product ordering on $a \sumcons \varsigma$ define a smallest preorder,
and the partial order on $\Summary$ is this preorder modulo the non-syntactic
equivalences $\aA \sumcons \aA.. \equiv \aA..$, $\aU \sumcons \aU.. \equiv
\aU..$, with $\aA..$ as the bottom element.

We can use $\semabs{\wild}$ to compute that $x_1$ is absent in
$\Let{x_2}{x_1}{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}$, as follows.
Since all let bindings are non-recursive, we will omit least fixpoints and
environment extension.
\begin{DispWithArrows*}[fleqn,mathindent=1.5em]
      & \semabs{\Let{x_2}{x_1}{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}}_{ρ_Δ}
        \Arrow{Unfold $\semabs{\Let{\px}{\pe_1}{\pe_2}}$. NB: Lazy Let!} \\
  ={} & \semabs{\Let{k}{\Lam{y}{\Lam{z}{y}}}{k~x_3~x_2}}_{ρ_Δ[x_2↦x_2+\semabs{x_1}_{ρ_Δ}]}
        \Arrow{Unfold $\semabs{\wild}$, $ρ_x \triangleq ρ_Δ[x_2↦x_2+\semabs{x_1}_{ρ_Δ}]$} \\
  ={} & \semabs{k~x_3~x_2}_{ρ_x[k↦k+\semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x}]}
        \Arrow{$ρ_{xk} \triangleq ρ_x[k↦k+\semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x}]$} \\
  ={} & \semabs{k~x_3~x_2}_{ρ_{xk}}
        \Arrow{Unfold $\semabs{\pe~\px}$ twice, $\semabs{\px}$} \\
  ={} & \mathit{app}(\mathit{app}(ρ_{xk}(k),ρ_{xk}(x_3)))(ρ_{xk}(x_2))
        \Arrow{Unfold $ρ_{xk}(k)$} \\
  ={} & \mathit{app}(\mathit{app}(k + \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x})(ρ_{xk}(x_3)))(ρ_{xk}(x_2))
        \Arrow{Unfold $\semabs{\Lam{\px}{\pe}}$ twice, $\semabs{\px}$} \\
  ={} & \mathit{app}(\mathit{app}(k + \mathit{fun}_{y}(\fn{θ_y}{\mathit{fun}_{z}(\fn{θ_z}{θ_y})}))(...))(...)
        \Arrow{Unfold $\mathit{fun}$ twice, simplify} \\
  ={} & \mathit{app}(\mathit{app}(\langle [k ↦ \aU], \highlight{\aU} \sumcons \aA \sumcons \aU.. \rangle)(\highlight{ρ_{xk}(x_3)}))(...)
        \Arrow{Unfold $\mathit{app}$, $ρ_{xk}(x_3)=ρ_Δ(x_3)$, simplify} \\
  ={} & \mathit{app}(\langle [k ↦ \aU,x_3↦\aU], \highlight{\aA} \sumcons \aU.. \rangle)(\highlight{ρ_{xk}(x_2)})
        \Arrow{Unfold $\mathit{app}$, simplify} \\
  ={} & \langle [k ↦ \aU,x_3↦\aU], \aU.. \rangle
\end{DispWithArrows*}
Both $x_1$ and $x_2$ map to $\aA$ in the final $\Uses$ $[k ↦ \aU,x_3↦\aU]$,
indicating that $x_1$ is absent.
That is in contrast to the result for the free variable $x_3$, which is used.

%In general, we can make the following \emph{soundness statement}:
%$\px$ is absent in $\pe$ when $\px \not∈ \semabs{\pe}_{\tr_Δ}$.
%Thus, $\semabs{\wild}$ can be used in a compiler to enable absent code removal.

\subsection{Function Summaries, Substitution Lemmas, Compositionality and Modularity}

% Note that it was convenient to postpone evaluation of
% $k + \semabs{\Lam{y}{\Lam{z}{y}}}_{ρ_x}$
Note that in order to see that $x_1$ was absent in the example above, absence
analysis employs a \emph{summary mechanism} to enable useful and sound analysis
of function calls, with relevant analysis information highlighted in grey.
This summary mechanism is manifest in the $\mathit{fun}$ and $\mathit{app}$
functions we deliberately extracted out, encoding a contract between function
definitions and their call sites.

We can give a more formal definition of what a summary mechanism is in terms of
abstract interpretation~\citep{Cousot:21}:
In this work, a \emph{function summary} is an approximation to, or abstraction
of, the function's abstract transformer implied by the considered analysis.

In case of $\semabs{\Lam{\px}{\pe}}$, the implied abstract transformer is the
function $f^\sharp_{ρ,\pe,\px} \triangleq \fn{θ}{\semabs{\pe}_{ρ[\px ↦
θ]}}$ passed to $\mathit{fun}_\px$,%
\footnote{Note that in contrast to let-bound names, the syntactic parameter
$\px$ is used as a convenient proxy for a De Bruijn level, if you wonder about
the scoping semantics.}
which \emph{summarises} (\ie, abstracts)
$f^\sharp_{ρ,\pe,\px}$ into something finite (\ie, not a function).
The produced summary is concretised back in $\semabs{\pe~\px}$ through
$\mathit{app}$ which encodes the adjoint (``reverse'') operation.
More concretely, $f^\sharp_{ρ,\pe,\px}(θ) ⊑
\mathit{app}(\mathit{fun}_\px(f^\sharp_{ρ,\pe,\px}))(θ)$ for any choice of
$ρ$, $\pe$, $\px$ and $θ$, suggesting a Galois connection between abstract
transformers in $\AbsTy \to \AbsTy$ and $\AbsTy$.%
\footnote{We will see at the end of \Cref{sec:by-name-soundness} why it is
important to restrict the Galois connection to syntactic $f^\sharp_{ρ,\pe,\px}$
and not arbitrary monotone functions in $\AbsTy \to \AbsTy$.}

If we unfold $f^\sharp_{ρ,\pe,\px}$ and refold $\semabs{\wild}$ twice in
the above statement, we can recognise it as a \emph{substitution lemma},
so called because the (delayed) substitution carried out when beta reducing
$(\Lam{\px}{\pe})~\py$ to $\pe[\px:=\py]$ preserves analysis results:%
\footnote{All proofs can be found in the Appendix; in case of the extended
version via clickable links.}
\footnote{An inconsequential observation: The other half of the Galois connection
proof, $\mathit{fun}_\px \circ \mathit{app} \mathbin{\ddot{⊑}} \mathit{id}$,
corresponds to eta expansion $\semabs{\Lam{\px}{\pe~\px}}_ρ ⊑
\semabs{\pe}_ρ$.}

\begin{toappendix}
\begin{abbreviation}
  The syntax $θ.φ$ for an $\AbsTy$ $θ = \langle φ, \varsigma \rangle$
  returns the $φ$ component of $θ$.
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
  ={} & \mathit{fun}_\py(\fn{θ_\py}{(\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \aU.. \rangle,\py↦θ_\py]})[\px \Mapsto ρ(\pz).φ]})
      \Arrow{$ρ(\pz)(\py) = \aA$ by \Cref{thm:lambda-bound-absent}, $\px \not= \py \not= \pz$} \\
  ={} & (\mathit{fun}_\px(\fn{θ_\px}{\semabs{\pe}_{ρ[\px↦\langle [\px↦\aU], \aU.. \rangle,\py↦θ_\py]}}))[\px \Mapsto ρ(\pz).φ]
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
This can easily be proven by induction on $\pe_2$, which we omit here, but
indicate the respective step below as ``handwaving''.

\begin{DispWithArrows*}[fleqn,mathindent=1em]
      & \semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ
      \Arrow{Unfold $\semabs{\wild}$} \\
  ={} & \semabs{(\Lam{\px}{\pe_2})~\py}_{ρ[\pz↦\lfp(\fn{θ}{\px + \semabs{(\Lam{\px}{\pe_1})~\py}_{ρ[\pz ↦ θ]}})]}
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle,\pz↦\lfp(\fn{θ}{\px + (\semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle, \pz ↦ θ]})[\px \Mapsto ρ(\py).φ]})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Handwaving above} \\
  ={} & (\semabs{\pe_2}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle,\pz↦\lfp(\fn{θ}{\px + \semabs{\pe_1}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle, \pz ↦ θ]}})]})[\px \Mapsto ρ(\py).φ]
      \Arrow{Refold $\semabs{\wild}$} \\
  ={} & (\semabs{\Let{\pz}{\pe_1}{\pe_2}}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]
      \Arrow{\Cref{thm:abs-syn-subst}} \\
  ={} & \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ
\end{DispWithArrows*}
\end{proof}
\end{toappendix}

\begin{lemmarep}[Substitution, syntactically]
\label{thm:subst-absence}
$\semabs{\pe}_{ρ[\px↦ρ(\py)]} ⊑ \semabs{(\Lam{\px}{\pe})~\py}_ρ$.
\end{lemmarep}
\begin{proof}
By induction on $\pe$.
\begin{itemize}
  \item \textbf{Case }$\pz$:
    When $\px \not= \pz$, we have
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\pz}_{ρ[\px↦ρ(\py)]}
        \Arrow{$\px \not= \pz$} \\
    ={} & ρ(\pz)
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]}
        \Arrow{By \Cref{thm:lambda-bound-absent}, $φ(\px) = \aA$} \\
    ⊑{} & (\semabs{\pz}_{ρ[\px↦\langle [\px ↦ \aU], \aU.. \rangle]})[\px \Mapsto ρ(\py).φ]
        \Arrow{\Cref{thm:abs-syn-subst}} \\
    ={} & \semabs{(\Lam{\px}{\pz})~\py}_ρ
    \end{DispWithArrows*}
    The application of \Cref{thm:lambda-bound-absent} above requires
    that $ρ(\py)$ is \emph{syntactic}, \eg, of the form $\px' +
    \semabs{\pe'}_{ρ'}$ for some $\px'$, $\pe'$, $ρ'$.
    A detail we hand-wave over for now, but revisit in \Cref{defn:syn-name}.

    Otherwise, we have $\px = \pz$, thus $φ = [\px ↦ \aU], \varsigma = \aU..$, and thus
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
    ={} & \semabs{\pe_2}_{ρ[\px↦ρ(\py),\pz↦\lfp(\fn{θ}{\pz + \semabs{\pe_1}_{ρ[\px↦ρ(\py),\pz ↦ θ]}})]}
        \Arrow{Induction hypothesis, monotonicity} \\
    ⊑{} & \semabs{(\Lam{\px}{\pe_2})~\py}_{ρ[\pz↦\lfp(\fn{θ}{\pz + \semabs{(\Lam{\px}{\pe_1})~\py}_{ρ[\pz ↦ θ]}})]}
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & \semabs{\Let{\pz}{(\Lam{\px}{\pe_1})~\py}{(\Lam{\px}{\pe_2})~\py}}_ρ
        \Arrow{\Cref{thm:push-let-absence}} \\
    ={} & \semabs{(\Lam{\px}{\Let{\pz}{\pe_1}{\pe_2}})~\py}_ρ
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

We conjecture that every substitution lemma has a summary mechanism it proves
correct; that is why they are capstone lemmas in type system soundness
proofs~\citep{tapl} and a crucial part in proving $\semabs{\wild}$ correct.

Summaries arise naturally in a compiler analysis such as $\semabs{\pe}$ that is
\emph{compositional}:%
\footnote{Although even non-compositional analyses such as CFA \emph{might}
employ a summary mechanism; see \Cref{sec:related-work}.}
A (static or dynamic) semantics $\denot{\wild}$ is compositional
when $\denot{\pe}$ can be defined as a function solely of the denotations
$\denot{\pe_1}, ..., \denot{\pe_n}$ of $\pe$'s subexpressions $\pe_1,...,\pe_n$,
but \emph{not} of the subexpressions themselves.

Compositionality implies that $\denot{\Let{\px}{\Lam{\py}{\pe_1}}{\pe_2}}$
is a function of $\denot{\Lam{\py}{\pe_1}}$, itself a function of
$\denot{\pe_1}$.
In order to satisfy the scalability requirements of a compiler and
guarantee termination of the analysis in the first place, it is
important not to repeat the work of analysing $\denot{\pe_1}$, so
$\denot{\Let{\px}{\Lam{\py}{\pe_1}}{\pe_2}}$ computes a \emph{finite} summary
(\ie, data) for $\denot{\Lam{\py}{\pe_1}}$ to apply at use sites of $\px$ in
$\pe_2$. For our absence analysis, summarisation is baked right into the lambda
case rather than the let case.
% Doing so keeps the analysis domain simple, even though it penalises analysis
% of redexes such as $(\Lam{y}{\Lam{z}{z}})~x$ that fortunately are unlikely
% to be encountered in an optimised program.

In the same way that compositionality and finite summaries enable scalability
\emph{within} a module~\citep[Section 11.3.2]{Shivers:91}, they ensure
\emph{modularity}~\citep{Cousot:02}, \ie, scalability \emph{across} module
boundaries.
Let us say that $f = (\Lam{y}{\Lam{z}{z}})$ is defined
in module A and there is a use site $(f~x_1~x_2)$ in module B.
To analyse the use site, we only need to load $f$'s summary $\aA \sumcons \aU..$
from module A's signature file, but do not need to reanalyse its definition.

\subsection{Soundness}

Suppose now that we were to prove $\semabs{\wild}$ correct.
What are the main obstacles to do so?
As the first step, we must define what absence \emph{means}, in a formal sense.
There are many ways to do so, and it is not at all clear which is best.
One plausible definition is in terms of the operational semantics in
\Cref{sec:op-sem}.
Given such a formal definition, soundness is easily stated:

\begin{toappendix}
\begin{definition}[Operational Absence]
  \label{defn:absence}
  A variable $\px$ is \emph{used} in an expression $\pe$
  if and only if there exists a trace
  $(\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],\wild,\wild) \smallstep^* (\py,ρ'[\py↦\pa],\wild,\wild)$
  that is about to evaluate $\px$, \ie, look up its heap entry.
  Otherwise, $\px$ is \emph{absent} in $\pe$.
\end{definition}

The elaborate setup of this definition ensures that $\pa$, the address that
$\px$ binds, does not alias with anything defined in the initial heap $μ$ and
thus not with anything in $ρ$ or $κ$.
Unsurprisingly, the no-alias property is easily defeated during evaluation, as
soon as $\px$ is passed as an argument, hence $\py$ can be chosen differently to
$\px$ in \Cref{defn:absence}.

For the purposes of the correctness proof, we will write $\tr$ with a tilde to
denote that abstract environment of type $\Var \to \AbsTy$, to disambiguate it
from a concrete environment $ρ$ from the LK machine.

Whenever there exists $\tr$ such that $\tr(\px) \not⊑ (\semabs{\pe}_\tr).φ$
(recall that $θ.φ$ selects the $\Uses$ in the first field of the pair $θ$),
then also $\tr_Δ(\px) \not⊑ \semabs{\pe}_{\tr_Δ}$.
The following lemma captures this intuition:

\begin{lemma}[Diagonal factoring]
\label{thm:diag-fact}
Let $\tr_α$ be an environment such that $\tr_α.φ(\px) ⊑ \tr_α.φ(\py)$ if
and only if $\px = \py$.

Then every instantiation of $\semabs{\pe}$ factors through $\semabs{\pe}_{\tr_α}$,
that is,
\[
  \semabs{\pe}_\tr = (\semabs{\pe}_{\tr_α})[\many{\px \Mapsto \tr(\px).φ}]
\]
\end{lemma}
\begin{proof}
By induction on $\pe$.
\begin{itemize}
  \item \textbf{Case $\pe = \py$}:
    We assert $\semabs{\py}_\tr = \tr(\py) = \tr_α(\py)[\py \Mapsto \tr(\py).φ]$ by simple unfolding.

  \item \textbf{Case $\pe = \pe'~\py$}:
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
          & \semabs{\pe'~\py}_\tr
          \Arrow{Unfold $\semabs{\wild}$} \\
      ={} & \mathit{app}(\semabs{\pe'}_\tr,\tr(\py))
          \Arrow{Induction hypothesis, variable case} \\
      ={} & \mathit{app}((\semabs{\pe'}_{\tr_α})[\many{\px \Mapsto \tr(\px).φ}], \tr_α(\py)[\many{\px \Mapsto \tr(\px).φ}]).
          \Arrow{$⊔$ and $*$ commute with $\wild[\wild\Mapsto\wild]$} \\
      ={} & \mathit{app}(\semabs{\pe'}_{\tr_α},\tr_α(\py))[\many{\px \Mapsto \tr(\px).φ}]
          \Arrow{Refold $\semabs{\wild}$} \\
      ={} & (\semabs{\pe'~\py}_{\tr_α})[\many{\px \Mapsto \tr(\px).φ}]
    \end{DispWithArrows*}

  \item \textbf{Case $\pe = \Lam{\py}{\pe'}$}:
    Note that $\px \not= \py$ because $\py$ is not free in $\pe$.
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
          & \semabs{\Lam{\py}{\pe'}}_\tr
          \Arrow{Unfold $\semabs{\wild}$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{\semabs{\pe'}_{\tr[\py↦θ]}})
          \Arrow{Property of $\mathit{lam}_\py$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{\tr}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})})
        \Arrow{Induction hypothesis} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{\tr_α}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})[\many{\px \Mapsto \tr(\px).φ}, \py \Mapsto [\py ↦ \aU]]})
          \Arrow{$θ[\py \Mapsto [\py ↦ \aU]] = θ$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{\tr_α}[\py↦\langle [\py ↦ \aU], \aU.. \rangle]})[\many{\px \Mapsto \tr(\px).φ}]})
          \Arrow{$θ[\py \Mapsto [\py ↦ \aU]] = θ$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{(\semabs{\pe'}_{{\tr_α}[\py↦θ]})[\many{\px \Mapsto \tr(\px).φ}]})
          \Arrow{Property of $\mathit{lam}_\py$} \\
      ={} & \mathit{lam}_\py(\fn{θ}{\semabs{\pe'}_{{\tr_α}[\py↦θ]}})[\many{\px \Mapsto \tr(\px).φ}]
          \Arrow{Refold $\semabs{\wild}$} \\
      ={} & (\semabs{\Lam{\py}{\pe'}}_{\tr_α})[\many{\px \Mapsto \tr(\px).φ}]
    \end{DispWithArrows*}

  \item \textbf{Case }$\Let{\py}{\pe_1}{\pe_2}$:
    Note that $\px \not= \py$ because $\py$ is not free in $\pe$.
    \begin{DispWithArrows*}[fleqn,mathindent=4em]
        & \semabs{\Let{\py}{\pe_1}{\pe_2}}_\tr
        \Arrow{Unfold $\semabs{\wild}$} \\
    ={} & \semabs{\pe_2}_{\tr[\py↦\lfp(\fn{θ}{\py + \semabs{\pe_1}_{\tr[\py ↦ θ]}})]}
        \Arrow{Induction hypothesis} \\
    ={} & \semabs{\pe_2}_{\tr[\py↦\lfp(\fn{θ}{(\semabs{\pe_1}_{{\tr_α}[\py ↦ \langle [\py ↦ \aU], θ.\varsigma \rangle]})[\many{\px \Mapsto \tr(\px).φ}, \py \Mapsto θ.φ]})]}
        \Arrow{Induction hypothesis, backwards} \\
    ={} & \semabs{\pe_2}_{\tr[\py↦\lfp(\fn{θ}{(\semabs{\pe_1}_{{\tr_α}[\py ↦ θ]})[\many{\px \Mapsto \tr(\px).φ}]})]} \\
        & \qquad \text{\emph{Similarly for $\pe_2$, handwaving to push out the subst as in \Cref{thm:push-let-absence}}} \\
    ={} & (\semabs{\pe_2}_{\tr_α[\py↦\lfp(\fn{θ}{\semabs{\pe_1}_{{\tr_α}[\py ↦ θ]}})]})[\many{\px \Mapsto \tr(\px).φ}]
        \Arrow{Refold $\semabs{\wild}$} \\
    ={} & (\semabs{\Let{\py}{\pe_1}{\pe_2}}_{\tr_α})[\many{\px \Mapsto \tr(\px).φ}]
    \end{DispWithArrows*}
\end{itemize}
\end{proof}

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
                   α(μ) & {}={} & \lfp(\fn{\tm}{[ \pa ↦ \px + \semabs{\pe'}_{\tm \circ ρ'} \mid μ(\pa) = (\px,ρ',\pe') ]}) \\
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
For safety properties such as absence, a least fixed-point is appropriate.
Apply frames on the stack correspond to the application case of $\semabs{\wild}$
and hence encode a need for the whole heap entry they point to.
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
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pe_2}_{(α(μ) \circ ρ)[\py↦\py + \lfp(\fn{θ}{\semabs{\pe_1}_{(α(μ) \circ ρ)[\py↦θ]}})]}) \Arrow{Move fixpoint outwards, refold $α$} \\
      {}={}& \mathit{apps}_{μ_1}(κ)(\semabs{\pe_2}_{α(μ_1) \circ ρ_1}) \Arrow{Stack was well-addressed in $μ$} \\
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
      {}={}& \mathit{apps}_μ(κ)(\pz + \semabs{\pe'}_{α(μ) \circ ρ'}) \Arrow{Drop $[\pz↦\aU]$} \\
      {}⊒{}& \mathit{apps}_μ(κ)(\semabs{\pe'}_{α(μ) \circ ρ'}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}

  \item \textbf{Case }$\UpdateT$:
    Then $(\pv, ρ, μ[\pa↦(\py,ρ',\pe')], \UpdateF(\pa) \pushF κ) \smallstep (\pv,ρ,μ[\pa↦(\py,ρ,\pv)],κ)$.

    This case is a bit hand-wavy and shows how heap update during by-need
    evaluation is dreadfully complicated to handle, even though
    $\semabs{\wild}$ is correct heap-less and otherwise correct \wrt by-name
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
    has been proven for all $n < k$ and proceed to prove it for $n = k$.
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

    Assuming \Cref{eqn:absent-upd} has been proven, we proceed
    \begin{DispWithArrows*}[fleqn,mathindent=3em]
           & \semabsS{σ_1} \Arrow{Unfold $\semabsS{σ_1}$} \\
      {}={}& \mathit{apps}_μ(κ)(\semabs{\pv}_{α(μ) \circ ρ}) \Arrow{Above argument that $\semabs{\pv}_{α(μ) \circ ρ} ⊑ \semabs{\pe'}_{α(μ') \circ ρ'}$} \\
      {}⊒{}& \mathit{apps}_{μ[\pa↦(\py,ρ,\pv)]}(κ)(\semabs{\pv}_{α(μ[\pa↦(\py,ρ,\pv)]) \circ ρ}) \Arrow{Refold $\semabsS{σ_2}$} \\
      {}={}& \semabsS{σ_2}
    \end{DispWithArrows*}
%    NB: This result is doubly subtle in that heap update may change the data dependencies of the heap;
%    For example, $\Let{x}{\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}}{x}$ will
%    evaluate to a mutually recursive heap
%    \[
%      [\pa_1↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~y), \pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)],
%    \]
%    whereas before the final heap update to $\pa_1$ we have
%    \[
%      [\pa_1↦([x↦\pa_1],\Let{y}{\texttt{Just}~x}{\texttt{Just}~y}),\pa_2↦([x↦\pa_1,y↦\pa_2],\texttt{Just}~x)].
%    \]
\end{itemize}
\end{proof}
\end{toappendix}

\begin{theoremrep}[Correct absence analysis]
  \label{thm:absence-correct}
  If $\semabs{\pe}_{\tr_Δ} = \langle φ, \varsigma \rangle$ and $φ(\px) = \aA$,
  then $\px$ is absent in $\pe$.
\end{theoremrep}
\begin{proof}
We show the contraposition, that is,
if $\px$ is used in $\pe$, then $φ(\px) = \aU$.

Since $\px$ is used in $\pe$, there exists a trace
\[
  (\Let{\px}{\pe'}{\pe},ρ,μ,κ) \smallstep (\pe,ρ[\px↦\pa],μ[\pa↦(\px,ρ[\px↦\pa],\pe')],κ) \smallstep^* (\py,ρ'[\py↦\pa],μ',κ').
\]
Let us abbreviate $ρ_1 \triangleq ρ[\px↦\pa]$, $μ_1 \triangleq μ[\pa↦(\px,ρ[\px↦\pa],\pe')]$.

Without loss of generality, we assume that there is no other heap entry for
$\px$ yet -- this may happen under a lambda that is called multiple times, and
when that happens we can always find a simpler evaluation context in which this
is not the case.
(This is a subtle claim that we would have to prove as well if we were serious.)
Furthermore, let us assume that this is the first lookup at $\pa$, so $μ'(\pa) = μ_1(\pa) = (\px, ρ_1,\pe')$.

Let us abbreviate $\tr \triangleq (α(μ_1) \circ ρ_1)$.
Under the above assumptions, $\tr(\py).φ(\px) = \aU$ implies $\px = \py$ for all
$\py$, because $μ_1(\pa)$ is the only heap entry in which $\px$ occurs.

By unfolding $\semabsS{\wild}$ and $\semabs{\py}$ we can see
that $[\px ↦ \aU] ⊑ α(μ')(\pa).φ ⊑ (\semabsS{(\py,ρ'[\py↦\pa],μ',κ')}).φ$.
By \Cref{thm:preserve-absent} and transitivity, we also have
$[\px ↦ \aU] ⊑ (\semabsS{(\pe,ρ_1,μ_1,κ)}).φ$.
Since there was no other heap entry for $\px$ and $\pa$ cannot occur in $κ$ or
$ρ$ due to well-addressedness, we have $[\px ↦ \aU] ⊑ (\semabsS{(\pe,ρ_1,μ_1,κ)}).φ$ if
and only if $[\px ↦ \aU] ⊑ (\semabs{\pe}_{\tr}).φ$.
With \Cref{thm:diag-fact}, we can decompose
\[
  [\px ↦ \aU] ⊑ (\semabs{\pe}_{\tr}).φ = (\semabs{\pe}_{\tr_Δ}[\many{\py \Mapsto \tr(\py).φ}]).φ = \Lub \{ \tr(\py).φ \mid \py ∈ \semabs{\pe}_{\tr_Δ}.φ(\py) = \aU \}
\]
But since $\tr(\py).φ(\px) = \aU$ implies $\px = \py$, we must have
$(\semabs{\pe}_{\tr_Δ}).φ(\px) = \aU$, as required.
\end{proof}

The proof of this statement in the Appendix is exemplary of more ambitious
proofs such as in \citet{Sergey:14} and \citet[Section 4]{Breitner:16}.
We suggest the reader to have a cursory look.
Though seemingly disparate, these proofs all follow an established
preservation-style proof technique at heart.%
\footnote{A ``mundane approach`` according to \citet[Section
4.1]{Nielson:99}, applicable to \emph{trace properties}, but not to
\emph{hyperproperties}~\citep{ClarksonSchneider:10}.}
The proof of \citet{Sergey:14}, who prove a generalisation of $\semabs{\wild}$
correct, is roughly structured as follows (non-clickable references to Figures
and lemmas below reference \citet{Sergey:14}):

\begin{enumerate}
  \item Instrument a standard call-by-need semantics (a variant of our reference
    in \Cref{sec:op-sem}) such that heap lookups decrement a per-address
    counter; when heap lookup is attempted and the counter is 0, the machine is stuck.
  \item Give a declarative type system that characterises the results of the
    analysis (\ie, $\semabs{\wild}$) in a lenient (upwards closed) way, a unary
    \emph{logical relation}~\citep{Nielson:99}.
  \item Prove that evaluation of well-typed terms in the instrumented
    semantics is bisimilar to evaluation of the term in the standard semantics,
    \ie, does not get stuck when the standard semantics would not.
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
  \item
    This is all setup before step (3) proves interesting properties about the
    semantic domain of the analysis.
    Among the more interesting properties is the \emph{substitution lemma} A.8
    to be applied during beta reduction; exactly as in our proof.
  \item
    Although the proof for step (3) is perceived as detailed and rigorous, it
    hand-waves in the key proof for single-step safety in lemma A.6.
    The proof claims that the heap update step \textsc{EUpd} to memoise a value
    is similar to when looking up a value in the heap \textsc{ELkpV}, neglecting
    the implied mutable update of the heap that is not present in \textsc{ELkpV}.

    In our experience this step hides the thorniest of surprises; that is
    definitely the case in the correctness proof for $\semabs{\wild}$ as well as
    \Cref{thm:soundness-by-need}.

    \sg{Is this a fair characterisation or perhaps too destructive already? I
    really don't want to diminish Ilya's contribution here; it was an enormous
    undertaking.}
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
\footnote{A more useful application of the ``at most once'' cardinality is the
identification of \emph{one-shot} lambdas~\citep{Sergey:14} --- functions
which are called at most once for every activation --- because it allows for
inlining computations into function bodies.}.

For these reasons, we set out to find a \textbf{\emph{compositional semantics
that exhibits operational detail}} just like the trace-generating semantics of
\citet{Cousot:21}, and were successful.
The example of usage analysis in \Cref{sec:abstraction} (generalising
$\semabs{\wild}$, as suggested above) demonstrates that we can
\textbf{\emph{derive summary-based analyses as an abstract interpretation}} from
our semantics.
Since both semantics and analysis are derived from the same compositional
interpreter skeleton, the correctness proof for usage analysis in
\Cref{thm:usage-correct} takes no more than a substitution lemma and a bit of
plumbing.
Hence our \emph{Denotational Interpreter} does not only enjoy useful
compositional semantics and analyses as instances, the soundness proofs become
compositional as well, building on reusable evaluation-order-specific theorems
such as \Cref{thm:soundness-by-name}.
