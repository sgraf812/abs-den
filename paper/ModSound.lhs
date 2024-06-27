%if style == newcode
> module ModSound where
%endif

\section{Modular Proofs for \textsc{Beta-App}, \textsc{Beta-Sel} and \textsc{Bind-ByName} by Parametricity}
\label{sec:mod-sound}

The usage analysis proof for \Cref{thm:usage-abstracts-need-closed} relies on
the syntactic substitution \Cref{thm:usage-subst}, which has a serious drawback:
It relies on knowing the complete definition of |eval|.
Ergo, the proof complexity scales in the size of the interpreter, and
whenever the definition of |eval| changes, \Cref{thm:usage-subst} must be
updated.
In this section, we present a cure:
To make the proof \emph{modular}, we ignore the \emph{definition} of |eval|
and prove \textsc{Beta-App}, \textsc{Beta-Sel} and \textsc{Bind-ByName} by
appealing to parametricity of the \emph{System $F$ type} of |eval|.

For a concrete example, in \textsc{Beta-App} we need to show
|forall x f a. f a ⊑ apply (fun x f) a|, where |f :: (Trace d, Domain d,
HasBind d) => d -> d| is parametric because it is defined in terms of
|eval|.
Following the semi-formal style of \citet[Section 3]{Wadler:89},
we apply the abstraction theorem to the corresponding System $F$ encoding
\[
  f : \forall X.\ \mathsf{Dict(X)} \to X \to X,
\]
where $\mathsf{Dict(|d|)}$ is the type of the type class
dictionary for |(Trace d, Domain d, HasBind d)|.
The abstraction theorem yields the following assertion about relations:
\[
  (f, f) ∈ \forall \mathcal{X}.\ \mathsf{Dict(\mathcal{X})} \to \mathcal{X} \to \mathcal{X}
\]
Wadler overloads the type formers with a suitable relational interpretation, which translates to
\begin{align}
  \forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict(R)}.\
  \forall (d_1,d_2) ∈ R.\
  (f_A(\mathit{inst_1})(d_1), f_B(\mathit{inst_2})(d_2)) ∈ R
\label{eqn:free-theorem}
\end{align}
The key to making use of parametricity is to find a useful instantiation of this
theorem, of relation $R$ in particular.
We successfully proved \textsc{BetaApp} in the Appendix with the following instantiation:
\[\begin{array}{c}
  A \triangleq B \triangleq |UD|, \qquad \mathit{inst_1} \triangleq \mathit{inst_2} \triangleq \mathit{inst}, \qquad d_1 \triangleq a, \qquad d_2 \triangleq \mathit{pre}(x) \\
  R_{x,a}(d_1,d_2) \triangleq \forall g.\ d_1 = g(a) \land d_2 = g(\mathit{pre}(x)) \implies g(a) ⊑ \mathit{apply}(\mathit{fun}(x,g),a)  \\
\end{array}\]
where $\mathit{pre}(x) \triangleq |MkUT (singenv x U1) (Rep Uω)|$ is the
argument that the implementation of |fun x f| passes to |f| and $\mathit{inst}$ is
the canonical instance dictionary at |UD|.

$R$ might look like a strange definition because the conditions relating $g$
with $d_1$ and $d_2$ appear to be dead in the conclusion.
However, they are vital to prove $R_{x,a}(a, \mathit{pre}(x))$ for example,
which simplifies to the left premise of the following derived inference rule:
\begin{align}
\inferrule[]
  { a ⊑ \mathit{apply}(\mathit{fun}(x,\mathit{id}),a) \\ (\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict(R_{x,a})} }
  { f_|UD|(\mathit{inst})(a) ⊑ \mathit{apply}(\mathit{fun}(x,f_|UD|(\mathit{inst})),a) }
\label{eqn:free-theorem}
\end{align}
which can easily be translated back to Haskell.
We have successfully applied this inference rule for an alternative proof
of \textsc{BetaApp} for usage analysis:

\begin{lemmarep}[Semantic substitution]
\label{thm:usage-subst-sem}
Let |f :: (Trace d, Domain d, HasBind d) => d -> d|, |x :: Name| and |a :: UD|.
Then |f a ⊑ apply (fun x f) a :: UD|.
\end{lemmarep}
\begin{proof}
We instantiate the free theorem for |f|
\[
  \forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict(R)}.\
  \forall (d_1,d_2) ∈ R.\
  (f_A(\mathit{inst_1})(d_1), f_B(\mathit{inst_2})(d_2)) ∈ R
\]
as follows
\[\begin{array}{c}
  A \triangleq B \triangleq |UD|, \qquad \mathit{inst_1} \triangleq \mathit{inst_2} \triangleq \mathit{inst}, \qquad d_1 \triangleq a, \qquad d_2 \triangleq \mathit{pre}(x) \\
  R_{x,a}(d_1,d_2) \triangleq \forall g.\ d_1 = g(a) \land d_2 = g(\mathit{pre}(x)) \implies g(a) ⊑ \mathit{apply}(\mathit{fun}(x,g),a)  \\
\end{array}\]
and get (translated back into Haskell)
\[
  \inferrule
    { (|a|,|pre x|) ∈ R_{|x|,|a|} \\ (\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict(R_{|x|,|a|})} }
    { (|f a|, |f (pre x)|) ∈ R_{|x|,|a|} }
\]
where |pre x := MkUT (singenv x U1) (Rep Uω)| defines the proxy for |x|,
exactly as in the implementation of |fun x|, and $\mathit{inst}$ is the canonical
instance dictionary for |UD|.

We will first apply this inference rule and then show that the goal follows from
$(|f a|, |f (pre x)|) ∈ R_{|x|,|a|}$.

To apply the inference rule, we must prove its premises.
Before we do so, it is very helpful to eliminate the quantification over
arbitrary |g| in the relation $R_{x,a}(d_1,d_2)$.
To that end, we first need to factor |fun x g = abs x (g (pre x))|, where |abs|
is defined as follows:
\begin{spec}
  abs x (MkUT φ v) = MkUT (ext φ x U0) (UCons (φ !? x) v)
\end{spec}
And we simplify $R_{|x|,|a|}(d_1,d_2)$, thus
\begin{spec}
  forall g. d1 = g a /\ d2 = g (pre x) ==> g a ⊑ apply (fun x g) a
<==> {- |fun x g = abs x (g (pre x))| -}
  forall g. d1 = g a /\ d2 = g (pre x) ==> g a ⊑ apply (abs x (g (pre x))) a
<==> {- Use |d1 = g a| and |d2 = g (pre x)| -}
  forall g. d1 = g a /\ d2 = g (pre x) ==> d1 ⊑ apply (abs x d2) a
<==> {- There exists a |g| satisfying |d1 = g a| and |d2 = g (pre x)| -}
  d1 ⊑ apply (abs x d2) a
<==> {- Inline |apply|, |abs|, simplify -}
  d1 ⊑ MkUT (ext (d2^.φ) x U0 + (d2^.φ !? x) * a^.φ) (d2^.v)
\end{spec}

It turns out that $R_{|x|,|a|}$ is reflexive on all |d| in which |x| does
not occur.
(This corresponds to summarising a function that does not use its
argument.)
That is a fact that we need in the |fun| case below, so we prove it here:
\begin{spec}
  forall d. d ⊑ MkUT (ext (d^.φ) x U0 + (d^.φ !? x) * a^.φ) (d^.v)
<==> {- Use |(d^.φ ?! x) = U0| -}
  forall d. d ⊑ MkUT (d^.φ) (d^.v) = d
\end{spec}
and the last proposition is reflexivity on $⊑$.

ADJUST DOWN HERE

Now we prove the premises:
\begin{enumerate}
  \item $(|a|,|pre x|) ∈ R_{|x|,|a|}$:
    The proposition unfolds to
    \begin{spec}
      forall g. a = g a /\ pre x = g (pre x) ==> g a ⊑ appfun x g a
    <==> {- Use |a = g a| -}
      forall g. pre x = g (pre x) ==> a ⊑ appfun x g a
    <==> {- Unfold |appfun| -}
      forall g. pre x = g (pre x) ==> a ⊑ let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
    <==> {- Use |pre x = g (pre x)|, simplify -}
      a ⊑ let MkUT φ1 v1 = pre x in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
    <==> {- Unfold |pre|, simplify -}
      a ⊑ MkUT a^.φ (Rep Uω)
    \end{spec}
    and the latter follows from |a^.v ⊑ Rep Uω| because |Rep Uω| is the Top element.

  \item $(\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict(R_{|x|,|a|})}$:
    By the relational interpretation of products, we get one subgoal per instance method.
    \begin{itemize}
      \item \textbf{Case |step|}.
        Goal: $\inferrule{(|d1|,|d2|) ∈ R_{|x|,|a|}}{(|step ev d1|, |step ev d2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premise $(|d1|,|d2|) ∈ R_{|x|,|a|}$, show the goal.
        All cases other than |ev = Look y| are trivial, because then |step ev d = d| and the goal follows by the premise.
        So let |ev = Look y|. The goal is to show
        \begin{spec}
          forall g. step (Look y) d1 = g a /\ step (Look y) d2 = g (pre x) ==> g a ⊑ appfun x g a
        \end{spec}
        So assume there exists |g :: UD -> UD| such that |step (Look y) d1 = g a| and |step (Look y) d2 = g (pre x)|.

        Then we can define a function |h :: UD -> UD| such that
        |h a = d1| and |h (pre x) = d2|, and |g = h| anywhere else.
        This function |h| is very useful to instantiate the assumption $(|d1|,|d2|)
        ∈ R_{|x|,|a|}$ at to show the goal:
        \begin{spec}
          forall g. d1 = g a /\ d2 = g (pre x) ==> g a ⊑ appfun x g a
        ==> {- Instantiate at |h| above -}
          h a ⊑ appfun x h a
        <==> {- Unfold |appfun| -}
          h a ⊑ let MkUT φ1 v1 = h (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        ==> {- Follows from |u1 ⊑ u2 ==> (u1 + U1) ⊑ (u2 + U1)| and |x /= y| -}
          step (Look y) (h a) ⊑  let MkUT φ1 v1 = step (Look y) (h (pre x)) in
                                 MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Use |h a = d1|, |h (pre x) = d2| -}
          step (Look y) d1 ⊑ let MkUT φ1 v1 = step (Look y) d2 in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Use |step (Look y) d1 = g a|, |step (Look y) d2 = g (pre x)| -}
          g a ⊑ let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Refold |appfun| -}
          g a ⊑ appfun x g a
        \end{spec}

      \item \textbf{Case |stuck|}.
        Goal: $(|stuck|, |stuck|) ∈ R_{|x|,|a|}$ \\
        \begin{spec}
          forall g. stuck = g a /\ stuck = g (pre x) ==> g a ⊑ appfun x g a
        <==> {- |g a = stuck = bottom| -}
          forall g. stuck = g a /\ stuck = g (pre x) ==> bottom ⊑ appfun x g a
        \end{spec}
        And the latter follows because |bottom| is the bottom element of |UD|.

      \item \textbf{Case |fun|}.
        Goal: $\inferrule{\forall (|d1|,|d2|) ∈ R_{|x|,|a|} \implies (|f1 d1|, |f2 d2|) ∈ R_{|x|,|a|}}{(|fun y f1|, |fun y f2|) ∈ R_{|x|,|a|}}$. \\
        Additionally, we may assume |x /= y| by lexical scoping.

        Now assume the premise. The goal is to show
        \begin{spec}
          forall g. fun y f1 = g a /\ fun y f2 = g (pre x) ==> g a ⊑ appfun x g a
        \end{spec}
        So assume there exists |g :: UD -> UD| such that |fun y f1 = g a| and |fun y f2 = g (pre x)|.

        Define
        |post d = case d of MkUT φ v -> MkUT (ext φ y U0) (UCons (φ !? y) v)|
        and note that this function is monotonic and satisfies
        |fun x f = post (f (pre x))|.

        Note that we have $(|pre y|, |pre y|) ∈ R_{|x|,|a|}$ because of |x /= y| and reflexivity.
        That in turn yields $(|f1 (pre y), f2 (pre y)|) ∈ R_{|x|,|a|}$ by assumption.
        This is useful to kickstart the following proof, showing the goal:
        \begin{spec}
          forall g. f1 (pre y) = g a /\ f2 (pre y) = g (pre x) ==> g a ⊑ appfun x g a
        ==> {- Unfold |appfun|, Monotonicity of |post| -}
          forall g. f1 (pre y) = g a /\ f2 (pre y) = g (pre x) ==>
          post (g a) ⊑ post (let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1)
        <==> {- Use |f1 (pre y) = g a|, |f2 (pre y) = g (pre x)|, simplify -}
          post (f1 (pre y)) ⊑ post (let MkUT φ1 v1 = f2 (pre y) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1)
        <==> {- |x /= y| and |a^.φ !? y = U0| due to scoping, |φ !? y| unaffected by floating |post| -}
          post (f1 (pre y)) ⊑ let MkUT φ1 v1 = post (f2 (pre y)) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Use |forall f. fun y f = post (f (pre y))| -}
          fun y f1 ⊑ let MkUT φ1 v1 = fun y f2 in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Use |fun y f1 = g a| and |fun y f2 = g (pre x)| -}
          g a ⊑ let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Refold |appfun| -}
          g a ⊑ appfun x g a
        \end{spec}

      \item \textbf{Case |apply|}.
        Goal: $\inferrule{(|l1|,|l2|) ∈ R_{|x|,|a|} \\ (|r1|,|r2|) ∈ R_{|x|,|a|}}{(|apply l1 r1|, |apply l2 r2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premises. The goal is to show
        \begin{spec}
          forall g. apply l1 r1 = g a /\ apply l2 r2 = g (pre x) ==> g a ⊑ appfun x g a
        \end{spec}
        So assume there exists |g :: UD -> UD| such that |apply l1 r1 = g a| and |apply l2 r2 = g (pre x)|.

        \begin{spec}
          forall g. f1 (pre y) = g a /\ f2 (pre y) = g (pre x) ==> g a ⊑ appfun x g a
        ==> {- Unfold |appfun|, Monotonicity of |post| -}
          forall g. f1 (pre y) = g a /\ f2 (pre y) = g (pre x) ==>
          post (g a) ⊑ post (let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1)
        <==> {- Use |f1 (pre y) = g a|, |f2 (pre y) = g (pre x)|, simplify -}
          post (f1 (pre y)) ⊑ post (let MkUT φ1 v1 = f2 (pre y) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1)
          case peel l1^.v of (u, v) -> MkUT (l1^.φ + u*r1^.φ) v
          ⊑ let MkUT φ1 v1 = case peel l2^.v of (u, v) -> MkUT (l2^.φ + u*r2^.φ) v in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Rearrange -}
          case peel l1^.v of (u, v) -> MkUT (l1^.φ + u*r1^.φ) v
          ⊑ let MkUT φ1 v1 = case peel l2^.v of (u, v) -> MkUT (l2^.φ + u*r2^.φ) v in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Refold |apply| -}
          apply l1 r1 ⊑ let MkUT φ1 v1 = apply l2 r2 in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Use |apply l1 r1 = g a| and |apply l2 r2 = g (pre x)| -}
          g a ⊑ let MkUT φ1 v1 = g (pre x) in MkUT (ext φ1 x U0 + (φ1 !? x)*a^.φ) v1
        <==> {- Refold |appfun| -}
          g a ⊑ appfun x g a
        \end{spec}
    \end{itemize}
\end{enumerate}

\end{proof}

