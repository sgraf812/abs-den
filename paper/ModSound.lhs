%if style == newcode
> module ModSound where
%endif

\section{Modular Proofs for \textsc{Beta-App}, \textsc{Beta-Sel} and \textsc{Bind-ByName} by Parametricity}
\label{sec:mod-sound}

The usage analysis proof for \Cref{thm:usage-abstracts-need-closed} relies on
the syntactic substitution \Cref{thm:usage-subst}, which has a serious drawback\sven{Refer to the substitution lemma in Section 2. We should remove Lemma 7, because we do not use it anymore.}:
It relies on knowing the complete definition of |eval| and thus is
\emph{non-modular}.
As a result, the proof complexity scales in the size of the interpreter, and
whenever the definition of |eval| changes, \Cref{thm:usage-subst} must be
updated.
The complexity of such non-modular proofs would become unmanageable for large
denotational interpreters such as for WebAssembly~\citep{Brandl:23}.
Fortunately, the complexity of the \emph{semantic domain} of the interpreter
scales better.

Hence, this section attempts a more \emph{modular} proof for \textsc{Beta-App}
that ignores the \emph{definition} of |eval| and proves it by appealing to
parametricity of the \emph{System $F$ type} of |eval|.
(Do note that the proofs for \textsc{Beta-Sel} and \textsc{Bind-ByName} in
\Cref{thm:usage-abstracts-need-closed} either build on \textsc{Beta-App} or
ignore |eval| already.)

For a concrete example, in \textsc{Beta-App} we need to show
|forall x f a. f a ⊑ apply (fun x f) a|, where |f :: (Trace d, Domain d,
HasBind d) => d -> d| is parametric because it is defined in terms of
|eval|.
Following the semi-formal style of \citet[Section 3]{Wadler:89},
we apply the abstraction theorem to the corresponding System $F$ encoding
\[
  f : \forall X.\ \mathsf{Dict}(X) \to X \to X,
\]
where $\mathsf{Dict}(|d|)$ is the type of the type class
dictionary for |(Trace d, Domain d, HasBind d)|.
The abstraction theorem yields the following assertion about relations:\sven{I don't understand the following line. Why does $f$ appear twice there. The formula with relation $R$ you introduce below is much more descriptive. You should remove the following line and instead focus on explaining the formula with $R$ instead: If $R$ relates the type-class instances $\mathit{inst}_1, \mathit{inst}_2$, then $R$ relates $f$ instantiated at $\mathit{inst}_1$ with $f$ instantiated at $\mathit{inst}_2$.}
\[
  (f, f) ∈ \forall \mathcal{X}.\ \mathsf{Dict}(\mathcal{X}) \to \mathcal{X} \to \mathcal{X}
\]
Wadler overloads the type formers with a suitable relational interpretation, which translates to
\[
  \forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict}(R).\
  \forall (d_1,d_2) ∈ R.\
  (f_A(\mathit{inst_1})(d_1), f_B(\mathit{inst_2})(d_2)) ∈ R
\]
The key to making use of parametricity is to find a useful instantiation of this
theorem, of relation $R$ in particular.
We successfully proved \textsc{Beta-App} in the Appendix with the following instantiation:
\[\begin{array}{c}
  A \triangleq B \triangleq |UD|, \qquad \mathit{inst_1} \triangleq \mathit{inst_2} \triangleq \mathit{inst}, \qquad d_1 \triangleq a, \qquad d_2 \triangleq \mathit{pre}(x) \\
  R_{x,a}(d_1,d_2) \triangleq \forall g.\ d_1 = g(a) \land d_2 = g(\mathit{pre}(x)) \implies g(a) ⊑ \mathit{apply}(\mathit{fun}(x,g),a)  \\
\end{array}\]
where $\mathit{pre}(x) \triangleq |MkUT (singenv x U1) (Rep Uω)|$ is the
argument that the implementation of |fun x f| passes to |f| and $\mathit{inst}$ is
the canonical instance dictionary at |UD|.

$R_{x,a}$ might look like a strange definition because the conditions relating
$g$ with $d_1$ and $d_2$ appear to be dead in the conclusion\sven{I don't get that.}.
However, the conditions are vital to prove $R_{x,a}(a, \mathit{pre}(x))$ for
example, and are useful to simplify $g$ away entirely once |fun| is inlined
(in the Appendix).\sven{You need to explain more what has to be proven for $\mathsf{Dict}(R)$}

From the abstraction theorem, we derive the following inference rule\sven{This inference motivates how we prove our goal. Move this paragraph directly after the instantiation of the abstraction theorem.}
\[
\inferrule[]
  { a ⊑ \mathit{apply}(\mathit{fun}(x,\mathit{id}),a) \\ (\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict}(R_{x,a}) }
  { f_|UD|(\mathit{inst})(a) ⊑ \mathit{apply}(\mathit{fun}(x,f_|UD|(\mathit{inst})),a) }
\]
which can easily be translated back to Haskell.
We have successfully applied this inference rule for an alternative proof
of \textsc{Beta-App} for usage analysis:

\begin{lemmarep}[Semantic substitution]
\label{thm:usage-subst-sem}
Let |f :: (Trace d, Domain d, HasBind d) => d -> d|, |x :: Name| lambda-bound
and |a :: UD|.
Then |f a ⊑ apply (fun x f) a :: UD|.\sven{Please use top-down explanation: Start with lemma 11 and then explain how it can be proven}
\end{lemmarep}
\begin{proof}
We instantiate the free theorem for |f|
\[
  \forall A, B.\
  \forall R ⊆ A \times B.\
  \forall (\mathit{inst_1}, \mathit{inst_2}) ∈ \mathsf{Dict}(R).\
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
    { (|a|,|pre x|) ∈ R_{|x|,|a|} \\ (\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict}(R_{|x|,|a|}) }
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
  d1 ⊑ let MkUT φ v = d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
\end{spec}

Note that this implies |d1^.φ !? x = U0|, because |ext φ x U0 !? x = U0|
and |a^.φ !? x = U0| by the scoping discipline.

It turns out that $R_{|x|,|a|}$ is reflexive on all |d| for which |d^.φ ?! x =
U0|; indeed, then the inequality becomes an equality.
(This corresponds to summarising a function that does not use its
argument.)
That is a fact that we need in the |stuck|, |fun|, |con| and |select| cases
below, so we prove it here:
\begin{spec}
  forall d. d ⊑ MkUT (ext (d^.φ) x U0 + (d^.φ !? x) * a^.φ) (d^.v)
<==> {- Use |(d^.φ ?! x) = U0| -}
  forall d. d ⊑ MkUT (d^.φ) (d^.v) = d
\end{spec}
The last proposition is reflexivity on $⊑$.

Now we prove the premises of the abstraction theorem:
\begin{itemize}
  \item $(|a|,|pre x|) ∈ R_{|x|,|a|}$:
    The proposition unfolds to
    \begin{spec}
      a ⊑ let MkUT φ v = pre x in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
    <==> {- Unfold |pre|, simplify -}
      a ⊑ MkUT (a^.φ) (Rep Uω)
    \end{spec}
    The latter follows from |a^.v ⊑ Rep Uω| because |Rep Uω| is the Top element.

  \item $(\mathit{inst}, \mathit{inst}) ∈ \mathsf{Dict}(R_{|x|,|a|})$:
    By the relational interpretation of products, we get one subgoal per instance method.
    \begin{itemize}
      \item \textbf{Case |step|}.
        Goal: $\inferrule{(|d1|,|d2|) ∈ R_{|x|,|a|}}{(|step ev d1|, |step ev d2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premise $(|d1|,|d2|) ∈ R_{|x|,|a|}$, show the goal.
        All cases other than |ev = Look y| are trivial, because then |step ev d = d| and the goal follows by the premise.
        So let |ev = Look y|. The goal is to show
        \begin{spec}
          step (Look y) d1 ⊑ let MkUT φ v = step (Look y) d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}
        We begin by unpacking the assumption $(|d1|,|d2|) ∈ R_{|x|,|a|}$ to show it:
        \begin{spec}
          d1 ⊑ let MkUT φ v = d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        ==>   {- |step (Look y)| is monotonic -}
          step (Look y) d1 ⊑ step (Look y) (MkUT (ext (d2^.φ) x U0 + (d2^.φ !? x) * a^.φ) (d2^.v))
        <==> {- Refold |step (Look y)| -}
          step (Look y) d1 ⊑ MkUT (ext (d2^.φ) x U0 + singenv y U1 + (d2^.φ !? x) * a^.φ) (d2^.v)
        <==>  {- |step (Look y)| preserves value and $|x| \not= |y|$ because |y| is let-bound -}
          step (Look y) d1 ⊑ let MkUT φ v = step (Look y) d2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

      \item \textbf{Case |stuck|}.
        Goal: $(|stuck|, |stuck|) ∈ R_{|x|,|a|}$ \\
        Follows from reflexivity, because |stuck = bottom|, and |bottom^.φ !? x = U0|.

      \item \textbf{Case |fun|}.
        Goal: $\inferrule{\forall (|d1|,|d2|) ∈ R_{|x|,|a|} \implies (|f1 d1|, |f2 d2|) ∈ R_{|x|,|a|}}{(|fun y f1|, |fun y f2|) ∈ R_{|x|,|a|}}$. \\
        Additionally, we may assume $|x| \not= |y|$ by lexical scoping.

        Now assume the premise. The goal is to show
        \begin{spec}
          fun y f1 ⊑ let MkUT φ v = fun y f2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        Recall that |fun y f = abs y (f (pre y))| and that |abs y| is monotonic.

        Note that we have $(|pre y|, |pre y|) ∈ R_{|x|,|a|}$ because of $|x| \not= |y|$ and reflexivity.
        That in turn yields $(|f1 (pre y), f2 (pre y)|) ∈ R_{|x|,|a|}$ by assumption.
        This is useful to kickstart the following proof, showing the goal:
        \begin{spec}
          f1 (pre y) ⊑ let MkUT φ v = f2 (pre y) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        ==>   {- Monotonicity of |abs y| -}
          abs y (f1 (pre y)) ⊑ abs y (let MkUT φ v = f2 (pre y) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
        <==>  {- $|x| \not= |y|$ and |a^.φ !? y = U0| due to scoping, |φ !? x| unaffected by floating |abs| -}
          abs y (f1 (pre y)) ⊑ let MkUT φ v = abs y (f2 (pre y)) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        <==>  {- Rewrite |abs y (f (pre y)) = fun y f| -}
          fun y f1 ⊑ let MkUT φ v = fun y f2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

      \item \textbf{Case |apply|}.
        Goal: $\inferrule{(|l1|,|l2|) ∈ R_{|x|,|a|} \\ (|r1|,|r2|) ∈ R_{|x|,|a|}}{(|apply l1 r1|, |apply l2 r2|) ∈ R_{|x|,|a|}}$. \\
        Assume the premises. The goal is to show
        \begin{spec}
          apply l1 r1 ⊑ let MkUT φ v = apply l2 r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        \begin{spec}
          apply l1 r1
        ⊑  {- |l1 ⊑ apply (abs x l2)|, |r2 ⊑ apply (abs x r2)|, monotonicity -}
          apply  (let MkUT φ v = l2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
                 (let MkUT φ v = r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
        ⊑  {- Componentwise, see below -}
          let MkUT φ v = apply l2 r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
        \end{spec}

        For the last step, we show the inequality for |φ| and |v| independently.
        For values, it is easy to see by calculation that the value is
        |v := snd (peel l2^.v)| in both cases.
        The proof for the |Uses| component is quite algebraic;
        we will abbreviate |u := fst (peel l2^.v)|:
        \begin{spec}
          (apply  (let MkUT φ v = l2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)
                  (let MkUT φ v = r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v))^.φ
        =  {- Unfold |apply| -}
          ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * (ext (r2^.φ) x U0 + (r2^.φ !? x) * a^.φ)
        =  {- Distribute |u * (φ1 + φ2) = u*φ1 + u*φ2| -}
          ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * ext (r2^.φ) x U0 + u * (r2^.φ !? x) * a^.φ
        =  {- Commute -}
          ext (l2^.φ) x U0 + u * ext (r2^.φ) x U0 + (l2^.φ !? x) * a^.φ + u * (r2^.φ !? x) * a^.φ
        =  {- |ext φ1 x U0 + ext φ2 x U0 = ext (φ1 + φ2) x U0|, |u*φ1 + u*φ2 = u * (φ1+φ2)| -}
          ext (l2^.φ + u * r2^.φ) x U0 + ((l2^.φ + u * r2^.φ) !? x) * a^.φ
        =  {- Refold |apply| -}
          let MkUT φ _ = apply l2 r2 in ext φ x U0 + (φ !? x) * a^.φ
        \end{spec}

      \item \textbf{Case |con|}.
        Goal: $\inferrule{\many{(|d1|,|d2|) ∈ R_{|x|,|a|}}}{(|con k (many d1)|, |con k (many d2)|) ∈ R_{|x|,|a|}}$. \\
        We have shown that |apply| is compatible with $R_{|x|,|a|}$, and |foldl|
        is so as well by parametricity.
        The field denotations |many d1| and |many d2| satisfy $R_{|x|,|a|}$ by
        assumption; hence to show the goal it is sufficient to show that
        $(|MkUT emp (Rep Uω)|, |MkUT emp (Rep Uω)|) ∈ R_{|x|,|a|}$.
        And that follows by reflexivity since |emp ?! x = U0|.

      \item \textbf{Case |select|}.
        Goal: $\inferrule{(|d1|,|d2|) ∈ R_{|x|,|a|} \\ (|fs1|,|fs2|) ∈ |Tag :-> ([Rxa] -> Rxa)|}{(|select d1 fs1|, |select d2 fs2|) ∈ R_{|x|,|a|}}$. \\
        Similar to the |con| case, large parts of the implementation are
        compatible with |Rxa| already.
        With $(|MkUT emp (Rep Uω)|, |MkUT emp (Rep Uω)|) ∈ R_{|x|,|a|}$ proved
        in the |con| case, it remains to be shown that |lub :: [UD] -> UD| and
        |(>>) :: UD -> UD -> UD| preserve |Rxa|.
        The proof for |(>>)| is very similar to but simpler than the |apply|
        case, where a subexpression similar to |MkUT (φ1 + φ2) b| occurs.
        The proof for |lub| follows from the proof for the least upper bound
        operator |⊔|.

        So let |(l1,l2), (r1,r2) ∈ Rxa| and show that |(l1 ⊔ r1, l2 ⊔ r2) ∈ Rxa|.
        The assumptions imply that |l1^.v ⊑ l2^.v| and |r1^.v ⊑ r2^.v|, so
        |(l1 ⊔ r1)^.v ⊑ (l2 ⊔ r2)^.v| follows by properties of least upper bound operators.

        Let us now consider the |Uses| component.
        The goal is to show
        \begin{spec}
          (l1 ⊔ r1)^.φ ⊑ (let MkUT φ v = l2 ⊔ r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)^.φ
        \end{spec}

        For the proof, we need the algebraic identity |forall a b c d. a + c ⊔
        b + d ⊑ a ⊔ b + c ⊔ d| in |U|.
        This can be proved by exhaustive enumeration of all 81 cases; the
        inequality is proper when |a = d = U1| and |b = c = U0| (or vice versa).
        Thus we conclude the proof:
        \begin{spec}
          (l1 ⊔ r1)^.φ = l1^.φ ⊔ r1^.φ
        =  {- By assumption, |l1 ⊑ apply (abs x l2)| and |r1 ⊑ apply (abs x r2)|; monotonicity -}
          (ext (l2^.φ) x U0 + (l2^.φ !? x) * a^.φ) ⊔ (ext (r2^.φ) x U0 + (r2^.φ !? x) * a^.φ)
        ⊑  {- Follows from |forall a b c d. a + c ⊔ b + d ⊑ a ⊔ b + c ⊔ d| in |U| -}
          (ext (l2^.φ) x U0 ⊔ ext (r2^.φ) x U0) + ((l2^.φ !? x)*a^.φ ⊔ (r2^.φ !? x)*a^.φ)
        =  {- |ext φ1 x U0 ⊔ ext φ2 x U0 = ext (φ1 ⊔ φ2) x U0| -}
          ext ((l2 ⊔ r2)^.φ) x U0 + ((l2 ⊔ r2)^.φ !? x) * a^.φ
        =  {- Refold |MkUT φ v| -}
          (let MkUT φ v = l2 ⊔ r2 in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v)^.φ
        \end{spec}

      \item \textbf{Case |bind|}.
        Goal: $\inferrule{\forall (|d1|,|d2|) ∈ R_{|x|,|a|} \implies (|f1 d1|, |f2 d2|), (|g1 d1|, |g2 d2|) ∈ R_{|x|,|a|}}{(|bind f1 g1|, |bind f2 g2|) ∈ R_{|x|,|a|}}$. \\
        By the assumptions, the definition |bind f g = g (kleeneFix f)|
        preserves |Rxa| if |kleeneFix| does.
        Since |kleeneFix :: Lat a => (a -> a) -> a| is parametric, it suffices
        to show that the instance of |Lat| preserves |Rxa|.
        We have already shown that |⊔| preserves |Rxa|, and we have also shown
        that |stuck = bottom| preserves |Rxa|.
        Hence we have shown the goal.

        In \Cref{sec:usage-analysis}, we introduced a widening operator
        |widen :: UD -> UD| to the definition of |bind|, that is, we defined
        |bind rhs body = body (kleeneFix (widen . rhs))|.
        For such an operator, we would additionally need to show that |widen|
        preserves |Rxa|.
        Since the proposed cutoff operator in \Cref{sec:usage-analysis} only
        affects the |UValue| component, the only proof obligation is to show
        monotonicity:
        |forall d1 d2. d1^.v ⊑ d2^.v ==> (widen d1)^.v ⊑ (widen d2)^.v|.
        This is a requirement that our our widening operator must satisfy anyway.
    \end{itemize}
\end{itemize}

This concludes the proof that $(|f a|, |f (pre x)|) ∈ R_{|x|,|a|}$.
What remains to be shown is that this implies the overall goal
|f a ⊑ apply (fun x f) a|:
\begin{spec}
  (f a, f (pre x)) ∈ Rxa
<==>  {- Definition of |Rxa| -}
  f a ⊑ let MkUT φ v = f (pre x) in MkUT (ext φ x U0 + (φ !? x) * a^.φ) v
<==>  {- refold |apply|, |fun| -}
  f a ⊑ apply (fun x f) a
\end{spec}
\end{proof}
