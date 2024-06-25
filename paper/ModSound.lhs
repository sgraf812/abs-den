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

The exact details can again be found in the Appendix; here we give just the
seeding idea of how to apply parametricity to our setting.
The key to applying parametricity is to come up with the right relation.
For example, in \textsc{Beta-App} we need to show |forall x f a. f a ⊑ apply (fun x f) a|,
where |f :: (Trace d, Domain d, HasBind d) => d -> d|.
This type does not lend itself immediately to parametricity; however, in System $F$
every such |f| is semantically equivalent to a lambda |\a -> e| (where |a ::
d| is free in |e :: d|), so
|forall x e a. e ⊑ apply (fun x (\a -> e)) a| is an equivalent proposition.

More formally, let |PlainD| be an arbitrary type, $\mathit{inst} : |(Trace
PlainD, Domain PlainD, HasBind PlainD)|$ a type class dictionary, $x : |Name|$,
$a : |PlainD|$ arbitrary, but fixed.
Let $Γ \triangleq |PlainD|, \mathit{inst} : |(Trace PlainD, Domain PlainD,
HasBind PlainD)|, x : |Name|, a : |PlainD|$ a corresponding System $F$ context and $R ⊆
|PlainD| \times |PlainD|$ be the relation defined by
\[
  R(e_1, e_2) \triangleq e_1 ⊑ |inst|.|apply|~(|inst|.|fun|~x~(\fn{a}{e_2}))~a
\]
