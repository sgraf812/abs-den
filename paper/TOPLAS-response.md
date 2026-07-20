We thank the Associate Editor and the three referees for the care and patience
they brought to a demanding manuscript. The reviews converge on two themes:
(1) accessibility of the key ideas, and (2) the status and checkability of the
mechanised results. This revision responds to both. Below we summarise the major
changes and then answer each comment in turn, giving the location in the revised
manuscript. Section numbers refer to the revised paper.

## Summary of major changes

1. **A complete Lean/Iris mechanisation replaces the partial Agda encoding
   (new Section 6).**
   The submitted version proved totality by a separate
   Guarded Cubical Agda re-encoding that reviewers could not type-check. We have
   replaced it with a single Lean 4 development on `iris-lean` (using Iris' base
   logic, but not its weakest-precondition program logic) that mechanises the
   entire by-need story: the generic interpreter, adequacy against the lazy
   Krivine machine, and the soundness of usage analysis, culminating in a
   machine-checked absence theorem: a variable that the analysis reports unused
   is never looked up during by-need evaluation. The theorem depends on Lean's
   standard axioms alone. The Lean toolchain and the `iris-lean` commit are
   pinned (Section 6, footnote), so the artefact type-checks from the recorded
   manifest. The guarded-recursive interpreter **remains executable**: the
   example traces and analysis results in the paper are `#guard`-checked during
   the build, using compiled extraction through `implemented_by`.

2. **The paper is focused on one worked analysis.**
   The gentle absence-analysis introduction ("The Problem We Solve"), the
   Hindley-Milner type analysis, the 0CFA control-flow analysis, and GHC's
   Demand Analysis have been removed. The paper develops usage analysis end to
   end, and has no appendix.

3. **Generality claims are scaled back**
   A dedicated "Scope and Limitations" subsection (Section 5.5) states which
   analyses the framework reaches and how the pattern relates to other
   paradigms.

4. **The abstract-interpretation positioning is strengthened.**
   The central soundness statement in Section 5.1 is now given as three
   equivalent readings: a sound abstract interpretation, a step-indexed logical
   relation, and a preservation proof. We added the soundness-vs-completeness
   connection (Giacobazzi & Ranzato, POPL 2025) and positioned the framework
   against Cousot's generic abstract interpreter (Section 7). Cousot's bi-inductive
   trace semantics is first-order; our guarded-domain construction lifts it to the
   higher-order case (Section 8).

---

## Associate Editor

> Clear high-level explanation of the baseline semantics is needed.

The interpreter now carries an explicit operational reading in Section 2: the
behaviour of a subexpression is what happens when it is the expression under
evaluation, closed by an environment and placed in an evaluation context (the
CIU/context-lemma property Referee 3 asked for). We deliberately keep the
by-name instance as the first one the reader meets, so the interpreter can be
understood before the stateful by-need domain; see our reply to Referee 3.
We added example walkthroughs to both the by-name and by-need instances.

> Better positioning w.r.t. analyses beyond those considered; clarify the type
> analysis and 0CFA, or scale back the claimed generality.

The extra analyses were removed, and Section 5.5 scales the generality claim
back to a (proof) design pattern for summary-based analyses rather than a
universal method.

> Missing connections to abstract interpretation, in particular completeness.

Section 5.1 gives the sound-abstract-interpretation reading; Section 4.2 shows the
most precise abstraction is non-computable; Section 7 relates this to Giacobazzi and
Ranzato on best abstractions.

> The Agda artifact must be provided in a checkable form (versions/libraries).

Addressed by the change to Lean (major change 1). The toolchain and dependency
commit are pinned; the development type-checks from the manifest and is
executable.

---

## Referee 1

> The general description of the approach (l. 277-293) could be given earlier.

Done; this framing now opens the introduction.

> The claimed simplicity is not conveyed; the method uses sophisticated tools
> (Löb induction, totality by re-encoding in Agda, bisimulation, Theorems for
> Free), and I am not confident I could apply it to another analysis.

We have made two changes. First, the Agda re-encoding is gone; totality is now a
by-product of the mechanised productivity result (Section 6). Second, we are
more careful to claim the proofs are *simpler*, not *simple*, in the sense
we describe in Section 5.4.

> The typing analysis is too sketchy; leave it out or rewrite it.

Left out, as suggested.

> The paper cannot claim a general methodology while focusing on functional
> languages.

Agreed; Section 5.5 restricts the claim and discusses transfer to other
paradigms sharing higher-order mutable state.

> Section 2 (the simpler absence analysis) is not useful; consider removing it.

Removed. The paper develops usage analysis directly.

> Focus the article on usage analysis and develop it in detail.

Done; usage analysis is the single worked example across Sections 4-6.

> The proof sketch for the usage theorem hides details, and only one of the ten
> abstraction laws (Beta-App) is shown.

The whole development is now mechanised in Lean, including the abstraction laws.
We no longer claim unqualified simplicity, but show in what sense the proof is
simpler than a monolithic one (Section 5.4).

> Reconsider the appendices; some explanatory material (e.g. Appendix E) belongs
> in the main text.

The revised version has no appendix at all and should be self-contained.

> Appendix D.1's 0CFA has no correctness proof; is such a proof difficult?

The 0CFA analysis proof-of-concept has been removed.
If it is still of interest: a proof would first have required the 0CFA instance
to be totally definable (in Lean), which the experimental Haskell implementation
was not.

---

## Referee 2

> "Explosion of formal artefacts" is not clearly defined, and it conflates
> soundness (guaranteed by construction in abstract interpretation) with
> precision.

We reframed the problem concretely: the difficulty is the hand-crafted
step-indexed logical relation over machine configurations that a soundness proof
must build in one form or another, which is delicate in a higher-order setting
because the heap stores computations that refer back to the heap (introduction).

> Either formalise the whole construction in abstract-interpretation terms, or
> comment explicitly on soundness vs. completeness and cite Giacobazzi & Ranzato,
> "The best of abstract interpretations", POPL 2025.

We took the second route. Section 7 cites that work and states that we aim for
sound, computable abstractions rather than best abstractions; Section 5.1 gives
the abstract-interpretation reading of the soundness statement.

> The relation to Cousot's calculational design (1994, 2002) is underdeveloped.

Section 7 explains that Cousot's denotational setting did not obviously yield a
compositional, trace-generating semantics for a higher-order language, which is
what our interpreter provides.

> Moving away from abstract interpretation distances the work from a large
> literature.

We do not move away from abstract interpretation; we make it applicable. Our
framework supplies the higher-order, trace-generating semantics needed to reason in
abstract-interpretation terms in the first place, positioned against Cousot's generic
abstract interpreter, with the three-readings account in Section 5.1.

---

## Referee 3

> The presentation over-emphasises parameterisation; commit to one interpretation
> (call-by-need) and explain the baseline semantics (every machine expression is
> a subexpression of the program; the CIU / context-lemma property) before the
> layers of generalisation.

Partly addressed, partly a considered decision. The operational reading,
including the context-lemma property, is now in Section 2, and the subexpression
property is manifest: a compositional interpreter only ever evaluates
subexpressions. We keep the by-name instance as the reader's first contact, so the
compositional-yet-operational idea lands before the stateful by-need domain; the
mechanisation and soundness commit to by-need throughout.

> The motivating difficulty is a straw man; progress-and-preservation already
> links compositional analyses to non-compositional semantics, and Gustavsson
> extended type systems to abstract-machine configurations for usage analysis.

The preservation reading is now one of the three readings of our soundness
statement (Section 5.1), so we position the work alongside progress-and-preservation,
not against it. Gustavsson (and, much later, Sergey) extends the analysis's type
system over whole machine configurations (heaps, stacks, update markers), which is
bespoke, per-analysis machinery. Our decomposition avoids it: the coupling to machine
configurations, stack and heap, is discharged once in the by-need adequacy proof, and
everything after relates denotations and how they reduce. Section 5.4 summarises the
reusable layers of our proof.

> Haskell is a double-edged sword; add an informal unwinding of the Section 4.2
> definitions and types.

Section 2 (previously 4) adds an operational reading of the interpreter and its
combinators to complement the Haskell.

> Little guidance on instantiating the semantic domain "correctly" (so the laws
> of Fig. 13 hold).

The informal side conditions of the laws ("f polymorphic", "x fresh") are made
precise in Section 6.4, and Section 5.1 states the obligation crisply: supply the
abstraction laws and soundness follows.

> Remove the running example.

Done.

> Can you compare precision on concrete examples? Does it behave well?

We compare the analysis result to specific runs of the semantics and show up its
strengths and imprecisions in Section 4 (the first-order summary cannot see through an indirect call,
Section 4.3). Section 4.4 brings a non-trivial fixpoint example.
We do not claim that usage analysis is novel or uniquely precise.
We sought an analysis that is simple enough to explain the problem and demonstrate
the proof complexity.

> The supplied Agda code does not type-check with current libraries; documentation
> is lacking.

Addressed by the change to Lean with pinned versions (major change 1).

> The intended optimisation (e.g. a "garbage collect x in e" construct) and its
> interaction with usage data are not modelled.

Out of scope, and noted as such (Section 5.5). We prove the semantic property (a
reported-unused variable is never looked up); wiring it to a concrete optimisation is
standard and orthogonal.

> The untyped analysis framework uses clumsy, necessarily infinite argument
> summaries.

The infinite summaries are forced by recursive types, which nearly every
practical language has; the finite-arity alternative exists only in their absence.
We also make explicit that the usage summary is a *usage type* and `evalUsg` a
type-based analysis (Section 4.3), the view taken by earlier type systems for
usage and sharing.

> State the limitations; are there analyses forced into ad-hoc proof methods?

Section 5.5 states the limitation directly: we expect few analyses beyond usage
analysis to satisfy the laws unchanged, and a different source language may need a
different domain.

> Given Theorem 6 shows usage analysis over-approximates the abstraction alpha_S,
> could one simply use alpha_S as the analysis?

No: alpha_S is the abstraction of the concrete by-need trace and is not
computable (it would require running the program). The analysis is the
computable abstract interpreter evalUsg, whose least fixpoint terminates
(Section 4.4); alpha_S is the ideal it approximates.

> The abstract mentions a logical relation that does not appear in the body; and
> logical relations are usually type-indexed.

The logical relation is now explicitly mentioned in the body: Section 5.1 gives the
step-indexed logical-relation reading, and Section 6 builds it as `LR2`. On
type-indexing: the object language is untyped, yet this is a genuine logical
relation, with Löb induction on the step index in the role that induction on type
structure ordinarily plays (Section 5.1).

> Minor points (Fig. 1's A looks partial; cbname in 4.2 vs 4.3.1; why Event
> changes for cbv; productivity of the generic vs. specific interpreter; source
> of imprecision on p. 18).

The absence analysis of Fig. 1 was removed together with its section, so the
partiality of A no longer appears. Productivity is clarified by the mechanised
productivity result (Section 6): it is a property of a concrete instantiation, not of
the generic interpreter. The source of imprecision in the example formerly on p. 18
is now explained where the example appears (Section 4.3): the first-order summary
cannot see through an indirect call. A more potent summary mechanism encoded in the
domain definition could improve this; it has nothing to do with the interpreter pattern.
The duplication between old Sections 4.2 and 4.3.1 is gone: the revised
interpreter section defines a single by-name domain (`DName = T Value`),
without the `ByName` wrapper. On `Event`: Section 2 now states that the choice
of `Event` is use-case specific, spanning a spectrum of operational detail;
the events name the machine transitions a strategy makes observable (by-need
adds `Upd` for its update transition), while the generic interpreter itself is
unchanged.
