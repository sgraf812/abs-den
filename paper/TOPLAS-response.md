# Response to Reviewers

**Manuscript:** TOPLAS-00007-2025, *Abstracting Denotational Interpreters*
**Decision:** Major revision

We thank the Associate Editor and the three referees for the exceptionally
careful reading. The reviews converge on two themes: (1) accessibility of the
key ideas, and (2) the status and checkability of the mechanised results. This
revision responds to both. Below we summarise the major changes and then answer
each comment in turn, giving the location in the revised manuscript. Section
numbers refer to the revised paper.

## Summary of major changes

1. **A complete Lean/Iris mechanisation replaces the partial Agda encoding
   (new Section 6).** The submitted version proved totality by a separate
   Guarded Cubical Agda re-encoding that reviewers could not type-check. We have
   replaced it with a single Lean 4 development on `iris-lean` (Iris' OFE / COFE
   / camera / UPred model) that mechanises the *entire* by-need story: the
   generic interpreter, adequacy against the lazy Krivine machine, and the
   soundness of usage analysis, culminating in a machine-checked *absence*
   theorem: a variable that the analysis reports unused is never looked up
   during by-need evaluation. The theorem depends on Lean's standard axioms
   alone; the unsafe execution shims replace compiled code only (Section 6.6).
   The Lean toolchain and the `iris-lean` commit are pinned (Section 6,
   footnote), so the artifact type-checks from the recorded manifest. The
   guarded-recursive interpreter **remains executable**: the example traces and
   analysis results in the paper are `#guard`-checked during the build.

2. **The main body is focused on one worked analysis.** The gentle
   absence-analysis introduction ("The Problem We Solve"), the Hindley-Milner
   type analysis, the 0CFA control-flow analysis, and GHC's Demand Analysis now
   live in the extended version. The main body develops usage analysis
   end to end.

3. **Generality claims are scaled back**, and a dedicated *Scope and
   Limitations* subsection (Section 5.5) states which analyses the
   framework reaches and how the pattern relates to other paradigms.

4. **The abstract-interpretation positioning is strengthened.** The central
   soundness statement is now presented, where it is stated (Section
   5.1), through three equivalent readings: a sound abstract interpretation, a
   step-indexed logical relation, and a preservation proof. We added the
   soundness-vs-completeness connection (Giacobazzi & Ranzato, POPL 2025) and
   explained why Cousot's calculational designs did not directly yield a
   trace-generating higher-order semantics (Section 7). A new Related Work
   subsubsection positions the mechanisation against certified abstract
   interpretation (Cachera & Pichardie; Verasco), constructive Galois
   connections (Darais & Van Horn), mechanised call-by-need and Call Arity
   (Breitner), and guarded denotational semantics (Paviotti & Møgelberg).

5. **The abstract now states** that the call-by-need results are mechanised in
   Lean using Iris and that the mechanised interpreter stays executable.

---

## Associate Editor

> Clear high-level explanation of the baseline semantics is needed.

The interpreter now carries an explicit operational reading in Section 2: the
behaviour of a subexpression is what happens when it is the expression under
evaluation, closed by an environment and placed in an evaluation context (the
CIU / context-lemma property Referee 3 asked for). We deliberately keep the
by-name instance as the first one the reader meets, so the interpreter can be
understood before the stateful by-need domain; see our reply to Referee 3.

> Better positioning w.r.t. analyses beyond those considered; clarify the type
> analysis and 0CFA, or scale back the claimed generality.

Both. The extra analyses moved to the extended version, and Section 5.5 scales
the generality claim back to a design pattern for summary-based analyses rather
than a universal method.

> Missing connections to abstract interpretation, in particular completeness.

Addressed. Section 5.1 gives the sound-abstract-interpretation reading
explicitly; Section 7 discusses best correct approximations and completeness
(Giacobazzi & Ranzato, POPL 2025) and positions the work against Cousot's
generic abstract interpreter (Def. 27.1 / Thm. 27.4).

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
careful to claim the proofs are *simpler*, not *simple*: what a new analysis must
supply is exactly the local abstraction laws (Section 5.1), and the fundamental
theorem that assembles them is proved once (Section 5.4). The use of the
"Theorems for Free" argument is isolated to a single law, App-Fun (Section 5.2).
Section 6.3 names the three layers of the decomposition as the three reusable
Lean artifacts; a new analysis supplies only its abstraction laws.

> The typing analysis is too sketchy; leave it out or rewrite it.

Left out of the main body (now in the extended version).

> The paper cannot claim a general methodology while focusing on functional
> languages.

Agreed; Section 5.5 restricts the claim and discusses transfer to other
paradigms sharing higher-order mutable state.

> Section 2 (the simpler absence analysis) is not useful; consider removing it.

Moved to the extended version. The main body develops usage analysis directly.

> Focus the article on usage analysis and develop it in detail.

Done; usage analysis is the single worked example across Sections 4-6.

> The proof sketch for the usage theorem hides details, and only one of the ten
> abstraction laws (Beta-App) is shown.

All abstraction laws are machine-checked for the usage domain in Lean (Section
6.3), and the two steps the referee suspected of hiding details are now precise:
the Theorems-for-Free argument is a mechanised parametricity condition,
discharged for every closure the interpreter produces (Section 6.4), and the
remaining laws follow by routine calculation (Section 5.3). App-Fun (formerly
Beta-App) is still the one law whose pen-and-paper proof we walk through,
because it carries the summary mechanism (Section 5.2). One step of Theorem 10
remains pen-and-paper: the passage from the machine-checked per-variable bound
to absence in every by-need evaluation context (the contexts are now defined in
Section 5.3); Section 6 states precisely which statements are machine-checked.

> Reconsider the appendices; some explanatory material (e.g. Appendix E) belongs
> in the main text.

The revised version has no appendix at all (the extended version keeps the
case-analysis proofs). Explanatory material moved into the body: the
abstraction-laws narrative (Section 5.1), the by-need evaluation contexts
(Section 5.3), and the proof-architecture discussion (Sections 5.4 and 6.3).

> Appendix D.1's 0CFA has no correctness proof; is such a proof difficult?

The 0CFA analysis is now in the extended version. The mechanisation targets
usage analysis; a correctness proof for 0CFA would proceed through the same
abstraction laws but is outside this paper's scope (Section 5.5).

---

## Referee 2

> "Explosion of formal artefacts" is not clearly defined, and it conflates
> soundness (guaranteed by construction in abstract interpretation) with
> precision.

We reframed the problem concretely: the difficulty is the hand-crafted
step-indexed logical relation over machine configurations that a conventional
by-need soundness proof must build, which is delicate because the heap stores
computations that refer back to the heap (introduction). The notion of *summary*
is defined precisely where usage summaries are introduced (Section 4).

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

We now position the framework against Cousot's generic abstract interpreter
(Def. 27.1, Thm. 27.4) and give the three-readings account in Section 5.1.

---

## Referee 3

> The presentation over-emphasises parameterisation; commit to one interpretation
> (call-by-need) and explain the baseline semantics (every machine expression is
> a subexpression of the program; the CIU / context-lemma property) before the
> layers of generalisation.

Partly addressed, partly a considered decision. The operational reading,
including the context-lemma property, is now in Section 2. The subexpression
property is manifest in the interpreter itself: being compositional, it only
ever evaluates subexpressions of the program. We chose, however, to keep the
by-name instance as the reader's first contact with the interpreter: it lets one
grasp the compositional-yet-operational idea without the stateful by-need domain,
which we found essential to a gentle exposition. The mechanisation and the
soundness development do commit to by-need throughout.

> The motivating difficulty is a straw man; progress-and-preservation already
> links compositional analyses to non-compositional semantics, and Gustavsson
> extended type systems to abstract-machine configurations for usage analysis.

The preservation reading is now one of the three explicit readings of our
soundness statement (Section 5.1), so we position the work alongside
progress-and-preservation rather than against it. Gustavsson's work is cited as
semantic ground truth (Section 3).

> Haskell is a double-edged sword; add an informal unwinding of the Section 4.2
> definitions and types.

Partly addressed. Section 2 adds an operational reading of the interpreter and its
combinators to complement the Haskell. We did not add the type-by-type unwinding of
the Section 4.2 definitions that the referee suggests.

> Little guidance on instantiating the semantic domain "correctly" (so the laws
> of Fig. 13 hold).

The informal side conditions of the laws ("f polymorphic", "x fresh") are made
precise in Section 6.4, and Section 5.1 states the obligation crisply: supply the
abstraction laws and soundness follows.

> Remove the running example.

Done (moved to the extended version).

> Can you compare precision on concrete examples? Does it behave well?

Section 7 gives a concrete comparison: a recursively defined identity applied
42 times, where usage analysis infers "used at most once" but k-CFA for k < 42
conflates the recursive activations of the inner binding. Section 4 additionally
runs the analysis on a series of examples, including two where it is imprecise,
and explains the source of the imprecision (the first-order summary cannot see
through an indirect call, Section 4.3). The nontrivial fixpoint computation the
referee asks for is the subject of Section 4.4.

> The supplied Agda code does not type-check with current libraries; documentation
> is lacking.

Addressed by the change to Lean with pinned versions (major change 1).

> The intended optimisation (e.g. a "garbage collect x in e" construct) and its
> interaction with usage data are not modelled.

Out of scope for this paper and noted as such (Section 5.5). We prove the
semantic property (a reported-unused variable is never looked up); wiring it to a
specific transformation and to garbage collection is future work.

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
finite-height abstract interpreter evalUsg, whose least fixpoint terminates
(Section 4.4); alpha_S is the ideal it approximates.

> The abstract mentions a logical relation that does not appear in the body; and
> logical relations are usually type-indexed.

The logical relation is now explicit in the body: Section 5.1 gives the
step-indexed logical-relation reading, and Section 6 builds it as `LR2`. On
type-indexing: the object language is untyped, yet this is a genuine logical
relation, with Löb induction on the step index in the role that induction on type
structure ordinarily plays (Section 5.1).

> Minor points (Fig. 1's A looks partial; cbname in 4.2 vs 4.3.1; why Event
> changes for cbv; productivity of the generic vs. specific interpreter; source
> of imprecision on p. 18).

The absence analysis of Fig. 1 is now in the extended version, so the partiality of
A no longer appears in the main body. Productivity is clarified by the mechanised
productivity result (Section 6): it is a property of a concrete instantiation, not of
the generic interpreter. The source of imprecision in the example formerly on p. 18
is now explained where the example appears (Section 4.3): the first-order summary
cannot see through an indirect call. We have not separately reworked the two
remaining exposition points in the interpreter section (the call-by-name instance
of old 4.2 versus 4.3.1, and the Event change for call-by-value).
