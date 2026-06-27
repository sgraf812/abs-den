# Abstracting Denotational Interpreters — Restructuring Handoff

Self-contained handoff so work can continue on another machine. The assistant's
per-machine memory lives in `~/.claude/.../memory/` and does **not** travel; this
file captures its substance plus the agenda and immediate plan. Lives in the repo
so it moves with git. Safe to delete once merged.

Paper: `~/code/tex/abs-den/paper`. Lean: `~/code/tex/abs-den/lean` (NOT
`~/code/lean/abs-den`). Repo root is `~/code/tex/abs-den` (git tracks `paper/`,
`lean/`, `agda/`).

---

## Conventions (hard rules)

- **No em-dashes (`---`) in paper prose.** Overuse reads as AI-authored. Recast
  with commas, parentheses, semicolons, or two sentences. When editing a passage,
  strip any pre-existing `---` you encounter. (The global rule already bans
  `--`/`—` in chat/comments/commits/PRs; Lean `--` comments are fine.)
- **British spelling** throughout: behaviour, summarise, optimisation,
  initialisation, artefact, generalise.
- **Never document a decision by contrasting with a rejected alternative.**
  Describe what exists, on its own terms. Say *what*, not *how*. No "current vs
  future" framing, no PR/issue refs in prose/comments.
- **Commits**: only when explicitly asked. Branch first if on `main`. Identity if
  unset: `-c user.email=sgraf1337@gmail.com -c user.name="Sebastian Graf"`. No
  `Co-Authored-By: Claude`, no "Generated with Claude Code".
- When working in `lean/`, never bundle `paper/` changes into a `lean: …` commit;
  stage paths explicitly.
- Do not commit the user's `lean/*` WIP as part of paper work.

## Build / verify

- Generate TeX: `LANG=C.UTF-8 lhs2TeX --poly -o abs-den.tex abs-den.lhs`
  (fast structural check; **does not** run `\perform`).
- Typecheck all modules: `make test` =
  `ghc -ihs -pgmL lhs2TeX -optL--pre -fno-code -W [A-Z]*.lhs`.
  (Typecheck only; does **not** catch missing `Show` instances or ambiguous
  `\perform` types — those bite when `\perform` actually evaluates.)
- `\perform{e}` is evaluated by a separate `lhs2TeX`/ghci pass (via the
  `%options ghci …` line); editing a module invalidates its cache and forces
  re-evaluation. The real arbiter is a full `make` (pdflatex).
- Proceedings vs extended: appendix material is `\begin{toappendix}` collected by
  `apxproof`; the proceedings PDF drops the appendix via the Makefile page split
  (`abs-den-main.pdf = cat 1-29`). Review/arXiv carry the appendix.

## Current document structure

`%include` order in `abs-den.lhs` (lines 207–214):
Introduction, Interpreter, OpSem, **StaticAnalysis, Adequacy**, Problem,
Soundness, RelatedWork. (Adequacy is largely a `toappendix` block, so it floats to
the appendix regardless of include position; verify section nesting since OpSem
holds the merged §3 `\section`.)

Reading order / key labels:
- §1 Introduction — `Introduction.lhs`.
- §2 `\section{A Denotational Interpreter}` `sec:interp` — `Interpreter.lhs`.
  - `sec:syntax`, `sec:dna` (Semantic Domain), `sec:by-need-instance`,
    walkthroughs `sec:walkthrough`/`sec:walkthrough-need`, `sec:lazy-init`.
- §3 `\section{Reference Semantics and Adequacy}` — `OpSem.lhs` holds the
  `\section` + goal header + LK machine `sec:op-sem` (`fig:lk-semantics`,
  `fig:eval-correctness` with `α_Events`); `Adequacy.lhs` continues with the
  bisimulation/totality proofs (`sec:adequacy`, `sec:totality`, mostly appendix).
- §4 `\section{Usage Analysis}` `sec:abstraction` **and** `sec:usage-analysis`
  (both labels on the one section) — `StaticAnalysis.lhs`.
  - §4.1 Usage Cardinality and Absence (`defn:absence` lives here now).
  - §4.2 Trace Abstraction in `UT` (`sec:usage-trace-abstraction`,
    `fig:usage-analysis`, `fig:lat`).
  - §4.3 Value Abstraction and Summarisation (`fig:usage-trace` walkthrough).
  - §4.4 Finite Fixpoint Strategy and Totality (`sec:usage-fixpoint`).
  - Appendix (extended version, unlinked from main text): `sec:type-analysis`,
    `sec:0cfa`, `sec:annotations`, `sec:demand-analysis` + their figures.
- `Problem.lhs` `sec:problem` — **being killed** (scavenge source, still compiled).
- §5/§6 Soundness `sec:soundness`, RelatedWork `sec:related-work`.

---

## Key decisions made (the "why")

1. **Scope narrowed**: the paper introduces the *denotational-interpreter pattern*
   and proves soundness for **one** targeted analysis, **usage analysis**, with
   **absence** (a `U0`/never-looked-up variable) as the semantic correctness
   property. Type analysis, 0CFA, and GHC's Demand Analysis are *generality
   evidence*, not co-equal results.
2. **Other analyses kept in the appendix but unlinked**: no `\Cref` from the main
   text into `sec:type-analysis`/`sec:0cfa`/`sec:annotations`/`sec:demand-analysis`.
   The §4 intro states they live "only in the extended version of this paper." So
   the main text reads identically with or without the appendix. (This reversed an
   earlier idea to delete them / make Demand its own publication immediately;
   Demand may still get a dedicated paper later, but its rough version stays in the
   appendix.)
3. **Kill the Problem section** (`Problem.lhs`): scavenge its hard-won prose, then
   delete. `defn:absence` already re-homed into §4. Problem still holds insight to
   reuse deliberately (summaries/modularity, the soundness-difficulty exposition,
   AI/logical-relations/preservation in `sec:ai-lr-pres`) — do NOT blind-delete;
   git preserves it regardless.
4. **`eval` `Let` case changed** (by the user): `step Let1` now wraps the whole
   `bind` (uniform with `App1`/`Case1`), instead of sitting inside the body
   continuation. Observationally neutral for by-name/by-need (allocation emits no
   `Step`); the adequacy/bisimulation proofs are unaffected because they compare
   trace *values* and `αSTraces` attaches no heap to a `Step`. The Soundness
   `Let`-case proof was updated.
5. **CBV `Let0` renamed to `Let2`**, emitted *before the body* in CBV/lazy-init
   `bind`, giving the trace bracket `Let1 … Let2`. (`\LetOT`→`\LetTT` in
   `macros.tex`.)
6. **Removed type classes**: `Trace` (its `step` is now in `Domain`) and `HasBind`
   (its `bind` is now in `Domain`). The old `D (ByName T)`/`D (ByNeed T)`
   transformer notation is a remnant: use `DName`/`DNeed` (= `T Value` /
   `TNeed ValueNeed`), and `TNeed` for the by-need newtype wrapper.
7. **§4.3 rewritten** around a single end-to-end example
   (`let k = λy.λz.y in k x₁ x₂`), explaining `fun`/`apply`/`peel`/summary *in
   passing* rather than as a separate up-front exposition. "Summary" is defined at
   first use. `ρe` is explained where it appears.

## Status: done this session

- §2: by-need τ-derivation compressed; novelty paragraph removed; `Let`-case
  fixups across walkthroughs; CBV `Let0→Let2` rename + `bind` restructure; added
  `instance Show ValueValue`; `evalValue e ρ = eval e ρ :: DValue` (was
  polymorphic → ambiguous `\perform`).
- §3: `Trace`→`Domain`, `HasBind`→`bind`, `D (ByName/ByNeed T)`→`DName`/`DNeed`,
  `ByNeed`→`TNeed` remnants fixed in OpSem/Adequacy. Adequacy/bisimulation proofs
  verified unaffected by the `Let1` move.
- §4: renamed Static Analysis → Usage Analysis (both labels retained);
  subsubsections elevated to subsections; intro narrowed (generality → extended
  version, no appendix `\Cref`); absence intro enriched (usage cardinality, the
  "at most once not observable in a traditional denotational semantics" note,
  `Gustavsson:98`); `defn:absence` relocated from Problem; the 7 analogy sites
  decoupled from `fig:absence`; `fig:usage-trace` walkthrough added; §4.3 rewritten
  (single example); `kleeneFix` ordering fixed; em-dashes removed; fixes:
  behaviour, "at most 1 time", artefact, peeled; cite both
  `WrightBakerFinch:93,Gustavsson:98` in §1 and §4.
- Soundness: `Let`-case proof updated (the `bind` unfolding and the refold via
  `ByName-Bind` under `step Let1`/`Mono`); the `ByName-Bind` law itself unchanged.
- Intro: removed the `sec:problem`-deferring contributions bullet; defined/located
  "summary" via §4.3 (not deferred to the dying Problem).

---

## Agenda (broader roadmap)

1. **Reposition** the paper as pattern + one rigorous analysis (done structurally;
   keep prose aligned: Introduction, §4, contributions all tell the same story).
2. **Finish killing Problem**: scavenge, redirect refs, delete (see plan below).
3. **Appendix Agda→Lean migration**: `Adequacy.lhs` `sec:guarded-types` /
   `sec:totality-detail` still describe the *Agda* guarded-cubical encoding; the
   main-text claim is Lean. Port the encoding description (and ideally the
   development) to Lean. Larger task; deferred.
4. **Soundness exposition**: an "informal" soundness account precedes moving the
   big appendix proofs inline (apxproof currently auto-collects them).
5. **Related work**: cite `Backhouse:04` ("Safety of abstract interpretations for
   free…") as related-not-subsumed in `sec:related-work`.
6. **Demand Analysis** as its own future publication (the GHC case study). Its
   rough version stays in this paper's appendix for now.
7. **Final polish + review**: full `make`; then a cloud `/code-review ultra` /
   `ultrareview` pass on the branch (user-triggered).

## Immediate plan (ordered)

**A. Kill Problem.**
- Redirect / rephrase the `\Cref{sec:problem}` references (Problem is going away):
  - `Soundness.lhs`: lines 108, 419, 512, 863, 865, 905, 1010, 1019, 1023, 1034.
    Several compare the new modular proof to Problem's *preservation-style*
    framework (`thm:absence-subst`, `thm:preserve-absent`); decide per ref whether
    to drop the comparison or scavenge the needed statement into Soundness.
  - `Introduction.lhs`: line 116 ("a generalisation of absence analysis in
    `\Cref{sec:problem}`") → absence/usage now in §4; drop or repoint to
    `sec:abstraction`.
  - `Adequacy.lhs`: line 353 (`\Cref{sec:interp} and \Cref{sec:problem}`) → repoint.
- Absence machinery still defined in Problem and possibly needed elsewhere:
  `fig:absence` (Problem:69), `sec:absence` (24), `defn:abs-subst` (294),
  `fig:absence-ext` (572), plus `thm:absence-subst`/`thm:preserve-absent`. Move
  what survives into Soundness (or drop with the comparisons). `defn:absence` is
  already in StaticAnalysis (84) — keep that label.
- Then delete `Problem.lhs` and remove `%include Problem.lhs` (abs-den.lhs:212).
  **Only after** harvesting the prose worth reusing.

**B. Introduction contributions** — finish the reframe: type/0CFA/Demand as
"further instances … in the extended version" (no co-equal Demand contribution),
strip any remaining appendix `\Cref`, fix line 116.

**C. Stale remnants in `soundness-appendix.lhs`** (outside §4, not yet done):
lines 5, 169, 201, 259, 631, 765 mention `Trace`/`HasBind` instances and a
"`Trace`-derived" Galois connection. `Trace` merged into `Domain`, `HasBind`'s
`bind` is in `Domain` — update the dictionaries/captions accordingly.

**D. Verify structure**: confirm the OpSem/StaticAnalysis/Adequacy include order
nests correctly (OpSem owns the §3 `\section`; Adequacy is `toappendix`).

**E–G.** Agenda items 3 (Agda→Lean), 5 (`Backhouse:04`), 7 (full `make` + review).

---

## Cross-reference hazards / file notes

- `defn:absence` — defined in `StaticAnalysis.lhs:84`; referenced by Soundness.
  Keep the label when editing §4.
- `fig:absence`/`sec:absence`/`defn:abs-subst`/`fig:absence-ext` — still in
  `Problem.lhs`; main text (StaticAnalysis) no longer references `fig:absence`.
- `kleeneFix`/`lub` — defined in `fig:lat` (now in §4.2); used earlier in
  `fig:usage-analysis` `bind` and the §4.3 walkthrough (forward refs resolved by
  the figure move; the walkthrough no longer asserts the fixpoint *role*, deferring
  it to §4.4).
- `\perform` gotchas: an `eval*` alias must be monomorphic (e.g.
  `:: DValue`) or the `\perform` is ambiguous; the result type needs a `Show`
  instance. Both bit the by-value appendix this session.
- Citations: usage analysis cites both `WrightBakerFinch:93` and `Gustavsson:98`
  (in §1 and §4); "at most once" applications cite `Turner:95,Sergey:14`; absence
  rewrites cite `MoranSands:99` (contextual improvement).
