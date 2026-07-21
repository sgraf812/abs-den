# Abstracting Denotational Interpreters: Lean mechanisation

This repository mechanises the denotational interpreter, the usage analysis, and
the by-need soundness and adequacy results of the paper *Abstracting
Denotational Interpreters* in Lean 4, on top of `iris-lean`, the Lean port of the
Iris separation-logic framework. It backs the paper's Section "Mechanisation in
Lean". This file maps the paper's results to their Lean declarations.

- Toolchain: Lean `v4.31.0`; `iris-lean` pinned at commit `18e9020`, fetched by
  `lake` from `lake-manifest.json`. These are the versions named in the section
  footnote.
- 27 modules, roughly 12k lines.
- `sorry`-free.

## Building and checking

Install `elan`, the Lean version manager (`github.com/leanprover/elan`, or
`curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`), then:

```
lake build
```

`elan` reads `lean-toolchain` and fetches Lean `v4.31.0` on first use; `lake`
fetches `iris-lean` (pinned at `18e9020`) and its dependencies from the manifest
and compiles them from source, so the first build is slow.

The build elaborates every proof and runs the `#guard` example checks described
under "The Interpreter Still Runs": the example traces of Section "A Denotational
Interpreter" and the analysis results of Section "Usage Analysis", each agreeing
with the LK machine up to silent steps.

`#print axioms absence`, in any file that imports `AbsDen.Absence`, reports
`propext`, `Classical.choice`, and `Quot.sound`. Execution goes through
`implemented_by` shims for the domain isomorphism and the guarded fixpoint; these
replace compiled code only, so the proofs are unaffected.

## Paper results to Lean

`usage_approximates_need` (`Absence.lean`) is the Prop-valued statement: for a
Barendregt program `e`, at every variable `x` and prefix length `n`, the lookups
of `x` in the first `n` steps of the by-need trace, abstracted into a usage
cardinality, are bounded by the usage the analysis reports for `x`. It mentions
only the by-need semantics and the analysis, so it unfolds to a statement over
the operational trace. `absence` (`Absence.lean`) is its `U0` corollary: a binder
the analysis reports unused is never looked up. Both are the empty-heap reading
of the logic-level `usage_abstracts_need` (`NeedSound.lean`).

| Paper | Lean name | Module |
| --- | --- | --- |
| Usage approximates need, Prop level | `usage_approximates_need` | `Absence.lean` |
| Theorem "evalUsg infers absence": an unused binder is never looked up | `absence` | `Absence.lean` |
| Corollary "evalUsg1 abstracts evalNeed1", logic (UPred) level | `usage_abstracts_need` | `NeedSound.lean` |
| The binary logical relation and its structural induction (Section "A Logical Relation, Proved Once") | `structure LR2`, `LR2.fundamental` | `LR2.lean` |
| By-need soundness as an `LR2` instance (Theorem "Abstract By-need Interpretation"); the ghost-heap relation | `byNeed_sound`, `soundLR2`, `SoundR`, `HeapInv` | `NeedSound.lean` |
| The abstraction laws at the usage lattice | `usageAbstractionLaws`, `AbstractionLaws` | `UsageLaws.lean`, `Soundness.lean` |
| The finite-height usage domain and its interpreter (Section "Finite Height, and Where Completeness Enters") | `UDk`, `evalUsgk` | `BoundedUsage.lean` |
| Adequacy against the LK machine (Section "A Logical Relation, Proved Once") | `need_abstracts_lk`, `need_abstracts_lk_init` | `Adequacy.lean` |
| Productivity: at most one silent step between visible events | `productivity` | `Productive.lean` |
| The generic interpreter over any `Domain` OFE (Fig. "The Lean definition of eval") | `eval`, `class Domain` | `Semantics.lean` |
| At a discrete OFE, `eval` equals the direct interpreter | `evalConst_eq_eval`, `class AbstractDomain` | `AbstractDomain.lean` |
| The by-need interpreter (Section "The Guarded Domain") | `evalByNeed` | `ByNeed.lean` |
| Side condition `f` polymorphic, as parametricity (Section "The Side Conditions, Made Precise") | `ParametricLR`, `Exp.relTransport` | `ParametricLR.lean` |
| Side condition `x` fresh, as not observing a lookup of `x` | `Fresh`, `Exp.predTransport` | `ParametricLR.lean` |
| Side condition lexical scoping, as Barendregt well-scopedness | `Barendregt`, `Exp.Scoped` | `Syntax.lean` |

## Module map

- `Syntax.lean`, `OpSem.lean`: the expression language with `Barendregt`/
  `Exp.Scoped` well-scopedness, and the LK machine.
- `NonExpansive.lean`, `Env.lean`, `IrisExtensions.lean`: the non-expansiveness
  solver, environments as pointwise OFEs, and the OFE/COFE instances `iris-lean`
  lacks.
- `Trace.lean`, `FixImpl.lean`, `Domain.lean`, `ByNeed.lean`: the guarded
  by-need domain, its trace/value/heap functors, and the `Domain` instance.
- `Semantics.lean`, `AbstractDomain.lean`: the generic `eval` and the discrete
  collapse to the direct interpreter.
- `LR.lean`, `LR2.lean`, `ParametricLR.lean`, `NeedRel.lean`, `HeapAbs.lean`,
  `Safety.lean`: the logical relations and the ghost-heap camera.
- `Soundness.lean`, `NeedSound.lean`: the abstraction-law interface and by-need
  soundness.
- `UsesLattice.lean`, `UsageAnalysis.lean`, `BoundedUsage.lean`,
  `UsageLaws.lean`: the usage analysis, its finite-height truncation, and its
  abstraction laws.
- `Adequacy.lean`, `Productive.lean`: adequacy against the LK machine and
  productivity.
- `Absence.lean`: the Prop-level corollaries (`usage_approximates_need`,
  `absence`) and their extraction from the step-indexed logic.
- `SoundnessExamples.lean`: non-vacuity and tightness witnesses on concrete
  programs.
