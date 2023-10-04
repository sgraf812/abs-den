# Structure

## Introduction

- Start by pointing out the structural mismatch problem, and how denotational
  semantics is useful to formalise a bunch of practically relevant analyses
  (DONE)
- After AAM, stress the
  development on Abstract Definitional Interpreters more and say why it is not
  an option.
    + (Later: There exist **coinductive big-step semantics** that are equally expressive
      as small-step semantics (eg, they distinguish divergence from stuckness))
    + **Abstracting Definitional interpreters** offers a recipe to derive
      sound analysis from a shared definitional interpreter based on such a
      big-step semantics
    + (Perhaps later: There are even Definitional interpreters such as the meta-circular one
      by Reynolds and the one by Ager are structurally defined, we call these
      **Denotational Interpreters**...)
    - ... but the meta language is not total. Often, such interpreters loop
      indefinitely for non-terminating programs.
      Proving totality of the concrete interpreter is a massive undertaking.
      The problem is exacerbated for denotational interpreters due to
      higher-order functions.
      Thus, these definitional interpreters are no replacement for a formal
      semantics.
- Our Solution:
  - A specific class of Definitional Interpreters we call *Denotational Interpreter*,
    definable in a total language
    with guarded recursive types such as Guarded Cubical Agda.
    Denotational interpreters produce potentially infinite traces that are
    adequate wrt. a standard small-step operational semantics.
  - Through our final encoding of traces and values, this definitional
    interpreter enjoys a variety of concrete and abstract interpretations
    in the sense of Cousot and ADI.

## Problem

- 2.1 Usage analysis
- 2.2 Simple proof of correctness, both of analysis and transformation
- 2.3 Divergence, Safety properties (divergence = ⊥ means observe safety properties)
- 2.4 Operational detail
- 2.5 Structural mismatch for oeprational semantics -- Lacks a strong argument!!
      Esp. given what the proofs ultimately looked like. Much the same as
      for OpSem, I think, because we abandoned trace equivalence in favor of
      contextual equivalence.
      With ADI and our approach, it is quite simple to show α(S[[e]]) computes
      an upper bound on the number of lookup transitions.
      It is *not* any simpler to prove improvement from that fact -- experience
      shows it's best to stick to operational semantics/improvement.
      Nothing gets simpler because we currently lack ergonomic equivalence relations
      that imply contextual improvement and equivalence.
-
