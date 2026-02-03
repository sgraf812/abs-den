# Embedding of the denotational interpreter into Guarded Cubical Agda

Checked using Agda 2.7.0.1.

This Agda development explores how to embed the concrete instantiations of the denotational interpreter into Guarded Cubical Agda.
Guarded Cubical Agda implements Ticked Type Theory, in which the `Later` modality `▹ A` has a special definition in terms of tick variables;
`▹ A = (α : Tick) → A`.

## Overview

We recommend to read the development in this order.
It may help to read the next section first in order to be able to map the development to the paper.

* `PartialFunction`: Defines partial functions `A ⇀ B` for heap and environment mappings in terms of `A → Mabye B`.
* `Later`: The "prelude" of Guarded Cubical Agda, copied from ["the example"](https://github.com/agda/agda/blob/a16a0399438f71c910ee1db86f673f780d12a393/test/Succeed/LaterPrims.agda).
  Defines guarded recursion `dfix` and its beta rule `pfix` as a postulate. Part of the trusted code base.
* `Syntax`: The syntax of the language from the paper.
* `Semantics`: The denotational interpreter and the type class definitions (`Trace`, `Domain`, `HasBind`) necessary to define it.
* `Concrete`: The instances for by-name and by-need, defining the instances for `Trace`, `Domain` and `HasBind`
  in order to finally "run" the interpreter on a small example.

## Adjustments compared to the Haskell definition of the paper

Compared to the Haskell definition of the paper, we make the following adjustments to the interpreter and its type class algebra:

* We need to delay in `step` using the `Later` modality `▹`; thus its definition
  in `Trace` changes to `step :: Event → ▹ d → d`.
* All `D`s that will be passed to lambdas, put into the environment or
  stored in fields need to have the form `step (Look x) d` for some
  `x::Name` and a delayed `d :: ▹ (D τ)`.
  This is enforced as follows:
  1. The `Domain` type class gains an additional predicate parameter `p :: D → Set`
     that will be instantiated by the semantics to a predicate that checks
     that the `D` has the required form `step (Look x) d` for some
     `x::Name`, `d :: ▹ (D τ)`.
  2. Then the method types of `Domain` use a Sigma type to encode conformance
     to `p`.
     For example, the type of `fun` changes to `(Σ D p → D) → D`.
  3. The guarded recursive data type `Value` has a constructor
     `Fun :: (Name × ▹ (D τ) → D τ) → Value τ`, breaking the
     previously discussed negative recursive cycle by a `▹`, and
     expecting `x::Name`, `d::▹ (D τ)` such that the original `D τ` can
     be recovered as `step (Look x) d`.
     This is in contrast to the original definition `Fun :: (D τ → D τ) → Value τ`
     which would *not* type-check.
     The concrete `Domain` implementation then translates between `Σ D p`
     and `Name × ▹ (D τ)`, essentially defunctionalising the latter into
     the former.
* Expectedly, `HasBind` becomes more complicated because it encodes the fixpoint
  combinator. We settled on `bind :: ▹ (▹ D → D) → (▹ D → D) → D`.
  We tried rolling up `step (Look x) _` in the definition of `eval` to get a
  simpler type `bind :: (Σ D p → D) → (Σ D p → D) → D`, but then had
  trouble defining `ByNeed` heaps independently of the concrete predicate `p`.
* Higher-order mutable state is among the classic motivating examples for
  guarded recursive types. As such it is no surprise that the state-passing of
  the mutable `Heap` in the implementation of `ByNeed` requires breaking of a
  recursive cycle by delaying heap entries, `Heap D = Addr ⇀ ▸ D`.
* We need to pass around `Tick` binders in `eval` in a way that the type
  checker is satisfied.

## Trusted postulates

The by-name embedding of the interpreter is completely free of postulates, thus
trusting that it is a sound mathematical definition amounts to trusting that the
logic checked by Guarded Cubical Agda is sound.

For by-need, there we need to disclose two postulates with corresponding
postulated beta rules.

The first one concerns "well-addressedness". Heaps are modeled by partial
functions, so accessing an address may fail to find an entry. We did not bother
trying to formalize that every heap access finds an entry, so we postulate this.
We think it is clear how to get rid of this postulate, but it requires the usual
amount of effort.

The second postulate concerns an issue with the implementation of `fetch addr`,
which fetches a semantic element from the heap in the current state at address
`addr`. At every use site of `fetch addr`, we have a surrounding `step (look x)
: ▹ D → D` that does not modify the heap. However, `▹ D` is effectively
`(α : Tick) → (μ : Heap (next D)) → T (Value τ × Heap (next D))` and
because `α` occurs before `μ`, the tick calculus does not allow to apply `α`
to the delayed semantic element `μ addr : ▹ D`. Indeed, in general this would
be unsound. But in our situation, `step` could actually pass `μ` *before* `α`,
because `μ` is unchanged. We express this with a postulate `flip-tick : ∀ {A
B : Set} → (A → ▹ B) → ▹ (A → B)` with the corresponding beta rule,
acknowledging that this primitive is unsound in general but safe in the way we
use it.

One way to get rid of this latter postulate would be to specialise the
interpreter for by-need domains, meaning that we pass an additional heap `μ` as
argument. This effectively swaps the order of `α` and `μ` in the type of `step
(look x) : (μ : Heap (next D)) → (α : Tick) → T (Value τ × Heap (next
D))` and all will be well. The drawback of this is that it is no longer the same
interpreter as for by-name, but it is the trade-off we recommend doing for a
serious formalisation project.

We have explored a number of ways to get rid of this second postulate without
specialising the interpreter, ultimately to no avail.
