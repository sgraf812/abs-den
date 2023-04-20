# Motivation

- Observe cardinality/control-flow (hence trace-based)
- Enjoy compositionality (nice proofs)
- Simple and compositional semantic framework
  (no Domain Theory necessary for new language features)
- Full abstraction (WHY?)

# Topics

- Prove full abstraction! Even better: I believe that in general one can show
  that the semantics is fully abstract wrt. to the observational equivalence of
  the transition system
- Apply to cardinality
- Apply to CFA. Call string/contour = Limited-depth approximation of Functional
  of RHS


# Related Work

* Read "A fully abstract trace-based semantics for reasoning about backward compatibility of class libraries"
* Read "Trace-Based Coinductive Operational Semantics for While"
* Read "Trace-based control-flow analysis" PLDI '21


# Structure

Introduction:
- Tension for program analyses: Structure vs. Observable Cardinality
- Compositionality, structural induction
- Domain Theory is non-compositional
- Full Abstraction might be nice

# Problem statement

- ...

# Deriving the semantics from "first principles"

## Evolve from a functional big-step semantics? / Why is it hard
```
eval env (Var x) = env(x)
eval env (App e x) = case eval env e of
  Lam y e' -> eval (env[y ↦ env(x)]) e'
eval env (Lam x e) = Lam x e
eval env (Let x e1 e2) =
  let env' = env[x↦eval env' e1]
  in eval env' e2
```
==> { Traces/Delay to encompass infinite behaviors }
```
data Delay a = Now a | Later (Delay a)
(|>) = Later
eval env (Var x) = |> env(x)
eval env (App e x) = |> (case eval env e >>= \(Lam y e') ->
  eval (env[y ↦ env(x)]) e')
eval env (Lam x e) = |> Lam x e
eval env (Let x e1 e2) =
  let env' = env[x↦eval env' e1]
  in |> eval env' e2
```

## Traces
- First problem: What is the target? stateful or stateless?
- If it is stateless:
  - Need to introduce quite a lot of stuff and intuition before even starting to
    build the "principles"!
- If it is stateful:
  - We will have a hard time to discuss a principle without talking about traces first
  - And our specification is *exactly* the principle! It doesn't make sense to go with less.
  - Can we make the specification simpler? Perhaps by doing substituion instead of carrying around an Env? I doubt it! Substitution destroys labels.
    Although we could adopt the approach of the PLDI '21 paper and regard a label as a wrapping around an expressoin...
