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

## Evolve from a functional big-step semantics? / Why is it hard

WHY START FROM BIG STEP? We already said we wanted structural induction

(Our calculus does not meaningfully support syntactic substitution because
applications only allow variable args. So we delay substitution until the
Var case and need closures.)
Thinking about just call-by-need for now and thinking just about well-scoped
programs (e.g., never get stuck), so we simply assume that Env is total
```
type Env = Var -> Clo
data Clo = C Env Expr
uncurry f (a,b) = f a b
eval :: Env -> Expr -> Val
eval env (Var x) = uncurry eval env(x)
eval env (App e x) = case eval env e of
  (env', Lam y e') -> eval (env'[y ↦ env(x)]) e'
eval env (Lam x e) = Lam x e
eval env (Let x e1 e2) =
  letrec env' = env[x↦(env',e1)]
  in eval env' e2
```
==> { Traces/Delay to encompass infinite behaviors }
```
data Delay a = Now a | Later (Delay a)
(|>) = Later
eval :: Env -> Expr -> Delay Val
eval env (Var x) = |> uncurry eval env(x)
eval env (App e x) = |> (case eval env e >>= \(Lam y e') ->
  eval (env[y ↦ env(x)]) e')
eval env (Lam x e) = |> Now (Lam x e)
eval env (Let x e1 e2) = |>
  letrec env' = env[x↦(env',e1)]
  in eval env' e2
```
This is easily verified to be a total function defined by guarded recursion.
But this is not a definition by structural induction on e.
In particular, recursing into the substitutee in the var case is never going to work.
Also, the recursion in the application case doesn't work.
We can fix (1) by storing `eval env' e1` in the `env` instead of `(env',e1)`.
And (2) by changing the notion of value from a syntactic one to a semantic one, like
this:
==> { Denotations }
```
data Value = V (Delay Value -> Delay Value)
type D = Delay Value
eval :: (Var -> D) -> Expr -> D
eval env (Var x) = |> env(x)
eval env (App e x) = |> (case eval env e >>= \(V f) -> f (env(x)))
eval env (Lam x e) = |> Now (V (\d -> eval env[x↦d] e))
eval env (Let x e1 e2) = |>
  let env' = env[x↦eval env' e1]
  in eval env' e2
```
And now we recurse in all the right places.

This is the gist of what this paper sets out to do, ironing out subleties such as:
- An extension of the notion of coinductive datatypes and guarded recursion that allows
  for datatypes with negative recursive occurrences such as `Value`
- Elaborating the semantics to generate (potentially stuck) traces, and proving
  that those traces correspond to the maximal small-step traces of the expression
- Accommodate memoisation for call-by-need in this stateful trace semantics
- Refining the semantics into a stateless one
- Applying the semantics to usage analysis as well as control-flow analysis, and
  perhaps type soundness


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
