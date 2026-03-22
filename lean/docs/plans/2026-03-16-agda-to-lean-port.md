# Agda-to-Lean Port Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Port the guarded denotational interpreter from Guarded Cubical Agda to Lean 4, using a topos-of-trees model for the later modality, eliminating the flip-tick postulate via a lemma for constant presheaves.

**Architecture:** The topos of trees is modeled as presheaves over (ℕ, ≤). The Later modality, `next`, `dfix`, `fix` are defined by stage induction (Nat.rec). The generic interpreter is parameterized by type classes (Trace, Domain, HasBind) as in the Agda version. ByName and ByNeed are concrete instances. The flip-tick postulate is replaced by a provable lemma showing `(A → ▹B) ≅ ▹(A → B)` when A is a constant presheaf.

**Tech Stack:** Lean 4, Mathlib (category theory)

---

### Task 1: Initialize Lean 4 project with Mathlib

**Files:**
- Create: `lakefile.toml`, `lean-toolchain`, `AbsDen.lean`, `AbsDen/Syntax.lean`

Set up a standard Lean 4 project in `../lean` with Mathlib as a dependency.

### Task 2: Port Syntax

**Files:**
- Create: `AbsDen/Syntax.lean`

Port `Syntax.agda`: Var, Con, Exp, Alt, findAlt. Use Nat for Var/Con as in Agda.

### Task 3: Topos of Trees — Presheaf objects and Later modality

**Files:**
- Create: `AbsDen/ToposOfTrees.lean`

Define:
- `Psh`: presheaf objects as `(n : Nat) → Type` with restriction maps `r : obj (n+1) → obj n`
- `PshMor`: morphisms between presheaves
- `Later`: the later endofunctor `(▹A)_0 = Unit`, `(▹A)_{n+1} = A_n`
- `next : PshMor A (Later A)`
- `ap : PshMor (Later (A ⦥ B)) (Later A ⦥ Later B)` (applicative)
- `dfix : PshMor (Later A ⦥ A) (Later A)` — by Nat.rec
- `fix : ((n : Nat) → (Later A).obj n → A.obj n) → (n : Nat) → A.obj n`
- `pfix` (unfolding law): `dfix f = next (fix f)`

### Task 4: Topos of Trees — Constant presheaves and flip-tick lemma

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean`

Define:
- `Const : Type → Psh` — constant presheaf (all stages the same, identity restriction)
- `flipTick : ((s : Const S).obj n → (Later B).obj n) → (Later (Const S ⦥ B)).obj n` — the key lemma
- Prove this is an isomorphism (or at least construct the forward direction needed)
- Key insight: at stage 0 both sides are Unit; at stage n+1, LHS is `S → B_n`, RHS is `(S → B)_n` which for constant S is also `S → B_n`.

### Task 5: Port PartialFunction using HashMap

**Files:**
- Create: `AbsDen/Env.lean`

Replace association-list partial functions with `Std.HashMap Nat V` (since Var = Nat).
Define: `Env V := Std.HashMap Nat V`, lookup, update, bulkUpdate, pmapEnv.

### Task 6: Port Semantics — Type classes and generic interpreter

**Files:**
- Create: `AbsDen/Semantics.lean`

Port the type classes and interpreter:
- `Event` inductive
- `class Trace (D : Psh)` with `step : Event → PshMor (Later D) D`
- `class Domain (D : Psh) (p : ...)` with stuck, fun, apply, con, select
- `class HasBind (D : Psh)` with bind
- The generic interpreter `eval` using `fix` from ToposOfTrees

### Task 7: Port Concrete — T monad, Value, ByName

**Files:**
- Create: `AbsDen/Concrete.lean`

Port:
- `T` (trace monad): `inductive T (A : Type) | ret : A → T A | step : Event → ▹(T A) → T A`
  But in the presheaf model, this becomes stage-indexed.
- `Value`, `D` as guarded recursive types via the presheaf model
- `ByName` wrapper and its Trace/Domain/HasBind instances
- `evalByName`

### Task 8: Port Concrete — ByNeed with flip-tick lemma

**Files:**
- Modify: `AbsDen/Concrete.lean`

Port:
- `Heap`, `Addr`, `ByNeed` state monad
- `fetch` using the flipTick lemma instead of the postulate
- `memo`, `bindByNeed`
- `evalByNeed`
- Verify: no axioms needed beyond standard Lean/Mathlib

### Task 9: Verification and cleanup

- Run `#print axioms evalByName` and `#print axioms evalByNeed` to confirm no custom axioms
- Add a small test example (exp1 from the Agda code)
- Clean up imports
