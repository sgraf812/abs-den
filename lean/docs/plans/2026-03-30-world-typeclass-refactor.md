# World Typeclass Refactor: From Structure to Typeclass with Tarski Universes

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace `structure World` (bundled family + restriction) with a typeclass `class World (F : Nat → Type)`, introduce a Tarski-style `Desc` universe for syntactic descriptions of worlds, and derive `LocalFunctor`/`World` instances structurally from `Desc`/`DescF`.

**Motivation:**
1. World combinators currently return `World` values, making it awkward to pattern-match on `D n` directly. With unbundled families, `D n` is just a type.
2. `LocalFunctor` instances are currently built by hand (see `T.Sig.localFunctor`, `Value.Sig.localFunctor`). With `Desc`/`DescF`, they are derived by structural induction on descriptions.
3. `SignatureFunctor` generates a `World` value (`Sig`) and an isomorphism. Renaming to `HasSignature` with `Desc` makes the bridge uniform and the derive handler simpler.

**Tech Stack:** Lean 4, Lake, Nix (`nix develop --command lake build AbsDen`)

**Universe decision:** The proposed refactor moves from `Sort u` to `Type`. This is justified because all concrete worlds in the codebase use `Type` (products, sums, functions between types). The only use of `Sort u` is `World.Const (S : Sort u)`, where `S` is always a `Type` in practice. Keeping `Type` avoids universe polymorphism headaches in `Desc.interp`.

---

## Phase 1: New Foundations (World.lean, top section)

### Task 1.1: Define `class World`

Replace the structure with a typeclass on families.

**Current:**
```lean
structure World where
  obj : Nat → Sort u
  restrict : {n : Nat} → obj (n + 1) → obj n
```

**New:**
```lean
class World (F : Nat → Type) where
  restrict : {n : Nat} → F (n + 1) → F n
```

Key changes:
- `Sort u` becomes `Type` (see universe decision above)
- The family `F` is the parameter, not a field
- `obj` disappears; clients write `F n` instead of `W.obj n`

Also add:
```lean
/-- `next` maps from `F n` to `Later.shift F n` using the world restriction. -/
def World.next [World F] {n : Nat} : F n → Later.shift F n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | _n + 1 => World.restrict
```

**Keep unchanged:** `Later.shift`, `Later.hmap`, `Later.map`, `Later.ap`, `giter`, `loeb`. These already work on `Nat → Sort u` / `Nat → Type` families and do not mention `World`.

### Task 1.2: Define combinators as defs on families

Each combinator becomes a `def` returning `Nat → Type`, plus a `World` instance.

```lean
def Sum' (A B : Nat → Type) : Nat → Type := fun n => A n ⊕ B n
def Prod' (A B : Nat → Type) : Nat → Type := fun n => A n × B n
def Const' (T : Type) : Nat → Type := fun _ => T
def Later' (A : Nat → Type) : Nat → Type := Later.shift A
def Function' (A B : Nat → Type) : Nat → Type := fun n => ∀ m, m ≤ n → A m → B m
def Comp' (G : Type → Type) [Functor G] (A : Nat → Type) : Nat → Type := fun n => G (A n)
```

Note: These names use a prime suffix during migration. Once the old `World` namespace is removed, they can take the original names. Alternatively, they can live in a `Fam` namespace: `Fam.Sum`, `Fam.Prod`, etc.

World instances for each:
```lean
instance [World A] [World B] : World (Sum' A B) where
  restrict | .inl a => .inl (World.restrict a) | .inr b => .inr (World.restrict b)

instance [World A] [World B] : World (Prod' A B) where
  restrict | (a, b) => (World.restrict a, World.restrict b)

instance : World (Const' T) where
  restrict := id

instance [World A] : World (Later' A) where
  restrict := World.next  -- uses A's restriction

instance [World A] [World B] : World (Function' A B) where
  restrict f m hm := f m (Nat.le_trans hm (Nat.le_succ _))

instance [Functor G] [World A] : World (Comp' G A) where
  restrict := Functor.map World.restrict
```

### Task 1.3: Define `Desc` and `Desc.interp`

```lean
inductive Desc where
  | unit   : Desc
  | empty  : Desc
  | sum    : Desc → Desc → Desc
  | prod   : Desc → Desc → Desc
  | later  : Desc → Desc
  | func   : Desc → Desc → Desc
  | const  : Type → Desc
  | comp   : (Type → Type) → [Functor inst] → Desc → Desc
```

Interpretation maps `Desc` to families:
```lean
def Desc.interp : Desc → (Nat → Type)
  | .unit       => Const' Unit
  | .empty      => Const' PEmpty
  | .sum a b    => Sum' a.interp b.interp
  | .prod a b   => Prod' a.interp b.interp
  | .later a    => Later' a.interp
  | .func a b   => Function' a.interp b.interp
  | .const T    => Const' T
  | .comp G a   => Comp' G a.interp
```

World instance for `Desc.interp` (by structural recursion):
```lean
instance : World (Desc.interp d) := by
  induction d with
  | unit => exact instWorldConst'
  | empty => exact instWorldConst'
  | sum a b iha ihb => exact @instWorldSum' _ _ iha ihb
  | prod a b iha ihb => exact @instWorldProd' _ _ iha ihb
  | later a ih => exact @instWorldLater' _ ih
  | func a b iha ihb => exact @instWorldFunction' _ _ iha ihb
  | const T => exact instWorldConst'
  | comp G a ih => exact @instWorldComp' G _ _ ih
```

### Task 1.4: Define `HasSignature`

```lean
class HasSignature (F : Nat → Type) where
  desc : Desc
  ofSig : {n : Nat} → desc.interp n → F n
  toSig : {n : Nat} → F n → desc.interp n
```

World instance from HasSignature:
```lean
instance [inst : HasSignature F] [World inst.desc.interp] : World F where
  restrict x := inst.ofSig (World.restrict (inst.toSig x))
```

Note: The `[World inst.desc.interp]` instance is always available from Task 1.3.

---

## Phase 2: DescF and LocalFunctor from Descriptions

### Task 2.1: Define `DescF` (open descriptions with a variable)

`DescF` describes a functor `(Nat → Type) → (Nat → Type)` syntactically:

```lean
inductive DescF where
  | unit   : DescF
  | empty  : DescF
  | var    : DescF            -- the recursive variable
  | sum    : DescF → DescF → DescF
  | prod   : DescF → DescF → DescF
  | later  : DescF → DescF
  | func   : DescF → DescF → DescF
  | const  : Type → DescF
  | comp   : (Type → Type) → [Functor inst] → DescF → DescF
```

Interpretation:
```lean
def DescF.interp : DescF → (Nat → Type) → (Nat → Type)
  | .unit, _      => Const' Unit
  | .empty, _     => Const' PEmpty
  | .var, X       => X
  | .sum a b, X   => Sum' (a.interp X) (b.interp X)
  | .prod a b, X  => Prod' (a.interp X) (b.interp X)
  | .later a, X   => Later' (a.interp X)
  | .func a b, X  => Function' (a.interp X) (b.interp X)
  | .const T, _   => Const' T
  | .comp G a, X  => Comp' G (a.interp X)
```

Closing a DescF to a Desc (substituting a concrete Desc for the variable):
```lean
def DescF.close : DescF → Desc → Desc
  | .var, d       => d
  | .unit, _      => .unit
  | .empty, _     => .empty
  | .sum a b, d   => .sum (a.close d) (b.close d)
  -- ... etc
```

### Task 2.2: Derive `LocalFunctor` from `DescF`

The key insight: `LocalFunctor` for `DescF.interp df` can be proved by structural induction on `df`, because each constructor corresponds to a combinator with a known locality proof.

```lean
instance : LocalFunctor (DescF.interp df) := by
  induction df with
  | unit => exact LocalFunctor.const _
  | empty => exact LocalFunctor.const _
  | var => exact LocalFunctor.id
  | sum a b iha ihb => exact LocalFunctor.sum _ _ (iha) (ihb)
  | prod a b iha ihb => exact LocalFunctor.prod _ _ (iha) (ihb)
  | later a ih => exact LocalFunctor.compose World.Later _ -- or specific later instance
  | func a b iha ihb => exact LocalFunctor.function _ _ (iha) (ihb)
  | const T => exact LocalFunctor.const _
  | comp G a ih => exact LocalFunctor.comp G _ (ih)
```

Note: `LocalFunctor` itself needs to be refactored to work on `(Nat → Type) → (Nat → Type)` instead of `World → World`. This is the most significant change in this phase.

### Task 2.3: Refactor `LocalFunctor`

**Current:**
```lean
class LocalFunctor (F : World → World) where
  obj_local : ∀ (X Y : World) (n : Nat),
    (∀ m, m ≤ n → X.obj m = Y.obj m) →
    (F X).obj n = (F Y).obj n
```

**New:** Since `World` is now a typeclass on `Nat → Type`, `LocalFunctor` operates on type-level functors:

```lean
class LocalFunctor (F : (Nat → Type) → (Nat → Type)) where
  obj_local : ∀ (X Y : Nat → Type) (n : Nat),
    (∀ m, m ≤ n → X m = Y m) →
    F X n = F Y n
```

The instances for `sum`, `prod`, `later`, `function`, `comp`, `const`, `id`, `compose` all transfer with minimal changes (replace `.obj` with direct application).

Similarly update `StrictLocalFunctor` and `PositiveLocalFunctor`.

### Task 2.4: Refactor `gfix`

**Current:**
```lean
def gfix (F : World → World) [LocalFunctor F] : World where
  obj n := (gfix.chain F n).obj n
  restrict := cast (gfix.chain_stable F n) ∘ (gfix.chain F (n + 1)).restrict
```

**New:** `gfix` takes `F : (Nat → Type) → (Nat → Type)` and returns `Nat → Type`:

```lean
def gfix (F : (Nat → Type) → (Nat → Type)) [LocalFunctor F] : Nat → Type :=
  fun n => gfix.chain F n n
```

where `gfix.chain F : Nat → (Nat → Type)`:
```lean
def gfix.chain (F : (Nat → Type) → (Nat → Type)) : Nat → (Nat → Type)
  | 0 => F (Const' PUnit)
  | n + 1 => F (Later' (gfix.chain F n))
```

The `World` instance for `gfix F`:
```lean
instance [LocalFunctor F] : World (gfix F) where
  restrict := cast (gfix.chain_stable F n) ∘ (gfix.chain F (n + 1)).restrict
```

Wait -- the chain elements need `World` instances for the restriction. Since `F` maps worlds to worlds, `gfix.chain F k` is `F (Later' (gfix.chain F (k-1)))`, and we need `World` on each chain element. This requires:
- `F` preserves `World` instances (i.e., if `[World X]` then `[World (F X)]`)
- A new property, or we require `F` to be `DescF.interp df` for some `df`

**Decision:** For `gfix`, the `World` instance on the result is constructed from the chain, which uses `cast` through the stabilization theorem. The restriction at step `n` is the restriction of `gfix.chain F (n+1)` at step `n+1`, cast via stabilization to step `n`. The chain elements have `World` instances when `F` preserves them. We can either:
1. Add a typeclass `PreservesWorld F` saying `[World X] → World (F X)`, or
2. Restrict `gfix` to `DescF.interp df` where `World` is derived from `DescF`

Option 2 is cleaner and aligns with the goal. But option 1 is more general. For now, option 1 is safer and closer to the current code. The `LocalFunctor` property already implies a relationship between inputs and outputs.

Actually, looking more carefully: the current `gfix` only needs `restrict` from the chain, and each chain element `F (Later (chain F n))` *is* a `World` because `F` returns a `World`. In the new design, `F` returns `Nat → Type`, and we need `World` on `F X` whenever `World X`. This is naturally satisfied when `F = DescF.interp df` because the `World` instance is built compositionally. For a general `F`, we'd need the `PreservesWorld` class.

**Practical approach:** Add `[∀ {X}, [World X] → World (F X)]` as a constraint on `gfix`, and show this for `DescF.interp` by induction.

---

## Phase 3: Derive Handler and HasSignature

### Task 3.1: Update derive handler to generate `Desc` values

**Current handler generates:**
1. `F.sig` — a `World` value built with `world(...)` syntax
2. `F.toSig` — match on `F n` to produce `sig.obj n`
3. `F.ofSig` — match on `sig.obj n` to produce `F n`
4. `SignatureFunctor` instance

**New handler generates:**
1. `F.desc` — a `Desc` value (an inductive term, not a `World`)
2. `F.toSig` — match on `F n` to produce `F.desc.interp n`
3. `F.ofSig` — match on `F.desc.interp n` to produce `F n`
4. `HasSignature` instance

The key change in `WorldLift.toSyntax`: instead of generating `world(...)` syntax, generate `Desc` constructor syntax:
- `.world w` → depends on context; if `w` has a `HasSignature` instance, use `w.desc`
- `.const t` → `Desc.const t`
- `.recVar` → This is the variable, invalid in `Desc` (only valid in `DescF`)
- `.later l` → `Desc.later (l.toDescSyntax)`
- `.prod a b` → `Desc.prod (a.toDescSyntax) (b.toDescSyntax)`
- `.sum a b` → `Desc.sum (a.toDescSyntax) (b.toDescSyntax)`
- `.func a b` → `Desc.func (a.toDescSyntax) (b.toDescSyntax)`
- `.comp F l` → `Desc.comp F (l.toDescSyntax)`

For types with a recursive World parameter (like `T.F V T`), the handler generates a `DescF` and the corresponding `HasSignature` instance references `DescF.close df (someDesc)`.

### Task 3.2: Handle the recursive-variable case

Inductives like `T.F (V : World) (T : World) (n : Nat)` have a World parameter (`T`) that is the recursive variable. The handler currently tracks this via `recFVar?`.

In the new design:
- If the inductive has no recursive World param: generate a `Desc`
- If it has a recursive World param: generate a `DescF` where the recursive param maps to `.var`

For the `DescF` case, `HasSignature` would be parameterized:
```lean
-- For T.F V:
def T.F.descF (V_desc : Desc) : DescF := .sum V_desc.lift (.prod (.const Event) .var)
-- where Desc.lift : Desc → DescF injects Desc into DescF (no variables)
```

Actually, this is getting complex. A simpler approach: the handler always generates a `Desc` (possibly parameterized by other `Desc` arguments for the World params). The recursive variable is NOT represented in `Desc` — it lives in `DescF` only for the `LocalFunctor` derivation.

**Revised approach for derive handler:**
1. For each World parameter, the `desc` takes a `Desc` argument
2. For the recursive variable, a separate `descF` is generated with `.var`
3. The `HasSignature` instance is parameterized by `[HasSignature P]` for each World param `P`

Example for `T.F`:
```lean
def T.F.desc (V : Desc) : Desc := .sum V (.prod (.const Event) .var) -- ERROR: .var is DescF
```

Hmm. The recursive variable complicates things. Let me reconsider.

**Key insight:** `HasSignature` is for *closed* types (like `Value.F D n` for a specific `D`). The `Desc` in `HasSignature` is always closed. The `DescF` is only used for deriving `LocalFunctor` on the *functor* `fun X => T.Sig V X`.

So the derive handler generates:
1. `F.desc` — parameterized by `Desc` for each non-recursive World param, with the recursive World param as a `Desc` argument too:
   ```lean
   def T.F.desc (V_desc : Desc) (T_desc : Desc) : Desc := .sum V_desc (.prod (.const Event) T_desc)
   ```
2. `F.descF` — same but with `.var` for the recursive param:
   ```lean
   def T.F.descF (V_desc : Desc) : DescF := .sum (Desc.lift V_desc) (.prod (.const Event) .var)
   ```
3. `HasSignature` — uses `F.desc` with concrete Desc arguments
4. `LocalFunctor` — uses `F.descF`, automatic from Task 2.2

### Task 3.3: `world(...)` syntax update

The `world(...)` elaborator currently produces `World` values. Options:
1. **Keep it** but have it produce `Nat → Type` families instead of `World` values
2. **Remove it** if `Desc` makes it unnecessary
3. **Dual mode**: `world(...)` produces families, `desc(...)` produces `Desc` values

Recommendation: **Option 1** — update `world(...)` to produce `Nat → Type`. This is the minimal change. The elaborator maps:
- `world(A ⊕ B)` → `Sum' (world(A)) (world(B))`
- `world(A × B)` → `Prod' (world(A)) (world(B))`
- `world(A → B)` → `Function' (world(A)) (world(B))`
- `world(▹ A)` → `Later' (world(A))`
- `world(γ X, body)` → `gfix (fun X => world(body))`
- `world(T)` where `T : Type` → `Const' T`
- `world(T)` where `T : Nat → Type` → `T`

---

## Phase 4: Migration of Downstream Files

### Task 4.1: Migrate `Trace.lean`

**Current:**
```lean
inductive T.F (V T : World) (n : Nat) where
  | ret (v : V n) | step (ev : Event) (t : T n)
def T.Sig (V T : World) : World := world(V ⊕ Event × T)
instance : SignatureFunctor (T.F V W) where Sig := T.Sig V W; ...
instance T.Sig.localFunctor (V : World) : LocalFunctor (T.Sig V) := ...  -- manual!
def T (V : World) : World := World.gfix (T.Sig V)
```

**New:**
```lean
inductive T.F (V : Nat → Type) (T : Nat → Type) (n : Nat) where
  | ret (v : V n) | step (ev : Event) (t : T n)

-- HasSignature generated by derive handler:
-- T.F.desc (V_desc T_desc : Desc) : Desc := .sum V_desc (.prod (.const Event) T_desc)
-- T.F.descF (V_desc : Desc) : DescF := .sum (lift V_desc) (.prod (.const Event) .var)
deriving instance HasSignature for T.F  -- generates desc, descF, ofSig, toSig

-- LocalFunctor is automatic from descF!
-- instance (V_desc : Desc) : LocalFunctor (DescF.interp (T.F.descF V_desc))

-- T.Sig as a family:
def T.Sig (V : Nat → Type) (X : Nat → Type) : Nat → Type :=
  Sum' V (Prod' (Const' Event) X)
-- or equivalently: fun n => V n ⊕ (Event × X n)

def T (V : Nat → Type) [World V] : Nat → Type := gfix (T.Sig V)
-- World instance for T V: from gfix
```

The `T.unfold`, `T.fold`, `T.ret`, `T.step` functions change `World` → `Nat → Type` in their signatures, and `(T V) n` replaces `(T V).obj n`.

### Task 4.2: Migrate `Semantics.lean`

**Current:**
```lean
class Sem (D : World) where
  step   : world(Event → ▹ D → D).El
  ...
```

**New:**
```lean
class Sem (D : Nat → Type) [World D] where
  step   : world(Event → ▹ D → D).El
  ...
```

The `world(...)` syntax now elaborates to `Nat → Type` families, so `world(Event → ▹ D → D)` becomes `Function' (Const' Event) (Function' (Later' D) D)` — a `Nat → Type`.

`El` becomes `El (F : Nat → Type) := {n : Nat} → F n` (defined on families, not on `World`).

`EnvEntry D` becomes:
```lean
abbrev EnvEntry (D : Nat → Type) : Nat → Type := Prod' (Const' Var) (Later' D)
-- or: fun n => Var × Later.shift D n
```

### Task 4.3: Migrate `ByName.lean`

**Current:**
```lean
inductive Value.F (D : World) (n : Nat) where ...
def Value.Sig (D : World) : World := world(Unit ⊕ (Var × D → D) ⊕ Con × List (Var × D))
def D.Sig (D : World) : World := world(T.Sig (Value.Sig D) D)
instance D.Sig.localFunctor : LocalFunctor Sig where obj_local := by sorry  -- !
def D : World := World.gfix D.Sig
```

**New:**
```lean
inductive Value.F (D : Nat → Type) (n : Nat) where
  | stuck | fn : (Function' (Prod' (Const' Var) D) D) n → Value.F D n
  | con : Con → (Comp' List (Prod' (Const' Var) D)) n → Value.F D n

deriving instance HasSignature for Value.F

def Value.Sig (D : Nat → Type) : Nat → Type :=
  Sum' (Const' Unit) (Sum' (Function' (Prod' (Const' Var) D) D)
                            (Prod' (Const' Con) (Comp' List (Prod' (Const' Var) D))))

def D.Sig (X : Nat → Type) : Nat → Type := T.Sig (Value.Sig X) X
-- LocalFunctor for D.Sig: derived from DescF automatically! No more sorry!

def D : Nat → Type := gfix D.Sig
-- World instance: from gfix
```

The `sorry` in `D.Sig.localFunctor` is eliminated because `LocalFunctor` is derived from the `DescF` structure.

### Task 4.4: Migrate `ByNeed.lean`

Same pattern as ByName. `DN` becomes `Nat → Type`:
```lean
def DN : Nat → Type := gfix D.Sig
-- Same signature as D, different Sem instance
```

`Heap`, `ByNeedF`, `ByNeed` adapt similarly, replacing `World` with `Nat → Type` and `.obj n` with `n`.

### Task 4.5: Migrate `Env.lean`

`Env` is already `List (Var × V)` for `V : Type`. No change needed. It's used as `Env (EnvEntry D n)` at each step, or as `Comp' (fun V => Env V) (EnvEntry D)` at the family level.

---

## Phase 5: Cleanup

### Task 5.1: Remove old `World` structure and namespace

Delete:
- `structure World`
- `World.Const`, `World.Sum`, `World.Prod`, `World.Function`, `World.Comp`, `World.Bicomp`
- `CoeFun World`, `Coe World`
- Old `SignatureFunctor` class

Rename:
- `Sum'` → `World.Sum` (or keep in a `Fam` namespace)
- `Prod'` → `World.Prod`
- etc.

### Task 5.2: Rename primed combinators

Remove the prime suffixes once the old namespace is clear.

### Task 5.3: Update tests

- `SignatureFunctorTests.lean` → `HasSignatureTests.lean`
- `WorldSyntax.lean` tests: update expected types from `World` to `Nat → Type`

---

## Migration Ordering and Dependencies

The tasks must be done in this order to maintain a compilable state:

```
Phase 1 (new foundations, additive only):
  1.1 → 1.2 → 1.3 → 1.4

Phase 2 (DescF and LocalFunctor):
  2.1 → 2.2
  2.3 (can be parallel with 2.1-2.2, but needed before gfix)
  2.4 (needs 2.3)

Phase 3 (derive handler):
  3.1 → 3.2 → 3.3

Phase 4 (downstream migration):
  4.1 → 4.2 → 4.3 → 4.4 → 4.5

Phase 5 (cleanup):
  5.1 → 5.2 → 5.3
```

**Parallel tracks:** Phases 1 and 2 can be developed in parallel to some extent. The new definitions (Phase 1) can coexist with the old `structure World` during migration. Phase 3 depends on Phase 1 (for `Desc`) and Phase 2 (for `DescF`). Phase 4 depends on all earlier phases. Phase 5 is cleanup.

**Recommended approach:** Do Phase 1 first, keeping the old `World` structure. Add the new typeclass under a different name if needed (e.g., `class IsWorld`), then once all downstream files are migrated, rename.

Actually, a more practical migration: **keep `structure World` as a compatibility wrapper** that bundles `F : Nat → Type` with `[World F]`:
```lean
structure WorldBundle where
  carrier : Nat → Type
  [inst : World carrier]
```
This lets old code work while new code uses the typeclass. Then Phase 4 migrates file by file, and Phase 5 removes the bundle.

---

## Key Technical Challenges

### 1. Instance resolution for nested `Desc.interp`

When `d = .sum (.const Unit) (.prod (.const Event) (.later .unit))`, Lean needs to resolve `World (Desc.interp d)` by unfolding `interp` and composing instances. This should work because Lean's instance resolution handles definitional unfolding, but may need `@[reducible]` on `Desc.interp`.

### 2. `gfix` and `World` on chain elements

The `gfix.chain F k` elements need `World` instances for `restrict`. When `F = DescF.interp df`, this is obtained by:
- `gfix.chain F 0 = F (Const' PUnit)`, and `World (Const' PUnit)` is trivial
- `gfix.chain F (k+1) = F (Later' (gfix.chain F k))`, and if `World (gfix.chain F k)` then `World (Later' (gfix.chain F k))` then `World (F (Later' (gfix.chain F k)))` by the DescF structure

But `gfix.chain F k` is defined by recursion on `k`, so the `World` instance is also by recursion. This needs a `def` with explicit recursion, not an `instance` declaration.

Workaround: the `restrict` for `gfix` is defined directly using `cast` and chain restriction (as currently), without needing a `World` instance on chain elements. The chain elements' `restrict` is obtained from the structure of `F`:

```lean
-- Chain elements have restriction because F maps families-with-restriction to families-with-restriction
-- This is implicit in the current code: (gfix.chain F (n+1)).restrict exists because
-- F returns a World, so F(anything).restrict exists.
```

In the new design, we need `F` to produce a `World` instance on its output given one on its input. This is `[∀ X [World X], World (F X)]`, which holds for `DescF.interp df` by the Task 2.2 construction.

### 3. Cast-heavy proofs in `gfix`

The `gfix` construction heavily uses `cast` and equality proofs from `LocalFunctor.obj_local`. These proofs use `(F X).obj n = (F Y).obj n`, which in the new design becomes `F X n = F Y n`. The proofs should transfer directly since `.obj` was just projection.

### 4. `world(...)` syntax during migration

During migration, `world(...)` needs to work with both old `World` values and new `Nat → Type` families. The recommended approach: update `world(...)` to produce families first (Phase 3), then migrate downstream files.

---

## Risk Assessment

- **Low risk:** Desc, HasSignature, new combinators — purely additive
- **Medium risk:** LocalFunctor refactoring — touches proofs in gfix/lfp, but proofs should transfer
- **Medium risk:** world(...) syntax — needs careful testing with all existing examples
- **High risk:** gfix World instance on chain elements — may need creative instance management
- **High risk:** D.Sig.localFunctor sorry elimination — this is a key deliverable but depends on DescF working correctly

---

## Estimated Effort

- Phase 1: 2-3 hours (straightforward definitions)
- Phase 2: 3-4 hours (LocalFunctor refactoring touches many proofs)
- Phase 3: 3-4 hours (derive handler metaprogramming)
- Phase 4: 4-6 hours (downstream migration, most mechanical but verbose)
- Phase 5: 1-2 hours (cleanup)
- **Total: 13-19 hours**
