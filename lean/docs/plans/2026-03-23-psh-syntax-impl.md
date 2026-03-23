# Presheaf Syntax Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `psh(...)` syntax, `Later : Psh → Psh`, `Psh.Function`, `Psh.fix`, hiding step index quantification.

**Architecture:** Rename primitives (`Later` → `Later.shift`, `fixType` → `Psh.fix.shift`), define Psh-level combinators, implement `psh(...)` elaborator, update Semantics/Concrete to use new API.

**Tech Stack:** Lean 4, Lake, lean-lsp MCP tools

**Spec:** `docs/plans/2026-03-23-psh-syntax-design.md`

---

## File Structure

| File | Changes |
|------|---------|
| `AbsDen/ToposOfTrees.lean` | Rename primitives, add `Later`, `Psh.Function`, `Psh.El`, `Psh.fix`, `Psh.Bicomp`, `psh(...)` syntax |
| `AbsDen/Semantics.lean` | Update `Sem` class and `semEval` to use `psh(...).El` types |
| `AbsDen/Concrete.lean` | Rewrite `D` as `Psh` using combinators, remove step index matching |

---

### Task 1: Rename Later to Later.shift

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean:21-56`

- [ ] **Step 1.1: Rename `Later` definition to `Later.shift`**

```lean
/-- The primitive step-index shifting operation.
    `Later.shift A 0 = PUnit` and `Later.shift A (n+1) = A n`. -/
def Later.shift (A : Nat → Sort u) : Nat → Sort u
  | 0 => PUnit
  | n + 1 => A n
```

- [ ] **Step 1.2: Update Later namespace to use Later.shift**

Update `Later.map`, `Later.ap`, `Later.inhabited` to reference `Later.shift`:

```lean
namespace Later

@[inline] def map {A B : Nat → Sort u} (f : (m : Nat) → A m → B m)
    (n : Nat) : Later.shift A n → Later.shift B n :=
  match n with
  | 0 => fun _ => PUnit.unit
  | m + 1 => fun a => f m a

@[inline] def ap {A B : Nat → Sort u}
    (n : Nat) : Later.shift (fun m => A m → B m) n → Later.shift A n → Later.shift B n :=
  match n with
  | 0 => fun _ _ => PUnit.unit
  | _ + 1 => fun f a => f a

def inhabited {A : Nat → Sort u} (n : Nat) (h : ∀ m, Inhabited (A m))
    : Inhabited (Later.shift A n) :=
  match n with
  | 0 => ⟨PUnit.unit⟩
  | m + 1 => h m

instance {A : Nat → Sort u} {n : Nat} [h : ∀ m, Inhabited (A m)]
    : Inhabited (Later.shift A n) :=
  Later.inhabited n h

end Later
```

- [ ] **Step 1.3: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 1.4: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "refactor: rename Later to Later.shift"
```

---

### Task 2: Rename fixType to Psh.fix.shift (private)

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean:77-96`

- [ ] **Step 2.1: Move fixType into Psh.fix namespace as private**

```lean
namespace Psh.fix

/-- The primitive guarded fixpoint for step-indexed type families.
    `shift F 0 = F PUnit` and `shift F (n+1) = F (shift F n)`.
    Private: only used internally to define `Psh.fix`. -/
private def shift (F : Sort u → Sort u) : Nat → Sort u
  | 0 => F PUnit
  | n + 1 => F (shift F n)

/-- Unfold: `shift F n → F (Later.shift (shift F) n)`. -/
private def shift.unfold {F : Sort u → Sort u}
    : (n : Nat) → shift F n → F (Later.shift (shift F) n)
  | 0, x => x
  | _ + 1, x => x

/-- Fold: `F (Later.shift (shift F) n) → shift F n`. -/
private def shift.fold {F : Sort u → Sort u}
    : (n : Nat) → F (Later.shift (shift F) n) → shift F n
  | 0, x => x
  | _ + 1, x => x

end Psh.fix
```

- [ ] **Step 2.2: Add compatibility alias for fixType**

```lean
/-- Compatibility alias. Use `Psh.fix.shift` in new code. -/
abbrev fixType := Psh.fix.shift
```

- [ ] **Step 2.3: Update dfix and loeb to use Later.shift**

```lean
def dfix {A : Nat → Sort u} (f : (n : Nat) → Later.shift A n → A n)
    : (n : Nat) → Later.shift A n
  | 0 => PUnit.unit
  | n + 1 => f n (dfix f n)

def loeb {A : Nat → Sort u} (f : (n : Nat) → Later.shift A n → A n) (n : Nat) : A n :=
  f n (dfix f n)

theorem dfix_eq {A : Nat → Sort u} (f : (n : Nat) → Later.shift A n → A n)
    (n : Nat) : dfix f (n + 1) = loeb f n := by rfl
```

- [ ] **Step 2.4: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 2.5: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "refactor: rename fixType to private Psh.fix.shift"
```

---

### Task 3: Define Later : Psh → Psh

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean` (after Psh definition, ~line 134)

- [ ] **Step 3.1: Define Later on Psh**

```lean
/-- Later modality on presheaves. `(Later A).obj n = Later.shift A.obj n`. -/
def Later (A : Psh) : Psh where
  obj := Later.shift A.obj
  restrict {n} := A.next n
```

- [ ] **Step 3.2: Add Later.map for Psh**

```lean
namespace Later

/-- Functorial map for Later on presheaves. Step index is implicit. -/
def pmap {A B : Psh} (f : {n : Nat} → A n → B n)
    : {n : Nat} → (Later A) n → (Later B) n :=
  fun {n} => match n with
    | 0 => fun _ => PUnit.unit
    | _ + 1 => f

end Later
```

- [ ] **Step 3.3: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 3.4: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: add Later : Psh → Psh"
```

---

### Task 4: Define Psh.Function (Internal Hom)

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean` (in Psh namespace)

- [ ] **Step 4.1: Define Psh.Function**

```lean
/-- Internal hom in presheaves: `(Function A B).obj n = ∀ m ≤ n, A m → B m`. -/
def Function (A B : Psh) : Psh where
  obj n := ∀ m, m ≤ n → A m → B m
  restrict {n} f m hm := f m (Nat.le_trans hm (Nat.le_succ n))
```

- [ ] **Step 4.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 4.3: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: add Psh.Function (internal hom)"
```

---

### Task 5: Define Psh.El

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean` (in Psh namespace)

- [ ] **Step 5.1: Define Psh.El**

```lean
/-- Global elements: step-index-polymorphic values. -/
abbrev El (D : Psh.{u}) : Sort _ := {n : Nat} → D.obj n
```

- [ ] **Step 5.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 5.3: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: add Psh.El (global elements)"
```

---

### Task 6: Define Psh.Bicomp

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean` (in Psh namespace)

- [ ] **Step 6.1: Define Psh.Bicomp**

```lean
/-- Lift a bifunctor to presheaves: `(Bicomp F A B).obj n = F (A n) (B n)`. -/
def Bicomp (F : Type → Type → Type) (fmap : ∀ {A B C D}, (A → C) → (B → D) → F A B → F C D)
    (A B : Psh) : Psh where
  obj n := F (A n) (B n)
  restrict {n} := fmap A.restrict B.restrict
```

- [ ] **Step 6.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 6.3: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: add Psh.Bicomp (bifunctor lift)"
```

---

### Task 7: Update psh(...) Syntax

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean:146-156`

- [ ] **Step 7.1: Update macro rules for psh syntax**

```lean
/-- Presheaf type syntax. -/
syntax:max "psh(" term ")" : term

macro_rules
  | `(psh($a → $b))        => `(Psh.Function psh($a) psh($b))
  | `(psh(▹ $a))           => `(Later psh($a))
  | `(psh(μ $x:ident . $b)) => `(Psh.fix (fun $x => psh($b)))
  | `(psh(($a)))           => `(psh($a))
  | `(psh($t))             => pure t

/-- `▹ A` enters psh mode: `▹ D` = `Later D` for `D : Psh`. -/
macro:1024 "▹ " x:term:1025 : term => `(Later psh($x))
```

- [ ] **Step 7.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: No errors

- [ ] **Step 7.3: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: update psh(...) syntax for Psh combinators"
```

---

### Task 8: Define Psh.fix (Guarded Fixpoint)

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean`

- [ ] **Step 8.1: Define Later.fromShift helper**

```lean
namespace Later

/-- Convert step-indexed family to presheaf for use in Psh.fix. -/
def fromShift (A : Nat → Sort u) (rst : ∀ n, A (n + 1) → A n) : Psh where
  obj := Later.shift A
  restrict {n} := match n with
    | 0 => fun _ => PUnit.unit
    | m + 1 => rst m

end Later
```

- [ ] **Step 8.2: Define Psh.fix**

```lean
/-- Guarded fixpoint on presheaves: solves `X ≅ F (▹ X)`. -/
def fix (F : Psh → Psh) : Psh where
  obj n := Psh.fix.shift (fun X => (F (Later.fromShift (Psh.fix.shift (fun X => (F (Later.fromShift X sorry)).obj n)) sorry)).obj n) n
  restrict {n} := sorry  -- Will be filled in during implementation
```

Note: The exact definition of `Psh.fix` is complex. Start with `sorry` and refine based on lean-lsp feedback.

- [ ] **Step 8.3: Add Psh.fix.fold and Psh.fix.unfold**

```lean
namespace Psh.fix

def fold (F : Psh → Psh) : {n : Nat} → (F (Later (fix F))).obj n → (fix F).obj n :=
  fun {n} => shift.fold n

def unfold (F : Psh → Psh) : {n : Nat} → (fix F).obj n → (F (Later (fix F))).obj n :=
  fun {n} => shift.unfold n

end Psh.fix
```

- [ ] **Step 8.4: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/ToposOfTrees.lean`
Expected: May have errors on `sorry` — iterate to fix

- [ ] **Step 8.5: Commit (may be partial)**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "wip: add Psh.fix (guarded fixpoint)"
```

---

### Task 9: Build ToposOfTrees.lean

**Files:**
- Verify: `AbsDen/ToposOfTrees.lean`

- [ ] **Step 9.1: Run full build**

```bash
nix develop --command lake build AbsDen.ToposOfTrees
```

- [ ] **Step 9.2: Fix any remaining errors using lean-lsp tools**

Use `lean_diagnostic_messages`, `lean_hover_info`, `lean_goal` as needed.

- [ ] **Step 9.3: Commit**

```bash
git add AbsDen/ToposOfTrees.lean
git commit -m "feat: complete ToposOfTrees Psh combinators"
```

---

### Task 10: Update Sem Type Class

**Files:**
- Modify: `AbsDen/Semantics.lean:33-40`

- [ ] **Step 10.1: Update Sem to use psh(...).El types**

```lean
class Sem (D : Psh) where
  step   : psh(Event → ▹ D → D).El
  stuck  : D.El
  fn     : psh((D → D) → D).El
  apply  : psh(D → D → D).El
  con    : psh(Con → List D → D).El
  select : psh(D → List (Con × (List D → D)) → D).El
  bind   : psh(▹ (▹ D → D) → (▹ D → D) → D).El
```

- [ ] **Step 10.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/Semantics.lean`
Expected: Errors in semEval (expected — will fix next)

- [ ] **Step 10.3: Commit**

```bash
git add AbsDen/Semantics.lean
git commit -m "refactor: update Sem class to use psh(...).El"
```

---

### Task 11: Update semEval

**Files:**
- Modify: `AbsDen/Semantics.lean:44-86`

- [ ] **Step 11.1: Update semEval signature**

```lean
def semEval {D : Psh} [Sem D] : Exp → psh(Env D → D).El
```

- [ ] **Step 11.2: Update semEval body (step indices implicit)**

Iterate with lean-lsp to fix type mismatches. Key changes:
- Remove explicit `n` parameters from `Sem.*` calls
- Use `D.next` instead of `D.next n`
- Update `Later.map` calls to use `Later.pmap`

- [ ] **Step 11.3: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/Semantics.lean`

- [ ] **Step 11.4: Commit**

```bash
git add AbsDen/Semantics.lean
git commit -m "refactor: update semEval for implicit step indices"
```

---

### Task 12: Build Semantics.lean

**Files:**
- Verify: `AbsDen/Semantics.lean`

- [ ] **Step 12.1: Run build**

```bash
nix develop --command lake build AbsDen.Semantics
```

- [ ] **Step 12.2: Fix errors iteratively with lean-lsp**

- [ ] **Step 12.3: Commit**

```bash
git add AbsDen/Semantics.lean
git commit -m "feat: complete Semantics.lean refactor"
```

---

### Task 13: Rewrite D as Psh in Concrete.lean

**Files:**
- Modify: `AbsDen/Concrete.lean:83-103`

- [ ] **Step 13.1: Add Bifunctor-like map to T.F**

```lean
namespace T.F

def bimap' {V W X Y : Type} (fv : V → W) (fx : X → Y) : F V X → F W Y :=
  bimap fv fx

end T.F
```

- [ ] **Step 13.2: Define D as Psh using Psh.fix**

```lean
/-- The domain D as a presheaf, defined via guarded fixpoint. -/
def DPsh : Psh := Psh.fix (fun X =>
  Psh.Bicomp T.F T.F.bimap' (Psh.Comp ValueF (Later X)) (Later X))
```

- [ ] **Step 13.3: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/Concrete.lean`

- [ ] **Step 13.4: Commit**

```bash
git add AbsDen/Concrete.lean
git commit -m "refactor: define D as Psh using Psh.fix"
```

---

### Task 14: Update D operations to use Psh.El

**Files:**
- Modify: `AbsDen/Concrete.lean`

- [ ] **Step 14.1: Update D.fold, D.unfold, D.ret, D.step**

```lean
namespace D

def fold : psh(T.F (ValueF (▹ DPsh)) (▹ DPsh) → DPsh).El :=
  Psh.fix.fold _

def unfold : psh(DPsh → T.F (ValueF (▹ DPsh)) (▹ DPsh)).El :=
  Psh.fix.unfold _

def ret : psh(ValueF (▹ DPsh) → DPsh).El := fun v => fold (.ret v)
def step : psh(Event → ▹ DPsh → DPsh).El := fun e dl => fold (.step e dl)

end D
```

- [ ] **Step 14.2: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/Concrete.lean`

- [ ] **Step 14.3: Commit**

```bash
git add AbsDen/Concrete.lean
git commit -m "refactor: update D operations to use Psh.El"
```

---

### Task 15: Update Sem DPsh Instance

**Files:**
- Modify: `AbsDen/Concrete.lean:167-186`

- [ ] **Step 15.1: Update Sem instance (no step index matching)**

```lean
instance : Sem DPsh where
  step := D.step
  stuck := D.ret .stuck
  fn f := D.ret (.fn (fun (x, dp) => D.unfold (f (D.step (.look x) dp))))
  apply dv da :=
    D.bind dv fun
      | .fn g => D.fold (g (D.envEntry da))
      | _ => D.ret .stuck
  con K ds := D.ret (.con K (ds.map D.envEntry))
  select dv alts :=
    D.bind dv fun
      | .con K ds =>
        match alts.find? (fun (K', _) => K' == K) with
        | some (_, f) => f (ds.map fun (x, dl) => D.step (.look x) dl)
        | none => D.ret .stuck
      | _ => D.ret .stuck
  bind rhs body := D.bind' rhs body  -- D.bind' handles Later
```

- [ ] **Step 15.2: Define D.bind using Later.pmap**

```lean
def D.bind : psh(DPsh → (ValueF (▹ DPsh) → DPsh) → DPsh).El :=
  fun d k =>
    match D.unfold d with
    | .ret v => k v
    | .step ev x => D.fold (.step ev (Later.pmap (fun d' => D.bind d' k) x))
```

- [ ] **Step 15.3: Verify with lean-lsp**

Run: `lean_diagnostic_messages` on `AbsDen/Concrete.lean`

- [ ] **Step 15.4: Commit**

```bash
git add AbsDen/Concrete.lean
git commit -m "refactor: update Sem DPsh instance (no step index matching)"
```

---

### Task 16: Full Build and Test

**Files:**
- Verify: All files

- [ ] **Step 16.1: Run full build**

```bash
nix develop --command lake build AbsDen
```

- [ ] **Step 16.2: Verify #eval tests pass**

Check that the 4 `#eval` tests at the end of Concrete.lean produce expected output.

- [ ] **Step 16.3: Verify no step index matching outside ToposOfTrees**

Grep for `match n with` or `| 0 =>` patterns in Semantics.lean and Concrete.lean.

- [ ] **Step 16.4: Final commit**

```bash
git add -A
git commit -m "feat: complete psh(...) syntax refactor"
```

---

## Notes

- **lean-lsp MCP tools**: Use throughout for verification
  - `lean_diagnostic_messages` after each edit
  - `lean_hover_info` to inspect types
  - `lean_goal` for proof state
  - `lean_multi_attempt` to try tactics without modifying files

- **Iterative approach**: Tasks 8-15 may require iteration. Use `sorry` placeholders and refine.

- **Open questions from spec** will be resolved during implementation via lean-lsp feedback.
