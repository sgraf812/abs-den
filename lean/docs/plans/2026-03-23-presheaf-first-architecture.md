# Presheaf-First Architecture

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Refactor the Lean development so that all stage-index matching is confined to `ToposOfTrees.lean`, and client modules work entirely with presheaf operations.

**Architecture:** `Later` becomes `def` (opaque outside its module). `Psh` gets `CoeFun` so `D n = D.obj n`. `Sem` becomes a type class on `Psh`, without `nextD`. `semEval` uses `Psh.next` (evaluate-then-restrict) and the `Later` applicative (`map`, `ap`) — no stage matching.

**Tech Stack:** Lean 4, Lake, Nix (`nix develop --command lake build AbsDen`)

---

### Task 1: Update `ToposOfTrees.lean`

**Files:**
- Modify: `AbsDen/ToposOfTrees.lean`

**Step 1: Add `CoeFun` and `Coe` for `Psh`**

Add after the `Psh` definition:

```lean
instance : CoeFun Psh.{u} (fun _ => Nat → Sort u) where
  coe A := A.obj

instance : Coe Psh.{u} (Nat → Sort u) where
  coe A := A.obj
```

`CoeFun` lets us write `D n` for `D : Psh`. `Coe` lets us write `▹ D` for `D : Psh`.

**Step 2: Remove `withOuter` and `withOuter₂`**

Delete the `withOuter` and `withOuter₂` definitions from the `Later` namespace (they no longer exist in the user's version, but verify they're gone).

**Step 3: Keep `Later` as `def`**

Verify `Later` is `def` (not `abbrev`). This makes it opaque outside this module.

**Step 4: Verify `Later.map`, `Later.ap`, `Psh.next` compile**

These match on `n` internally — that's fine, they're in ToposOfTrees.

**Step 5: Build**

Run: `nix develop --command lake build AbsDen`

---

### Task 2: Update `Semantics.lean`

**Files:**
- Modify: `AbsDen/Semantics.lean`

**Step 1: Rewrite `Sem` as a type class**

```lean
class Sem (D : Psh) where
  step : (n : Nat) → Event → ▹ D n → D n
  stuck : (n : Nat) → D n
  fn : (n : Nat) → (D n → D n) → D n
  apply : (n : Nat) → D n → D n → D n
  con : (n : Nat) → Con → List (D n) → D n
  select : (n : Nat) → D n → List (Con × (List (D n) → D n)) → D n
  bind : (n : Nat) → ▹ (fun m => ▹ D m → D m) n → (▹ D n → D n) → D n
```

No `nextD` — restriction comes from `D : Psh` via `Psh.next`.

**Step 2: Define `envPsh` helper**

```lean
def envPsh (D : Psh) : Psh where
  obj n := Env (D n)
  restrict ρ := ρ.map fun (y, d) => (y, D.restrict d)
```

This makes `Env D` into a presheaf, so we can use `Psh.next (envPsh D)` to restrict envs.

**Step 3: Remove `laterEnv` and `laterEnvArg`**

Delete both definitions. They are replaced by `Psh.next` and `Later.map`/`Later.ap`.

**Step 4: Rewrite `semEval`**

The key patterns:
- **Evaluate-then-restrict** for `step`: `Psh.next D n (eval e n ρ)`
- **Applicative** for `bind`: `Later.map` + `Later.ap`

```lean
def semEval {D : Psh} [Sem D] : Exp → (n : Nat) → Env (D n) → D n
  | .ref x, n, ρ => match ρ.find? x with
    | some d => d
    | none => Sem.stuck n
  | .lam x body, n, ρ =>
    Sem.fn n (fun d =>
      Sem.step n .app2 (Psh.next D n (semEval body n (ρ.bind x d))))
  | .app e₁ x, n, ρ => match ρ.find? x with
    | some d =>
      Sem.step n .app1 (Psh.next D n (Sem.apply n (semEval e₁ n ρ) d))
    | none => Sem.stuck n
  | .conapp K xs, n, ρ => match ρ.pmapList xs with
    | some ds => Sem.con n K ds
    | none => Sem.stuck n
  | .case' eₛ alts, n, ρ =>
    Sem.step n .case1 (Psh.next D n (
      Sem.select n (semEval eₛ n ρ) (alts.map fun alt =>
        (alt.con, fun ds =>
          let ρ'' := ρ.bindMany alt.vars ds
          Sem.step n .case2 (Psh.next D n (semEval alt.rhs n ρ''))))))
  | .let' x e₁ e₂, n, ρ =>
    let ρ▹ := Psh.next (envPsh D) n ρ
    let rhs' : ▹ (fun m => ▹ D m → D m) n :=
      Later.map (fun m (ρ' : Env (D m)) =>
        fun dx => semEval e₁ m (ρ'.bind x (Sem.step m (.look x) dx)))
        n ρ▹
    let body : ▹ D n → D n :=
      fun dx =>
        let f := Later.map (fun m (ρ' : Env (D m)) => fun (d : D m) =>
          semEval e₂ m (ρ'.bind x (Sem.step m (.look x) d)))
          n ρ▹
        Sem.step n .let1 (Later.ap n f dx)
    Sem.bind n rhs' body
```

Key observations:
- `.ref`, `.lam`, `.app`, `.conapp`, `.case'`: all recursive calls at stage `n`, restricted via `Psh.next`
- `.let'`: `rhs'` uses `Later.map` over restricted env; `body` uses `Later.map` + `Later.ap` (applicative) to compute under `▹`
- No stage-index matching anywhere in `semEval`
- Structural recursion on `Exp` — all recursive calls use sub-expressions

**Step 5: Build**

Run: `nix develop --command lake build AbsDen.Semantics`

This will fail until Concrete.lean is updated, but Semantics should compile on its own (it only imports Syntax, Env, ToposOfTrees).

---

### Task 3: Update `Concrete.lean`

**Files:**
- Modify: `AbsDen/Concrete.lean`

**Step 1: Define `DPsh`**

```lean
def DPsh : Psh where
  obj := D
  restrict := nextD _
```

Where `nextD` is the existing presheaf restriction for `D`.

Note: `nextD` matches on stage indices — that's fine, it's a concrete implementation defining the presheaf structure, in the concrete module.

**Step 2: Provide `Sem DPsh` instance**

```lean
instance : Sem DPsh where
  step _n ev dl := D.step ev dl
  stuck _n := D.ret .stuck
  fn _n f := D.ret (.fn (fun (x, dp) => D.unfold (f (D.step (.look x) dp))))
  apply _n dv da :=
    dbind dv fun
      | .fn g => D.fold (g da.envEntry)
      | _ => D.ret .stuck
  con _n K ds := D.ret (.con K (ds.map D.envEntry))
  select _n dv alts :=
    dbind dv fun
      | .con K ds =>
        match alts.find? (fun (K', _) => K' == K) with
        | some (_, f) => f (ds.map fun (x, dl) => D.step (.look x) dl)
        | none => D.ret .stuck
      | _ => D.ret .stuck
  bind n rhs' body :=
    match n with
    | 0 => body PUnit.unit
    | _m + 1 => body (rhs' default)
```

**Step 3: Update evaluator**

```lean
def eval (e : Exp) (n : Nat) (ρ : Env (DPsh n)) : DPsh n :=
  semEval e n ρ

def evalByName (n : Nat) (e : Exp) : D n :=
  eval e n Env.empty
```

**Step 4: Build and verify tests**

Run: `nix develop --command lake build AbsDen`

Expected: all 4 `#eval` tests produce correct output. The traces may differ slightly from before (evaluate-then-restrict vs direct inner-stage evaluation) but should be semantically equivalent.

---

### Task 4: Troubleshooting notes

**If `Later` as `def` causes elaboration failures:**
The Lean kernel unfolds `def` for type checking, but the elaborator doesn't eagerly. If type annotations are needed, add them. The concrete module (Concrete.lean) may need explicit type annotations where `▹ D n` appears.

**If structural recursion on `Exp` fails:**
The `.case'` branch has `alt.rhs` inside `alts.map`. Lean's structural recursion might not trace through `List.map`. Fix: replace `alts.map` with an explicit recursive helper, or add `termination_by sizeOf e` if needed.

**If `Coe Psh (Nat → Sort u)` doesn't work for `▹ D`:**
The `▹` notation expands to `Later D` where `D : Psh` needs to coerce to `Nat → Sort u`. If Lean's coercion doesn't fire, write `▹ D.obj` explicitly (only in type annotations, not in `semEval`).

**If by-need `bind` needs additional `Later` operations:**
Axiomatize them in ToposOfTrees.lean first (e.g., `axiom Later.flip : (A → ▹ B) → ▹ (A → B)`). We'll implement them later.
