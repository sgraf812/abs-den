# Presheaf Syntax and Later/Function Design

**Goal:** `psh(...)` syntax to construct presheaves, hiding step index quantification. `Later : Psh → Psh`, `Psh.Function` (internal hom), `Psh.fix` (guarded fixpoint).

**Build:** `nix develop --command lake build AbsDen`

**Tools:** Use lean-lsp MCP throughout:
- `lean_goal` — check proof state after each tactic
- `lean_diagnostic_messages` — verify no errors after edits
- `lean_hover_info` — inspect types
- `lean_completions` — discover available lemmas/tactics
- `lean_multi_attempt` — try multiple tactics without file modification
- `lean_local_search` / `lean_loogle` / `lean_leansearch` — find lemmas

---

## Overview

```lean
psh(A → B)   = Psh.Function psh(A) psh(B)   -- internal hom
psh(▹ A)     = Later psh(A)
psh(μX. F)   = Psh.fix (fun X => psh(F))    -- guarded fixpoint
psh(F A)     = Psh.Comp F psh(A)            -- functor lift
psh(P : Psh) = P
psh(T : Type)= Psh.Const T

abbrev Psh.El (D : Psh) := {n : Nat} → D.obj n
-- psh(Event → ▹ D → D).El  =  {n : Nat} → Event → (Later D) n → D n
```

---

## Task 1: Primitives in ToposOfTrees.lean

Rename `Later` → `Later.shift`, `fixType` → `private Psh.fix.shift`:

```lean
def Later.shift (A : Nat → Sort u) : Nat → Sort u
  | 0 => PUnit  | n + 1 => A n

namespace Psh.fix
private def shift (F : Sort u → Sort u) : Nat → Sort u
  | 0 => F PUnit  | n + 1 => F (shift F n)
private def shift.unfold/fold ...  -- identity at each stage
end Psh.fix
```

---

## Task 2: Psh Combinators in ToposOfTrees.lean

```lean
def Later (A : Psh) : Psh where
  obj := Later.shift A.obj
  restrict {n} := A.next n

def Later.map {A B : Psh} (f : {n : Nat} → A n → B n)
    : {n : Nat} → (Later A) n → (Later B) n
  | 0 => fun _ => PUnit.unit  | _ + 1 => f

def Psh.Function (A B : Psh) : Psh where  -- internal hom
  obj n := ∀ m, m ≤ n → A m → B m
  restrict {n} f m hm := f m (Nat.le_trans hm (Nat.le_succ n))

abbrev Psh.El (D : Psh) := {n : Nat} → D.obj n

def Psh.fix (F : Psh → Psh) : Psh where  -- guarded fixpoint
  obj n := Psh.fix.shift (fun X => (F (Later.fromShift X)).obj n) n
  restrict {n} := (F (Later (Psh.fix F))).restrict

def Psh.Bicomp (F : Type → Type → Type) [Bifunctor F] (A B : Psh) : Psh where
  obj n := F (A n) (B n)
  restrict := Bifunctor.bimap A.restrict B.restrict
```

---

## Task 3: psh(...) Elaborator

```lean
syntax:max "psh(" term ")" : term

macro_rules
  | `(psh($a → $b))        => `(Psh.Function psh($a) psh($b))
  | `(psh(▹ $a))           => `(Later psh($a))
  | `(psh(μ $x:ident. $b)) => `(Psh.fix (fun $x => psh($b)))
  | `(psh(($a)))           => `(psh($a))

-- Base case elaborator: infer type, wrap in Psh.Const/Psh.Comp as needed
```

---

## Task 4: Update Semantics.lean

```lean
class Sem (D : Psh) where
  step   : psh(Event → ▹ D → D).El
  stuck  : psh(D).El
  fn     : psh((D → D) → D).El
  apply  : psh(D → D → D).El
  con    : psh(Con → List D → D).El
  select : psh(D → List (Con × (List D → D)) → D).El
  bind   : psh(▹ (▹ D → D) → (▹ D → D) → D).El

def semEval {D : Psh} [Sem D] : Exp → psh(Env D → D).El
  -- step indices implicit throughout
```

---

## Task 5: Rewrite Concrete.lean

Define `D` as `Psh` using combinators (no step index matching):

```lean
def D : Psh := Psh.fix (fun X => Psh.Bicomp T.F (psh(ValueF (▹ X))) (Later X))
-- or: psh(μX. T.F (ValueF (▹ X)) (▹ X))

def D.fold   : psh(T.F (ValueF (▹ D)) (▹ D) → D).El := Psh.fix.fold
def D.unfold : psh(D → T.F (ValueF (▹ D)) (▹ D)).El := Psh.fix.unfold
def D.ret    : psh(ValueF (▹ D) → D).El := fun v => D.fold (.ret v)
def D.step   : psh(Event → ▹ D → D).El  := fun e dl => D.fold (.step e dl)
def D.bind   : psh(D → (ValueF (▹ D) → D) → D).El := ...  -- uses Later.map

instance : Sem D where
  step := D.step
  stuck := D.ret .stuck
  ...  -- no step index matching, all via Psh combinators
```

---

## Task 6: Verify

- `lake build AbsDen` compiles
- 4 `#eval` tests pass
- No step index matching outside `ToposOfTrees.lean`

---

## Open Questions

1. Elaborator handling of nested types like `List (Con × (List D → D))`
2. Internal hom use sites need `Nat.le_refl` coercion
3. `Psh.fix` / `Later.fromShift` well-definedness details
4. Alternative `bind` type: `psh((▹ ▹ D → D) → (▹ ▹ D → D))`?
