import AbsDen.NeedSound
import AbsDen.Absence

/-! # Non-vacuity witnesses for the soundness theorem

Concrete instantiations of `usage_abstracts_need` and of the freshness
vocabulary it rests on. The paper examples are closed Barendregt programs, so
every hypothesis of the theorem is discharged and the entailments below carry
no assumptions. `Fresh` at the bounded usage domain holds of elements that
avoid a variable and fails for elements that read it, so the freshness
premises of the abstraction laws are contentful on both sides. -/

open Iris Iris.BI

namespace AbsDen

/-! ## `Fresh` at `UDk` is neither empty nor total -/

/-- A look at a *different* variable is fresh at `x`: the production lemmas
    build the fact for any entry shape the fundamental lemma stores. -/
example : Fresh (D := Discrete (UDk 10)) "x"
    (Domain.step (.look "y") Domain.stuck) :=
  Fresh.step (.look "y") (fun h => absurd (Event.look.inj h) (by decide))
    (Fresh.stuck "x")

/-- An element that reads `x` is *not* fresh at `x`: freshness pins the usage
    at `x` to zero, and the proxy for a used binder reads it once. -/
example : ¬ Fresh (D := Discrete (UDk 10)) "x" (UDk.wrap (UD.fn.proxy "x")) :=
  fun h => by
    have h0 := UDk.get_eq_zero_of_fresh h
    rw [show (UDk.wrap (k := 10) (UD.fn.proxy "x")).uses
          = Uses.singenv "x" .u1 from rfl,
        Uses.get_singenv_self] at h0
    exact absurd h0 (by decide)

/-- The same failure for the look-wrapped shape the relation stores. -/
example : ¬ Fresh (D := Discrete (UDk 10)) "x"
    (Domain.step (.look "x") Domain.stuck) :=
  fun h => by
    have h0 := UDk.get_eq_zero_of_fresh h
    rw [show ((Domain.step (.look "x") Domain.stuck :
            Discrete (UDk 10)) : UDk 10).uses
          = Uses.singenv "x" .u1 + Uses.emp from rfl,
        Uses.get_add, Uses.get_singenv_self, Uses.get_emp] at h0
    exact absurd h0 (by decide)

/-! ## `EnvFresh` is satisfiable beyond the empty environment -/

/-- A let-bound entry, look-wrapped at its own binder inside the let universe,
    is fresh at everything outside it. -/
example : EnvFresh ["z"]
    (Env.empty[("z" : Var) ↦
      (Domain.step (.look "z") Domain.stuck : Discrete (UDk 10))]) :=
  EnvPred.extend EnvPred.empty "z" (fun y hy =>
    Fresh.step (.look "z")
      (fun h => hy (by rw [← Event.look.inj h]; exact List.mem_cons_self ..))
      (Fresh.stuck y))

/-! ## Usage analysis approximates the examples

`lookCount_le_usage` and `absence`, applied. The statements quantify
over every prefix length, so no evaluation can establish them; they are
consequences of the soundness theorem alone. The analysis values they
consume are derived symbolically through the combinator API, never by
computation. -/

theorem usgEx1_barendregt : Barendregt usgEx1 := by
  simp only [Barendregt, usgEx1, Exp.bv, Exp.fv]
  decide

theorem usgEx7_barendregt : Barendregt usgEx7 := by
  simp only [Barendregt, usgEx7, Exp.bv, Exp.fv]
  decide

/-- The analysis value at `j` in `let j = λy.y in j`, derived symbolically:
    the recursive promise is `j`-fresh because the right-hand side never
    mentions `j` (`Fresh.bind_id`), so the body's single look is all there
    is. -/
theorem usgEx7_uses_j : (evalUsgk 10 usgEx7 Env.empty).uses !? "j" = U.u1 := by
  have hff : FreshFn (D := Discrete (UDk 10)) "j"
      (fun _ => AbstractDomain.fn (D := UDk 10) "y"
        (fun a => AbstractDomain.step (D := UDk 10) .app2 a)) :=
    fun P hP _ _ => hP.fn "y"
      (discreteHom (fun a => AbstractDomain.step (D := UDk 10) .app2 a))
      (fun d' hd' => hP.step .app2 d' (fun h => Event.noConfusion h) hd')
  have hzero : (kleeneFix (fun _ => AbstractDomain.fn (D := UDk 10) "y"
      (fun a => AbstractDomain.step (D := UDk 10) .app2 a))).uses !? "j" = U.u0 :=
    UDk.get_eq_zero_of_fresh (Fresh.bind_id hff)
  simp only [evalUsgk, usgEx7, eval, Env.get_extend_self, Option.getD,
    disc_bind, disc_step, disc_fn]
  rw [UDk.bind_def]
  show (AbstractDomain.step (D := UDk 10) .let1
      (AbstractDomain.step (D := UDk 10) (.look "j")
        (kleeneFix (fun _ => AbstractDomain.fn (D := UDk 10) "y"
          (fun a => AbstractDomain.step (D := UDk 10) .app2 a))))).uses !? "j" = U.u1
  rw [UDk.step_uses_get_ne (fun h => Event.noConfusion h),
    UDk.step_look_uses, Uses.get_add, Uses.get_singenv_self, hzero]
  rfl

/-- `let j = λy.y in j`: the evaluation looks `j` up at most once, at any
    prefix length. The trace performs exactly one lookup (guard below), so
    the bound is tight. -/
theorem usgEx7_j_looked_at_most_once (n : Nat) :
    Trace.lookCount "j" n (D.runAt μ₀ (evalByNeed usgEx7 Env.empty)) ≤ 1 :=
  U.ofCount_le_u1
    (usgEx7_uses_j ▸ lookCount_le_usage 10 usgEx7 usgEx7_barendregt "j" n)

/-- `let i = λx.x in i i`: the lambda binder `x` is never looked up, at any
    prefix length. -/
theorem usgEx1_x_never_looked (n : Nat) :
    Trace.lookCount "x" n (D.runAt μ₀ (evalByNeed usgEx1 Env.empty)) = 0 :=
  absence_not_letBV 10 usgEx1 usgEx1_barendregt "x"
    (by simp only [usgEx1, Exp.letBV]; decide) n

/-! ### The recursive binding `let i = (λy.λx.x) i in i`

The right-hand side of the `let` mentions `i`, so the fixpoint iteration
recirculates the promise for `i` through a `look i`. The analysis still
reports `i ↦ u1`: the outer lambda `y` never uses its argument, so its
summary head is `u0` and the application annihilates the recirculated
usage. The bound below then holds at every prefix length. -/

theorem usgEx6_barendregt : Barendregt usgEx6 := by
  simp only [Barendregt, usgEx6, Exp.bv, Exp.fv]
  decide

/-- The right-hand side of `usgEx6`'s `let` reads `u0` at `i`, whatever
    promise it is applied to: the `u0` summary head of `λy.…` multiplies the
    recirculated `look i` to nothing. -/
theorem usgEx6_rhs_uses_i (d : UDk 10) :
    (AbstractDomain.step Event.app1
      (AbstractDomain.apply
        (AbstractDomain.fn (D := UDk 10) "y" (fun _ =>
          AbstractDomain.step Event.app2
            (AbstractDomain.fn (D := UDk 10) "x" (fun a =>
              AbstractDomain.step Event.app2 a))))
        (AbstractDomain.step (Event.look "i") d))).uses !? "i" = U.u0 := by
  rw [UDk.step_uses_get_ne (fun h => Event.noConfusion h), UDk.apply_uses_get]
  have hhead : (peel (AbstractDomain.fn (D := UDk 10) "y" (fun _ =>
      AbstractDomain.step Event.app2
        (AbstractDomain.fn (D := UDk 10) "x" (fun a =>
          AbstractDomain.step Event.app2 a))) : UDk 10).val.val).1 = U.u0 := by
    rw [UDk.fn_head (by decide),
      UDk.step_uses_get_ne (fun h => Event.noConfusion h),
      UDk.fn_uses_get_ne _ _ (by decide),
      UDk.step_uses_get_ne (fun h => Event.noConfusion h)]
    exact UDk.proxy_uses_get_ne (by decide)
  rw [hhead, U.zero_mul, U.add_zero,
    UDk.fn_uses_get_ne _ _ (by decide),
    UDk.step_uses_get_ne (fun h => Event.noConfusion h),
    UDk.fn_uses_get_ne _ _ (by decide),
    UDk.step_uses_get_ne (fun h => Event.noConfusion h)]
  exact UDk.proxy_uses_get_ne (by decide)

/-- The analysis value at `i` in `usgEx6`, derived symbolically: the
    fixpoint's usage at `i` stays `u0` (`usgEx6_rhs_uses_i` through
    `kleeneFix_pred`), so the body's single look is all there is. -/
theorem usgEx6_uses_i : (evalUsgk 10 usgEx6 Env.empty).uses !? "i" = U.u1 := by
  have hfix : (kleeneFix (fun a =>
      AbstractDomain.step Event.app1
        (AbstractDomain.apply
          (AbstractDomain.fn (D := UDk 10) "y" (fun _ =>
            AbstractDomain.step Event.app2
              (AbstractDomain.fn (D := UDk 10) "x" (fun a =>
                AbstractDomain.step Event.app2 a))))
          (AbstractDomain.step (Event.look "i") a)))).uses !? "i" = U.u0 := by
    refine kleeneFix_pred (P := fun (d : UDk 10) => d.uses !? "i" = U.u0) _ ?_ ?_ ?_
    · exact Uses.get_emp "i"
    · intro a b ha hb
      show (a.uses ⊔ b.uses) !? "i" = U.u0
      rw [Uses.get_sup, ha, hb]; rfl
    · exact fun d _ => usgEx6_rhs_uses_i d
  simp only [evalUsgk, usgEx6, eval, Env.get_extend_self, Option.getD, Option.elim,
    disc_bind, disc_step, disc_fn, disc_apply]
  rw [UDk.bind_def]
  show (AbstractDomain.step (D := UDk 10) .let1
      (AbstractDomain.step (D := UDk 10) (.look "i")
        (kleeneFix (fun a =>
          AbstractDomain.step Event.app1
            (AbstractDomain.apply
              (AbstractDomain.fn (D := UDk 10) "y" (fun _ =>
                AbstractDomain.step Event.app2
                  (AbstractDomain.fn (D := UDk 10) "x" (fun a =>
                    AbstractDomain.step Event.app2 a))))
              (AbstractDomain.step (Event.look "i") a)))))).uses !? "i" = U.u1
  rw [UDk.step_uses_get_ne (fun h => Event.noConfusion h),
    UDk.step_look_uses, Uses.get_add, Uses.get_singenv_self, hfix]
  rfl

/-- `let i = (λy.λx.x) i in i`: even though the binding is recursive, the
    evaluation looks `i` up at most once, at any prefix length. -/
theorem usgEx6_i_looked_at_most_once (n : Nat) :
    Trace.lookCount "i" n (D.runAt μ₀ (evalByNeed usgEx6 Env.empty)) ≤ 1 :=
  U.ofCount_le_u1
    (usgEx6_uses_i ▸ lookCount_le_usage 10 usgEx6 usgEx6_barendregt "i" n)

/-! The tightness witnesses: `usgEx7` does perform its one permitted lookup
of `j`, `usgEx6` its one lookup of `i`, and `usgEx1` looks `i` up twice under
its `uω` budget. -/
#guard Trace.lookCount "j" 20 (D.runAt μ₀ (evalByNeed usgEx7 Env.empty)) == 1
#guard Trace.lookCount "i" 20 (D.runAt μ₀ (evalByNeed usgEx6 Env.empty)) == 1
#guard Trace.lookCount "i" 20 (D.runAt μ₀ (evalByNeed usgEx1 Env.empty)) == 2
#guard (evalUsgk 10 usgEx1 Env.empty).uses !? "i" == U.uω

end AbsDen
