import AbsDen.Env

/-! # The generic denotational interpreter `eval`

Ported from Sebastian Graf, *Abstracting Denotational Interpreters*
(`~/code/tex/abs-den/paper`), mirroring `AbsDen/Semantics.lean`. The single class
`Domain` collects the denotational operations; faithfully to the repo's Kripke
naturality they are non-expansive (`-n>`). `eval` is a morphism `Env d -n> d`, so
the closures it hands to `fn`/`bind` are non-expansive by construction, and it
stays polymorphic over any `[OFE d] [Domain d]`. -/

open Iris Iris.COFE OFE

namespace AbsDen

/-- The semantic domain: an OFE with the denotational operations
    (`AbsDen/Semantics.lean`'s single `class Domain`). Only an OFE is needed (the
    operations are non-expansive); completeness is required solely to *build* a
    particular domain such as ByNeed's `D`, not by the class or by `eval`. Any
    plain type qualifies via its discrete OFE, where `-n>` collapses to `→`. -/
class Domain (d : Type) [OFE d] where
  step   : Event → d -n> d
  stuck  : d
  fn     : Var → (d -n> d) -n> d
  apply  : d -n> d -n> d
  con    : ConTag → List d -n> d
  select : d -n> List (ConTag × Nat × (List d -n> d)) -n> d
  bind   : (d -n> d) -n> (d -n> d) -n> d

open Domain

variable {d : Type} [OFE d] [Domain d]

/-- The generic denotational interpreter (`AbsDen/Semantics.lean`), as a morphism
    in the environment. `.look` is recorded at `let`-binding sites, and a `case`
    alternative checks its arity against the scrutinee's fields. Each clause is
    written in direct style; `ne_solve` discharges the `NonExpansive` witness
    compositionally from the parts (see `AbsDen/NonExpansive.lean`). -/
@[eval_simp] def eval : Exp → (Env d -n> d)
  | .ref x => ofe_fun ρ => (ρ.get x).getD stuck
  | .lam x body =>
      ofe_fun ρ => fn x (ofe_fun a => step .app2 (eval body ρ[x ↦ a]))
  | .app e x =>
      ofe_fun ρ => (ρ.get x).elim stuck (fun a => step .app1 (apply (eval e ρ) a))
  | .conapp K xs =>
      ofe_fun ρ => ρ[xs]?.elim stuck (fun ds => con K ds)
  | .«case» eₛ alts =>
      ofe_fun ρ => step .case1 (select (eval eₛ ρ)
        (alts.attach.map (fun alt =>
          (alt.1.con, alt.1.vars.length, ofe_fun ds =>
            if ds.length = alt.1.vars.length then
              step .case2 (eval alt.1.rhs ρ[alt.1.vars ↦* ds])
            else stuck))))
  | .«let» x e₁ e₂ =>
      ofe_fun ρ => step .let1 (bind
          (ofe_fun a => eval e₁ ρ[x ↦ step (.look x) a])
          (ofe_fun a => eval e₂ ρ[x ↦ step (.look x) a]))
  termination_by e => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | exact alt_rhs_lt _

end AbsDen
