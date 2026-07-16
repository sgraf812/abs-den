def eval {d : Type} [OFE d] [Domain d] : Exp → (Env d -n> d)
  | .ref x => ofe_fun ρ => (ρ.get x).getD stuck
  | .lam x body => ofe_fun ρ => fn x (ofe_fun a => step .app2 (eval body ρ[x ↦ a]))
  | .app e x => ofe_fun ρ => (ρ.get x).elim stuck (fun a => step .app1 (apply (eval e ρ) a))
  | .conapp K xs => ofe_fun ρ => ρ[xs]?.elim stuck (fun ds => con K ds)
  | .«case» eₛ alts => ofe_fun ρ =>
    step .case1 (select (eval eₛ ρ) (alts.attach.map fun alt =>
      (alt.1.con, alt.1.vars.length, ofe_fun ds =>
        if ds.length = alt.1.vars.length
        then step .case2 (eval alt.1.rhs ρ[alt.1.vars ↦* ds])
        else stuck)))
  | .«let» x e₁ e₂ => ofe_fun ρ =>
    step .let1 (bind (ofe_fun a => eval e₁ ρ[x ↦ step (.look x) a])
                     (ofe_fun a => eval e₂ ρ[x ↦ step (.look x) a]))
