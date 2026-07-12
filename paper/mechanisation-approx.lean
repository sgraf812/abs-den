theorem usage_approximates_need (k : Nat) (e : Exp) (hb : Barendregt e)
    (x : Var) (n : Nat) :
    U.ofCount (Trace.lookCount x n (D.runAt μ₀ (evalByNeed e Env.empty)))
      ⊑ (evalUsgk k e Env.empty).uses !? x
