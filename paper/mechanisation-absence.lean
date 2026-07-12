theorem absence (k : Nat) (e : Exp) (hb : Barendregt e) (x : Var)
    (habs : (evalUsgk k e Env.empty).uses !? x = U.u0) (n : Nat) :
    Trace.lookCount x n (D.runAt μ₀ (evalByNeed e Env.empty)) = 0
