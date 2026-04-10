import AbsDen.Semantics
import AbsDen.Trace

/-!
# By-name concrete instance

Uses the generic `eval` from Semantics.lean via `Domain D`.

## Domain

`D = World.Fix D.Sig` where `D.Sig X = T (Value.F.Rep X)`.
So `D n ≅ T (Value.F.Rep (▹D)) n` — a trace of values.
-/

/-! ## By-name domain family -/

abbrev D.Sig (X : Nat → Type) : Nat → Type := T (Value.F.Rep X)

instance : LocalFunctor D.Sig := by derive_local_functor

/-- The by-name domain family. -/
def D : Nat → Type := World.Fix D.Sig

instance : World D := inferInstanceAs (World (World.Fix D.Sig))

/-! ## Domain operations -/

/-- Abbreviation for the value Rep type used in traces. -/
abbrev VRep := Value.F.Rep (▹ D)

def D.unfold {n : Nat} (d : D n) : T VRep n := World.Fix.unfold d

def D.fold {n : Nat} (t : T VRep n) : D n := World.Fix.fold t

def D.Later.unfold {n : Nat} (dl : ▹ D n) : ▹ (T VRep) n :=
  Later.map (fun _ => D.unfold) _ dl

def D.Later.fold {n : Nat} (tl : ▹ (T VRep) n) : ▹ D n :=
  Later.map (fun _ => D.fold) _ tl

instance {n : Nat} {D' : Nat → Type} : Inhabited (Value.F D' n) := ⟨.stuck⟩

namespace D

def ret {n : Nat} (v : Value.F (▹ D) n) : D n :=
  fold (T.ret (Value.F.toRep _ v))

def step {n : Nat} (e : Event) (dl : ▹ D n) : D n :=
  fold (T.step e (Later.map (fun _ => D.unfold) _ dl))

def invis {n : Nat} (dl : ▹ D n) : D n :=
  fold (T.fold (.invis (Later.map (fun _ => D.unfold) _ dl)))

def stuck {n : Nat} : D n := ret .stuck

def fn {n : Nat} (f : world(D → D) n) : D n :=
  ret (.fn (fun m h dl => (Later.hmap m (fun k hk => f k (by omega)) dl)))

def con {n : Nat} (K : Con) (ds : world(List D) n) : D n :=
  ret (.con K (ds.map Later.next))

end D

instance {n : Nat} : Inhabited (D n) := ⟨D.stuck⟩

/-! ## D.bind using T.bind -/

def D.bind {n : Nat} (d : D n) (k : world(Value.F (Later D) → D) n) : D n :=
  D.fold (T.bind d.unfold (fun j hj v => (k j hj (Value.F.ofRep _ v)).unfold))

/-! ## Domain instance -/

instance : Domain D where
  step {_} _m _hm ev _k _hk d := D.step ev (Later.next d)
  stuck := D.stuck
  fn {_n} _m _hm f := D.fn f
  apply {_n} _m _hm dv k hk da :=
    D.bind (dv↓) fun j hj v =>
      match v with
      | .fn g => D.invis (g j (Nat.le_refl j) (Later.next (da↓)))
      | _ => D.stuck
  con {_} _m _hm K _k _hk ds := D.con K ds
  select {_} _m _hm dv k hk alts :=
    D.bind (dv↓) fun j hj v =>
      match v with
      | .con K ds =>
        match alts.find? (fun (p : Con × _) => p.1 == K) with
        | some (_, f) =>
          D.invis (Later.hmap j (fun i _h ds' => f i (by omega) ds') (Later.sequence _ ds))
        | none => D.stuck
      | _ => D.stuck
  bind {_n} _m _hm rhs' k _hk body :=
    body k (Nat.le_refl k) (loeb (fun l h d => rhs' l (by omega) (D.invis d)))

/-! ## By-name evaluator -/

def evalByName (n : Nat) (e : Exp) : D n :=
  eval (D := D) e n (Nat.le_refl n) Env.empty

/-! ========== Tests ========== -/

instance {n : Nat} {α : Type} [Repr α] : Repr (World.Const α n) := inferInstanceAs (Repr α)

def showValue {n : Nat} : Value.F (Later D) n → String
  | .stuck => "stuck"
  | .fn _ => "fn<...>"
  | .con K ds => s!"con({K}, {ds.length} args)"

partial def showT {n : Nat} (t : T VRep n) (fuel : Nat) : String :=
  if fuel = 0 then "..."
  else match T.unfold t with
    | .ret v => s!"ret({showValue (Value.F.ofRep _ v)})"
    | .step e x =>
      match n with
      | 0 => s!"step({repr (e : Event)}, ·)"
      | _ + 1 => s!"step({repr (e : Event)}, {showT x (fuel - 1)})"
    | .invis x =>
      match n with
      | 0 => s!"invis(·)"
      | _ + 1 => s!"invis({showT x (fuel - 1)})"

def showD {n : Nat} (d : D n) (fuel : Nat) : String := showT d.unfold fuel

def idId : Exp := .lam 0 (.ref 0)
def idAppId : Exp := .let' 0 (.lam 1 (.ref 1)) (.app (.ref 0) 0)
def idAppTrue : Exp := .let' 0 (.conapp 1 []) (.app (.lam 1 (.ref 1)) 0)
def idAppIdMemo : Exp := .let' 0 (.app (.lam 1 (.lam 2 (.ref 2))) 0) (.app (.ref 0) 0)

/-! ## Step-indexed bisimulation and tests -/

mutual
  def Exp.toString : Exp → String
    | .ref x => s!"ref {x}"
    | .lam x e => s!"λ{x}.{e.toString}"
    | .app e x => s!"({e.toString}) {x}"
    | .let' x e₁ e₂ => s!"let {x} = {e₁.toString} in {e₂.toString}"
    | .conapp K xs => s!"K{K}{xs}"
    | .case' e alts => s!"case {e.toString} of {alts.map Alt.toString}"

  def Alt.toString : Alt → String
    | ⟨K, vars, rhs⟩ => s!"K{K} {vars} → {rhs.toString}"
end

instance : ToString Exp := ⟨Exp.toString⟩

instance {n : Nat} {α : Type} [BEq α] : BEq (World.Const α n) := inferInstanceAs (BEq α)

namespace Bisim

mutual
  partial def trace {n : Nat} (a b : T VRep n) : Bool :=
    match T.unfold a, T.unfold b with
    | .ret va, .ret vb => value (Value.F.ofRep _ va) (Value.F.ofRep _ vb)
    | .step ea xa, .step eb xb => ea == eb && laterTrace xa xb
    | .invis xa, _ => laterTrace xa (Later.next b)
    | _, .invis xb => laterTrace (Later.next a) xb
    | _, _ => false

  partial def value {n : Nat} (a b : Value.F (▹ D) n) : Bool :=
    match a, b with
    | .stuck, .stuck => true
    | .fn _, .fn _ => true
    | .con Ka dsa, .con Kb dsb =>
      Ka == Kb && dsa.length == dsb.length &&
      (dsa.zip dsb).all fun (da, db) => laterTrace (D.Later.unfold da) (D.Later.unfold db)
    | _, _ => false

  partial def laterTrace {n : Nat} (a b : ▹ (T VRep) n) : Bool :=
    match n with
    | 0 => true
    | _ + 1 => trace a b
end

end Bisim

def D.bisim {n : Nat} (a b : D n) : Bool := Bisim.trace a.unfold b.unfold

instance {n : Nat} : BEq (D n) := ⟨D.bisim⟩

def D.anyFn {n : Nat} : D n := D.fn (fun _ _ _ => default)

def D.ev {n : Nat} (e : Event) (d : D n) : D (n + 1) := D.step e d

def test (exp : Exp) (n : Nat) (expected : D n) : Lean.Meta.MetaM Unit := do
  let actual := evalByName n exp
  unless actual == expected do
     throwError s!"Failed for {exp}:\n  expected: {showD expected n}\n  got:      {showD actual n}"

#eval! test idId 10 D.anyFn

#eval! test idAppId 10 <|
  D.ev .let1 <| D.ev .app1 <| D.ev (.look 0) <|
  D.ev .app2 <| D.ev (.look 0) <| D.anyFn

#eval! test idAppTrue 10 <|
  D.ev .let1 <| D.ev .app1 <|
  D.ev .app2 <| D.ev (.look 0) <| D.con 1 []

#eval! test idAppIdMemo 20 <|
  D.ev .let1 <| D.ev .app1 <| D.ev (.look 0) <|
  D.ev .app1 <| D.ev .app2 <|
  D.ev .app2 <| D.ev (.look 0) <|
  D.ev .app1 <| D.ev .app2 <| D.anyFn
