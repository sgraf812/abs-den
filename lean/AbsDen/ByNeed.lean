import AbsDen.Semantics
import AbsDen.Trace

/-!
# By-need concrete instance

The by-need domain is heap-threaded: `D n = Heap n → T (Value × Heap) n`.
Following the Agda: `D (ByNeed T) = Heap → T (Value × Heap)`.
-/

abbrev Addr := Nat

namespace ByNeed

/-! ## Heap and domain signature -/

def AddrMap (V : Type) : Type := Std.HashMap Addr V
instance : EmptyCollection (AddrMap V) := ⟨(∅ : Std.HashMap Addr V)⟩
instance : Functor AddrMap where
  map f (m : AddrMap _) := Std.HashMap.fold (fun acc k v => acc.insert k (f v)) ∅ m
instance : LocalFunctor (World.Comp AddrMap) where
  instWorld _ := inferInstance
  property X Y n h := by simp only [World.Comp]; congr 1; exact h n (Nat.le_refl n)

abbrev Heap (D : Nat → Type) : Nat → Type := World.Comp AddrMap D
instance {D : Nat → Type} {n : Nat} : EmptyCollection (Heap D n) := ⟨(∅ : AddrMap (D n))⟩

abbrev D.Sig (X : Nat → Type) : Nat → Type :=
  world(Heap X → T (Value.F.Rep X × Heap X))

instance : LocalFunctor D.Sig := by derive_local_functor

def D := World.Fix D.Sig

instance : World D := inferInstanceAs (World (World.Fix D.Sig))

/-! ## Abbreviations for the value-heap pair -/

/-- The value-heap pair with Rep values (matches D.Sig). -/
abbrev VH := world(Value.F.Rep (▹ D) × Heap (▹ D))

/-! ## Domain operations -/

def D.unfold {n : Nat} (d : D n) (m : Nat) (hm : m ≤ n) (μ : Heap (▹ D) m) : T VH m :=
  World.Fix.unfold d m hm μ

def D.fold {n : Nat} (f : world(Heap (▹ D) → T VH) n) : D n :=
  World.Fix.fold f

def D.ret {n : Nat} (v : Value.F (▹ D) n) : D n :=
  D.fold fun _ _ μ => T.ret (World.restrict (Value.F.toRep _ v), μ)

def D.step {n : Nat} (ev : Event) (dl : ▹ D n) : D n :=
  D.fold fun m _hm μ =>
    T.step ev (Later.hmap m (fun i _hi d =>
      d.unfold i (Nat.le_refl i) (World.restrict μ (by omega))) (World.restrict dl))

def D.invis {n : Nat} (dl : ▹ D n) : D n :=
  D.fold fun m _hm μ =>
    T.fold (.invis (Later.hmap m (fun i _hi d =>
      d.unfold i (Nat.le_refl i) (World.restrict μ (by omega))) (World.restrict dl)))

def D.stuck {n : Nat} : D n := D.ret .stuck

def D.fn {n : Nat} (f : world(D → D) n) : D n :=
  D.ret (.fn (fun m h dl => (Later.hmap m (fun k hk => f k (by omega)) dl)))

def D.con {n : Nat} (K : ConTag) (ds : world(List D) n) : D n :=
  D.ret (.con K (ds.map Later.next))

instance {n : Nat} : Inhabited (D n) := ⟨D.stuck⟩

/-! ## Bind -/

def D.bind {n : Nat} (d : D n) (k : world(Value.F (▹ D) → D) n) : D n :=
  D.fold fun m hm μ =>
    T.bind (d.unfold m (by omega) μ) fun j hj (v, μ') =>
      (k j (by omega) (Value.F.ofRep _ v)).unfold j (Nat.le_refl j) μ'

/-! ## Heap operations -/

partial def Heap.nextFree {n : Nat} (μ : Heap (▹ D) n) : Addr :=
  go 0
where
  go (k : Nat) : Addr :=
    match Std.HashMap.get? μ k with
    | none => k
    | some _ => go (k + 1)

def Heap.set {n : Nat} (μ : Heap (▹ D) n) (a : Addr) (d : ▹ D n) :
    Heap (▹ D) n :=
  Std.HashMap.insert μ a d

/-- Fetch: look up address a in the heap via invisible step. -/
def fetch {n : Nat} (a : Addr) : ▹ D n :=
  Later.next (D.fold fun m' _hm' μ =>
    match Std.HashMap.get? μ a with
    | some d => T.fold (.invis (Later.hmap m' (fun i _hi d' =>
        d'.unfold i (Nat.le_refl i) (World.restrict μ (by omega))) d))
    | none => T.ret (Value.F.toRep _ .stuck, μ))

/-- Memo: wraps thunk with memoization at address a.
    Evaluates thunk, emits `update`, stores memoized value at a. -/
def D.memo {n : Nat} (a : Addr) (d : ▹ D n) : ▹ D n :=
  Later.hmap n (fun m _ dv =>
    D.bind dv fun j _ v =>
      let memoThunk : ▹ D j := D.memo a (Later.next (D.ret (World.restrict v (by omega))))
      D.step .update (Later.next (D.fold fun j' _hj' μ' =>
        T.ret (World.restrict (Value.F.toRep _ v) (by omega),
               Std.HashMap.insert μ' a (World.restrict memoThunk (by omega)))))
  ) d

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
        match alts.find? (fun (p : ConTag × _) => p.1 == K) with
        | some (_, f) =>
          D.invis (Later.hmap j (fun i _h ds' => f i (by omega) ds') (Later.sequence _ ds))
        | none => D.stuck
      | _ => D.stuck
  bind {_n} _m _hm rhs' k _hk body :=
    D.fold fun j hj μ =>
      let a := Heap.nextFree μ
      let rhsThunk : ▹ D j := Later.next (rhs' j (by omega) (D.invis (fetch a)))
      let memoThunk : ▹ D j := D.memo a rhsThunk
      let μ' := Heap.set μ a memoThunk
      (body j (by omega) (D.invis (fetch a))).unfold j (Nat.le_refl j) μ'

/-! ## By-need evaluator -/

def evalByNeed (n : Nat) (e : Exp) : D n :=
  eval (D := D) e n (Nat.le_refl n) Env.empty

/-! ========== Tests ========== -/

instance : ToString Exp := ⟨fun e => toString (repr e)⟩

def idId : Exp := .lam 0 (.ref 0)
def idAppId : Exp := .let' 0 (.lam 1 (.ref 1)) (.app (.ref 0) 0)
def idAppTrue : Exp := .let' 0 (.conapp 1 []) (.app (.lam 1 (.ref 1)) 0)
def idAppIdMemo : Exp := .let' 0 (.app (.lam 1 (.lam 2 (.ref 2))) 0) (.app (.ref 0) 0)

def showValue {n : Nat} : Value.F (Later D) n → String
  | .stuck => "stuck"
  | .fn _ => "fn<...>"
  | .con K ds => s!"con({K}, {ds.length} args)"

partial def showT {n : Nat} (t : T VH n) (fuel : Nat) : String :=
  if fuel = 0 then "..."
  else match T.unfold t with
    | .ret (v, _) => s!"ret({showValue (Value.F.ofRep _ v)})"
    | .step e x =>
      match n with
      | 0 => s!"step({repr (e : Event)}, ·)"
      | _ + 1 => s!"step({repr (e : Event)}, {showT x (fuel - 1)})"
    | .invis x =>
      match n with
      | 0 => s!"invis(·)"
      | _ + 1 => s!"invis({showT x (fuel - 1)})"

def showD {n : Nat} (d : D n) (fuel : Nat) : String :=
  showT (d.unfold n (Nat.le_refl n) ∅) fuel

instance {n : Nat} {α : Type} [Repr α] : Repr (World.Const α n) := inferInstanceAs (Repr α)

partial def traceBisim {n : Nat} (a b : T VH n) : Bool :=
  match T.unfold a, T.unfold b with
  | .ret (va, _), .ret (vb, _) => valBisim (Value.F.ofRep _ va) (Value.F.ofRep _ vb)
  | .step ea xa, .step eb xb => ea == eb && laterBisim xa xb
  | .invis xa, _ => laterBisim xa (Later.next b)
  | _, .invis xb => laterBisim (Later.next a) xb
  | _, _ => false
where
  valBisim {n : Nat} (a b : Value.F (Later D) n) : Bool :=
    match a, b with
    | .stuck, .stuck => true
    | .fn _, .fn _ => true
    | .con Ka dsa, .con Kb dsb =>
      Ka == Kb && dsa.length == dsb.length &&
      (dsa.zip dsb).all fun (da, db) => laterTraceBisim da db
    | _, _ => false
  laterBisim {n : Nat} (a b : Later (T VH) n) : Bool :=
    match n with
    | 0 => true
    | _ + 1 => traceBisim a b
  laterTraceBisim {n : Nat} (a b : Later D n) : Bool :=
    match n with
    | 0 => true
    | _ + 1 => traceBisim (a.unfold _ (Nat.le_refl _) ∅) (b.unfold _ (Nat.le_refl _) ∅)

partial def D.bisim {n : Nat} (a b : D n) : Bool :=
  traceBisim (a.unfold n (Nat.le_refl n) ∅) (b.unfold n (Nat.le_refl n) ∅)

instance {n : Nat} : BEq (D n) := ⟨D.bisim⟩

def D.anyFn {n : Nat} : D n := D.fn (fun _ _ d => D.invis (Later.next d))
def D.ev {n : Nat} (e : Event) (d : D n) : D (n + 1) := D.step e d

def test (exp : Exp) (n : Nat) (expected : D n) : Lean.Meta.MetaM Unit := do
  let actual := evalByNeed n exp
  unless actual == expected do
     throwError s!"Failed for {exp}:\n  expected: {showD expected n}\n  got:      {showD actual n}"

#eval! test idId 10 D.anyFn

#eval! test idAppId 20 <|
  D.ev .let1 <| D.ev .app1 <| D.ev (.look 0) <|
  D.ev .update <| D.ev .app2 <| D.ev (.look 0) <| D.ev .update <| D.anyFn

#eval! test idAppTrue 20 <|
  D.ev .let1 <| D.ev .app1 <|
  D.ev .app2 <| D.ev (.look 0) <| D.ev .update <| D.con 1 []

#eval! test idAppIdMemo 30 <|
  D.ev .let1 <| D.ev .app1 <| D.ev (.look 0) <|
  D.ev .app1 <| D.ev .app2 <| D.ev .update <|
  D.ev .app2 <| D.ev (.look 0) <| D.ev .update <| D.anyFn

end ByNeed
