import AbsDen.World.Derive
import AbsDen.Syntax

/-! # Tests for World and LocalFunctor derive handlers -/

-- Test 1: No family params — deriving World
inductive SimpleF (n : Nat) where
  | leaf : Nat → SimpleF n
  | empty : SimpleF n
  deriving World

-- Test 2: One family param — deriving World and LocalFunctor
inductive TreeF (D : Nat → Type) (n : Nat) where
  | leaf : Nat → TreeF D n
  | node : D n → D n → TreeF D n
  deriving World, LocalFunctor
example : LocalFunctor TreeF.Rep := inferInstance
example (D : Nat → Type) (d1 d2 : D 0) :
    TreeF.ofRep D (TreeF.toRep D (TreeF.node d1 d2)) = TreeF.node d1 d2 := by rfl

-- Test 3: Two family params — deriving World and LocalFunctor
inductive TF' (V W : Nat → Type) (n : Nat) where
  | ret : V n → TF' V W n
  | step : Event → W n → TF' V W n
  deriving World, LocalFunctor
example (V : Nat → Type) [World V] : LocalFunctor (TF'.Rep V) := inferInstance

-- Test 4: Single constructor — deriving World and LocalFunctor
inductive PairF (D : Nat → Type) (n : Nat) where
  | mk : D n → Nat → PairF D n
  deriving World, LocalFunctor
example : LocalFunctor PairF.Rep := inferInstance
example (D : Nat → Type) (d : D 0) :
    PairF.ofRep D (PairF.toRep D (PairF.mk d 7)) = PairF.mk d 7 := by rfl

-- Test 5: Two constructors with Comp — deriving World and LocalFunctor
inductive ValF' (D : Nat → Type) (n : Nat) where
  | stuck : ValF' D n
  | con : ConTag → world(List (Var × D)) n → ValF' D n
  deriving World, LocalFunctor
example : LocalFunctor ValF'.Rep := inferInstance

-- Test 6: Comp lifting (List) — deriving World and LocalFunctor
inductive ListTreeF (D : Nat → Type) (n : Nat) where
  | leaf : ListTreeF D n
  | node : world(List D) n → ListTreeF D n
  deriving World, LocalFunctor
example : LocalFunctor ListTreeF.Rep := inferInstance

-- Test 7: World instance synthesis
example (D : Nat → Type) [World D] : World (TF' D (World.Const Nat)) := inferInstance
