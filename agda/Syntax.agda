{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary.Base
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Bool
open import Utils.PartialFunction

Var = ℕ
Con = ℕ

vx vy vz vi vf vg : Var
vx = 0
vy = 1
vz = 2
vi = 3
vf = 4
vg = 5

decEq-ℕ : (x y : ℕ) → Dec (x ≡ y)
decEq-ℕ zero zero = yes refl
decEq-ℕ zero (suc y) = no znots
decEq-ℕ (suc y) zero = no snotz
decEq-ℕ (suc x) (suc y) with decEq-ℕ x y 
... | yes p = yes (cong suc p)
... | no np = no (λ p → np (injSuc p))

instance 
  decEq-ℕ-imp : {x y : ℕ} → Dec (x ≡ y)
  decEq-ℕ-imp {x} {y} = decEq-ℕ x y
  
Alt : Set

data Exp : Set where
  ref : Var → Exp
  lam : Var → Exp → Exp
  app : Exp → Var → Exp
  let' : Var → Exp → Exp → Exp
  conapp : Con → List Var → Exp
  case' : Exp → List Alt → Exp

Alt = Con × List Var × Exp

data Val : Exp → Set where
  V-lam : ∀{x e} → Val (lam x e)
  V-conapp : ∀{K addrs} → Val (conapp K addrs)

findAlt : Con → List Alt → Maybe (List Var × Exp)
findAlt _ [] = nothing
findAlt K ((K' , vs , rhs) ∷ xs) with decEq-ℕ K K' 
... | yes _ = just (vs , rhs) 
... | no  _ = findAlt K xs

