{-# OPTIONS --cubical --rewriting --guarded #-}
module Semantics.Transition where

open import Utils.Later
open import Utils.PartialFunction
open import Syntax
open import Data.List
open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Bool
open import Cubical.Core.Everything hiding (_[_↦_])
open import Cubical.Foundations.Prelude hiding (_[_↦_]; _∎)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Relation.Nullary.Base

Env = Var ⇀ Addr
Heap = Addr ⇀ Env × Exp

data Frame : Set where
  apply : Addr → Frame 
  select : Env → List Alt → Frame
  update : Addr → Frame

Cont = List Frame

record State : Set where
  inductive
  constructor <_,_,_,_>
  field
    ctrl : Exp
    env  : Env
    heap : Heap
    cont : Cont

infix 4 _↪_

data _↪_ : State → State → Set where
  bind : ∀{x e₁ e₂ ρ μ κ a p} 
    → ((a , p) ≡ Addr.alloc μ)
    -------------------
    → < let' x e₁ e₂ , ρ , μ , κ > ↪ < e₂ , ρ [ x ↦ a ] , μ [ a ↦ (ρ [ x ↦ a ] , e₁) ] , κ >
  
  app1 : ∀{x e ρ μ κ a}     
    → (ρ x ≡ just a)
    → < app e x , ρ , μ , κ > ↪ < e , ρ , μ , apply a ∷ κ >
  
  case1 : ∀{e alts ρ μ κ}     
    → < case' e alts , ρ , μ , κ > ↪ < e , ρ , μ , select ρ alts ∷ κ >

  look : ∀{x a e ρ ρ' μ κ}     
    → (ρ x ≡ just a)
    → (μ a ≡ just (ρ' , e))
    → < ref x , ρ , μ , κ > ↪ < e , ρ' , μ , update a ∷ κ >
  
  app2 : ∀{x e ρ μ κ a}     
    → < lam x e , ρ , μ , apply a ∷ κ > ↪ < e , ρ [ x ↦ a ] , μ , κ >

  case2 : ∀{K xs addrs alts ys rhs ρ ρ' μ κ}     
    → (pmap ρ xs ≡ just addrs)
    → (findAlt K alts ≡ just (ys , rhs))
    → length xs ≡ length ys
    → < conapp K xs , ρ , μ , select ρ' alts ∷ κ > ↪ < rhs , ρ' [ ys ↦* addrs ] , μ , κ >
    
  upd : ∀{v ρ μ κ a}     
    → Val v
    → < v , ρ , μ , update a ∷ κ > ↪ < v , ρ , μ [ a ↦ (ρ , v) ] , κ >

infix  2 _↪*_
infix  1 begin_
infixr 2 _↪⟨_⟩_
infixr 2 _↪0≡⟨_⟩_
infix  3 _∎

data _↪*_ : State → State → Set where
  _∎ : ∀ M
      ---------
    → M ↪* M

  _↪▹⟨_⟩_ : ∀ L {M N}
    → L ↪ M
    → ▹ (M ↪* N)
      ---------
    → L ↪* N
    
begin_ : ∀ {M N}
  → M ↪* N
    ------
  → M ↪* N
begin M↪*N = M↪*N

_↪⟨_⟩_ : ∀ L {M N}
  → L ↪ M
  → (M ↪* N)
    ---------
  → L ↪* N
L ↪⟨ L↪M ⟩ M↪*N = L ↪▹⟨ L↪M ⟩ (next M↪*N)

_↪0≡⟨_⟩_ : ∀ L {M N}
    → L ≡ M
    → M ↪* N
      ---------
    → L ↪* N
_↪0≡⟨_⟩_ L {_} {N} L≡M M↪*N = transport (cong (λ x → x ↪* N) (sym L≡M)) M↪*N    

module Ex where
  a : Addr
  a = fst (Addr.alloc (empty-pfun {_} {Env × Exp}))
  ρ ρ₂ : Env
  ρ = empty-pfun [ vi ↦ a ]
  ρ₂ = ρ [ vx ↦ a ]
  μ : Heap
  μ = empty-pfun [ a ↦ (ρ , lam vx (ref vx)) ]

  noop : μ [ a ↦ (ρ , lam vx (ref vx)) ] ≡ μ  
  noop = idem-↦₂ empty-pfun a

  example :  
    < let' vi (lam vx (ref vx)) (app (ref vi) vi), empty-pfun , empty-pfun , [] >
    ↪* 
    < lam vx (ref vx) , ρ , μ , [] >
  example = 
    begin 
      < let' vi (lam vx (ref vx)) (app (ref vi) vi) , empty-pfun , empty-pfun , [] >
    ↪⟨ bind refl ⟩
      < app (ref vi) vi , ρ , μ , [] >
    ↪⟨ app1 refl ⟩
      < ref vi , ρ , μ , apply a ∷ [] >
    ↪⟨ look refl (apply-↦ empty-pfun a) ⟩
      < lam vx (ref vx) , ρ , μ , update a ∷ apply a ∷ [] >
    ↪⟨ upd V-lam ⟩
      < lam vx (ref vx) , ρ , μ [ a ↦ (ρ , lam vx (ref vx)) ] , apply a ∷ [] >
    ↪0≡⟨ cong (λ x → < lam vx (ref vx) , ρ , x , apply a ∷ [] >) noop ⟩
      < lam vx (ref vx) , ρ , μ , apply a ∷ [] >
    ↪⟨ app2 ⟩
      < ref vx , ρ₂ , μ , [] >
    ↪⟨ look refl (apply-↦ empty-pfun a) ⟩
      < lam vx (ref vx) , ρ , μ , update a ∷ [] >
    ↪⟨ upd V-lam ⟩
      < lam vx (ref vx) , ρ , μ [ a ↦ (ρ , lam vx (ref vx)) ] , [] >
    ↪0≡⟨ cong (λ x → < lam vx (ref vx) , ρ , x , [] >) noop ⟩
      < lam vx (ref vx) , ρ , μ , [] >
    ∎

data ℕω : Set where
  zero : ℕω
  suc : ▹ ℕω → ℕω

data Finω : ℕω → Set where
  zero : ∀ {n} → Finω (suc n) 
  suc  : ∀ {n} → (i : Finω (n unsafe⋄)) → Finω (suc n) -- This use of unsafe⋄ is safe, because the Finω still is ultimately finite

Seq : Set → Set
Seq A = Σ[ n ∈ ℕω ] (Finω n → A)

-- LKTrace = Σ (λ (seq : Seq State) → fst seq ≢ zero × (∀ {i : Finω (fst seq)} {j : Finω (fst seq)} {p : j ≡ suc i} → snd seq i ↪ snd seq j))

_extends_ : Cont → Cont → Set
κ₁ extends κ₂ = Suffix _≡_ κ₂ κ₁

data _deep-↪*_ : ∀ {σ₁ σ₂} → Cont → (σ₁ ↪* σ₂) → Set where
  deep-end : ∀ {κ σ} → ∀{ext : (State.cont σ) extends κ} → κ deep-↪* (σ ∎)
  deep-step : ∀ {κ σ₁ σ₂ σ₃} → ∀ {σ₁↪σ₂ : σ₁ ↪ σ₂} → ∀ {▹σ₂↪*σ₃ : ▹ (σ₂ ↪* σ₃)} → ∀{ext : (State.cont σ₁) extends κ} → ((@tick x : Tick) -> κ deep-↪* (▹σ₂↪*σ₃ x)) → κ deep-↪* (σ₁ ↪▹⟨ σ₁↪σ₂ ⟩ ▹σ₂↪*σ₃ )

interior : ∀ {σ₁ σ₂} → (σ₁ ↪* σ₂) → Set
interior {σ₁} τ = State.cont σ₁ deep-↪* τ  

-- balanced : ∀ {σ₁ σ₂} → (σ₁ ↪* σ₂) → Set
-- balanced = ? 

