module LDLC where

open import Data.List
open import Data.List.All
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Fin.Subset
open import Data.Fin hiding (_≤_)
open import Data.Product

data LTy (nl : ℕ) : Set

-- the index nl stands for the number of labels
data LTy nl where
  Tunit : LTy nl
  Tlabel : Subset nl → LTy nl
  Tfun : LTy nl → LTy nl → LTy nl

{-
 record Π {nl} where
   inductive
  constructor Π[_]_
  field
    snl : Subset nl
    B   : ∀ {l} → l ∈ snl → LTy nl
-}

-- subtype relation
data _≤_ {nl} : LTy nl → LTy nl → Set where
  Sunit  : Tunit ≤ Tunit
  Slabel : ∀ {snl snl'} → snl ⊆ snl' → (Tlabel snl) ≤ (Tlabel snl')
  Sfun   : ∀ {A A' B B'} → A' ≤ A → B ≤ B' → (Tfun A B) ≤ (Tfun A' B')

-- ≤-trans : 

LTEnv : ℕ → Set
LTEnv nl = List (LTy nl)


data _∈`_ {nl : ℕ} : LTy nl → LTEnv nl → Set where
  here  : ∀ {lt φ} → lt ∈` (lt ∷ φ)
  there : ∀ {lt lt' φ} → lt ∈` φ → lt ∈` (lt' ∷ φ)

data LExpr {nl : ℕ} : LTEnv nl → LTy nl → Set where
  Var      : ∀ {φ t} → (x : t ∈` φ) → LExpr φ t
  SubType  : ∀ {A A' φ} →  LExpr φ A → A ≤ A'
                        →  LExpr φ A'
  Lab-I    : ∀ {l snl φ} → l ∈ snl → LExpr φ (Tlabel ⁅ l ⁆)
  Lab-E    : ∀ {snl φ B} → LExpr φ (Tlabel snl)
                         → ∀ l
                         → l ∈ snl
                         → LExpr (Tlabel (⁅ l ⁆) ∷ φ) B 
                         → LExpr φ B
  Pi-I     : ∀ {B A φ}   → LExpr (A ∷ φ) B
                         → LExpr φ (Tfun A B)
  Pi-E     : ∀ {A B φ}  → LExpr φ (Tfun A B)
                        → (ex : LExpr φ A)
                        → LExpr φ B
                 
-- Big step
Val : ∀ {n} → LTy n → Set
Val Tunit = Data.Unit.⊤
Val {n} (Tlabel snl) = Σ (Fin n) (λ l → l ∈ snl)
Val (Tfun ty ty₁) = (Val ty) → (Val ty₁)

coerce : ∀ {nl} {t t' : LTy nl} → t ≤ t' → Val t → Val t'
coerce Sunit v = {!!}
coerce (Slabel x) v = {!!}
coerce (Sfun t≤t' t≤t'') v = {!!}

eval : ∀ {n φ t} → LExpr{n} φ t → All Val φ → Val t
eval e ϱ = {!!}

-- small step
data Val' {n φ} : (t : LTy n) → LExpr {n} φ t → Set where
  Vlab : ∀ {l snl x l∈snl tl≤tout} → Val' (Tlabel x) (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout)
  Vfun : ∀ {ty ty'} → Val' (Tfun ty ty') (SubType (Pi-I {!!}) {!!})

