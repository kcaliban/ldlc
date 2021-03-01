-- {-# OPTIONS --show-implicit #-} -- in case of emergency
module ldlc-algo where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Vec hiding (_++_ ; length)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Sum

open import aux

----------------------------------------------------------------------

module syntx where
  data Exp {n : ℕ} : Set
  data Val {n : ℕ} : Exp {n} → Set
  data Ty {n : ℕ} : Set

  data Exp {n} where
    Var : ℕ → Exp {n}
    UnitE : Exp {n}
    Abs : Exp {n} → Exp {n}
    App : {e : Exp {n}} → Exp {n} → Val e → Exp {n}
    LabI : Fin n → Exp {n}
    CaseE : {s : Subset n} {e : Exp {n}} → Val e → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    ProdV : {e : Exp {n}} → Val e → Exp {n} → Exp {n}
    LetP : Exp {n} → Exp {n} → Exp {n}
    LetE : Exp {n} → Exp {n} → Exp {n}

  data Val {n} where
    VUnit : Val UnitE
    VVar : {i : ℕ} → Val (Var i)
    VLab : {x : Fin n} → Val (LabI x)
    VFun : {N : Exp} → Val (Abs N)
    VProd : {e e' : Exp} → (v : Val e) → Val e' → Val (ProdV v e')

  data Ty {n} where
    UnitT : Ty
    Single : {e : Exp {n}} → Val e → Ty {n} → Ty
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    CaseT : {s : Subset n} {e : Exp {n}} → Val e → (f : ∀ l → l ∈ s → Ty {n}) → Ty 

  -- Useful shorthands
  data notSingle {n : ℕ} : Ty {n} → Set where
    notsingle : {A : Ty {n}} → (∀ e B → (W : Val e) → ¬ (A ≡ Single{e = e} W B)) → notSingle A

  notsingle-label : {n : ℕ} {L : Subset n} → notSingle (Label L)
  notsingle-label {n} {L} = notsingle λ e B W ()

  -- variable in expression
  data _∈`_ {n : ℕ} : ℕ → Exp {n} → Set where
    in-var : {x : ℕ} → x ∈` (Var x)
    in-abs : {x : ℕ} {e : Exp {n}} → x ∈` e → (ℕ.suc x) ∈` (Abs e)
    in-app : {x : ℕ} {e e' : Exp {n}} {v : Val e'} → x ∈` e ⊎ x ∈` e' → x ∈` App e v
    in-casee : {x : ℕ} {s : Subset n} {f : (∀ l → l ∈ s → Exp {n})} {e : Exp {n}} {v : Val e} → (∃₂ λ l i → x ∈` (f l i)) ⊎ x ∈` e → x ∈` CaseE v f
    in-prod : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` Prod e e'
    in-prodv : {x : ℕ} {e e' : Exp {n}} {v : Val e} → x ∈` e ⊎ x ∈` e' → x ∈` ProdV v e'  -- (Pair-A-I => e' has 0 substituted away => just x, not suc x)
    in-letp : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc (ℕ.suc x)) ∈` e' → x ∈` LetP e e'
    in-lete : {x : ℕ} {e e' : Exp {n}} → x ∈` e ⊎ (ℕ.suc x) ∈` e' → x ∈` LetE e e'

  -- variable in type
  data _∈`ᵀ_ {n : ℕ} : ℕ → Ty {n} → Set where
    in-single : {x : ℕ} {e : Exp {n}} {v : Val e} {A : Ty {n}} → x ∈` e ⊎ x ∈`ᵀ A → x ∈`ᵀ Single v A
    in-pi : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ n ∈`ᵀ B → n ∈`ᵀ Pi A B
    in-pigma : {x : ℕ} {A B : Ty {n}} → n ∈`ᵀ A ⊎ n ∈`ᵀ B → n ∈`ᵀ Sigma A B
    in-case : {x : ℕ} {s : Subset n} {f : ∀ l → l ∈ s → Ty {n}} {e : Exp {n}} {v : Val e} → (∃₂ λ l i → x ∈`ᵀ (f l i)) ⊎ x ∈` e → x ∈`ᵀ CaseT v f

----------------------------------------------------------------------
----------------------------------------------------------------------

module substitution where
  ---- Substitution and Shifting
  open syntx

  ↑ᴺ_,_[_] : ℤ → ℕ → ℕ → ℕ
  ↑ᴺ d , c [ x ]
    with (x <ᴺ? c)
  ...  | yes p = x
  ...  | no ¬p = ∣ ℤ.pos x +ᶻ d ∣

  ↑_,_[_] : ∀ {n} → ℤ → ℕ → Exp {n} → Exp {n}
  shift-val : ∀ {n d c} {e : Exp {n}} → Val e → Val (↑ d , c [ e ])

  ↑ d , c [ UnitE ] = UnitE
  ↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t v ] = App (↑ d , c [ t ]) (shift-val{d = d}{c = c} v)
  ↑ d , c [ LabI x ] = LabI x
  ↑ d , c [ CaseE{e = e} V f ] = CaseE (shift-val{d = d}{c = c} V) (λ l x → ↑ d , c [ f l x ])
  ↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ ProdV e e' ] = ProdV (shift-val{d = d}{c = c} e) (↑ d , c [ e' ])
  ↑ d , c [ LetP e e' ] = LetP (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])
  ↑ d , c [ LetE e e' ] = LetE (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

  shift-val {n} {d} {c} {.UnitE} VUnit = VUnit
  shift-val {n} {d} {c} {.(Var _)} VVar = VVar
  shift-val {n} {d} {c} {.(LabI _)} VLab = VLab
  shift-val {n} {d} {c} {.(Abs _)} VFun = VFun
  shift-val {n} {d} {c} {.(ProdV V _)} (VProd V V₁) = VProd (shift-val V) (shift-val V₁)

  -- shorthands
  ↑¹[_] : ∀ {n} → Exp {n} → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑ⱽ¹[_] : ∀ {n} {e : Exp {n}} → Val e → Val (↑ (ℤ.pos 1) , 0 [ e ])
  ↑ⱽ¹[_] {n} {e} v = shift-val v

  ↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  [_↦_]_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Exp {n} → Exp {n}
  sub-val : ∀ {n k} {e e' : Exp {n}} {v : Val e'} → Val e → Val ([ k ↦ v ] e)
  [_↦_]_ {n} {e} k v (Var x)
    with (_≟ᴺ_ x k)
  ...  | yes p = e
  ...  | no ¬p = Var x
  [ k ↦ v ] UnitE = UnitE
  [ k ↦ v ] Abs e = Abs (([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e))
  [_↦_]_ {n} {e'} k v (App{e = e₁} e v') = App ([ k ↦ v ] e) (sub-val{n}{k}{e₁}{e'}{v} v') -- ([ k ↦ v ] e₁)
  [ k ↦ v ] LabI x = LabI x
  [_↦_]_ {n} {e} k v (CaseE v' f) = CaseE (sub-val{n}{k}{e' = e}{v = v} v') (λ l x₁ → [ k ↦ v ] (f l x₁))
  [ k ↦ v ] Prod e e₁ = Prod ([ k ↦ v ] e) ([ ℕ.suc k ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)
  [_↦_]_ {n} {e} k v (ProdV v' e') = ProdV (sub-val{n}{k}{e' = e}{v = v} v') ([ k ↦ v ] e')
  [ k ↦ v ] LetP e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ shift-val{d = ℤ.pos 2}{c = 0} v ] e₁)
  [ k ↦ v ] LetE e e₁ = LetE ([ k ↦ v ] e) ([ (ℕ.suc k) ↦ shift-val{d = ℤ.pos 1}{c = 0} v ] e₁)

  sub-val {n} {k} {.UnitE} {e'} {v} VUnit = VUnit
  sub-val {n} {k} {(Var i)} {e'} {v} VVar
    with (_≟ᴺ_ i k)
  ...  | yes p = v
  ...  | no ¬p = VVar
  sub-val {n} {k} {.(LabI _)} {e'} {v} VLab = VLab
  sub-val {n} {k} {.(Abs _)} {e'} {v} VFun = VFun
  sub-val {n} {k} {.(ProdV v' _)} {e'} {v} (VProd v' v'') = VProd (sub-val v') (sub-val v'')

  -- type substitution
  [_↦_]ᵀ_ : ∀ {n} {e : Exp {n}} → ℕ → Val e → Ty {n} → Ty {n}
  [ k ↦ s ]ᵀ UnitT = UnitT
  [_↦_]ᵀ_ {n} {e} k v (Single x T) = Single (sub-val{n}{k}{e' = e}{v = v} x) ([ k ↦ v ]ᵀ T)
  [ k ↦ s ]ᵀ Label x = Label x
  [ k ↦ s ]ᵀ Pi T T₁ = Pi ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [ k ↦ s ]ᵀ Sigma T T₁ = Sigma ([ k ↦ s ]ᵀ T) ([ k ↦ s ]ᵀ T₁)
  [_↦_]ᵀ_ {n} {e} k v (CaseT x f) = CaseT (sub-val{n}{k}{e' = e}{v = v} x) λ l x₁ → [ k ↦ v ]ᵀ (f l x₁)

----------------------------------------------------------------------
----------------------------------------------------------------------

module typing where
  open syntx
  open substitution

  -- Type environment
  data TEnv {n : ℕ} : Set where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty {n}) (Γ : TEnv {n}) → TEnv

  _++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
  [] ++ Γ' = Γ'
  ⟨ T , Γ ⟩ ++ Γ' = ⟨ T , Γ ++ Γ' ⟩

  ++-assoc : {n : ℕ} {Γ Γ' Γ'' : TEnv {n}} → Γ ++ (Γ' ++ Γ'') ≡ (Γ ++ Γ') ++ Γ''
  ++-assoc {n} {[]} {Γ'} {Γ''} = refl
  ++-assoc {n} {⟨ T , Γ ⟩} {Γ'} {Γ''} = cong (λ x → ⟨ T , x ⟩) (++-assoc{n}{Γ}{Γ'}{Γ''})

  length : {n : ℕ} → TEnv {n} → ℕ
  length {n} [] = zero
  length {n} ⟨ T , Γ ⟩ = ℕ.suc (length Γ)

  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set where
    here : {T : Ty} {Γ : TEnv} → 0 ∶ T ∈ ⟨ T , Γ ⟩
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩

  ---- Algorithmic Typing
  -- Type environment formation
  data ⊢_ok {n : ℕ} : TEnv {n} → Set
  -- Type formation
  data _⊢_ {n : ℕ} : TEnv {n}→ Ty {n} → Set
  -- Type synthesis
  data _⊢_⇒_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
  -- Type check
  data _⊢_⇐_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
  -- Check subtype (⇐ instead of ⇒?)
  data _⇒_≤_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
  -- Unfolding (e.g. CaseT ... ⇓ T)
  data _⊢_⇓_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
  -- Conversion
  data _⇒_≡_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set

  -- Implementations
  data ⊢_ok {n} where
    empty : ⊢ [] ok
    entry : {Γ : TEnv {n}} {A : Ty {n}} → ⊢ Γ ok → Γ ⊢ A → ⊢ ⟨ A , Γ ⟩ ok

  data _⊢_ {n} where
    UnitF : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitT
    LabF : {Γ : TEnv {n}} {L : Subset n} → ⊢ Γ ok → Γ ⊢ Label L
    PiF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Pi A B
    SigmaF : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ A → ⟨ A , Γ ⟩ ⊢ B → Γ ⊢ Sigma A B
    SingleF : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} → ⊢ Γ ok → Γ ⊢ e ⇐ A → notSingle A → Γ ⊢ Single V A
    CaseF : {Γ : TEnv {n}} {L : Subset n} {e : Exp {n}} {V : Val e} {f : ∀ l → l ∈ L → Ty {n}} {f-ok : ∀ l → (i : l ∈ L) → Γ ⊢ (f l i)} → Γ ⊢ e ⇐ Label L → Γ ⊢ CaseT V f

  data _⊢_⇐_ {n} where
    SubTypeA : {Γ : TEnv {n}} {A B : Ty {n}} {M : Exp {n}}
               → Γ ⊢ M ⇒ A
               → Γ ⇒ A ≤ B
               → Γ ⊢ M ⇐ B

  data _⇒_≤_ {n} where
    ASubUnit : {Γ : TEnv {n}} → Γ ⇒ UnitT ≤ UnitT
    ASubLabel : {Γ : TEnv {n}} {L L' : Subset n} → L ⊆ L' → Γ ⇒ Label L ≤ Label L'
    ASubSingle : {Γ : TEnv {n}} {A B : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⇒ A ≤ B → Γ ⇒ Single V A ≤ B
    ASubPi : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
             → Γ ⇒ A' ≤ A
             → ⟨ A' , Γ ⟩ ⇒ B ≤ B'
             → Γ ⇒ Pi A B ≤ Pi A' B'
    ASubSigma : {Γ : TEnv {n}} {A A' B B' : Ty {n}}
                → Γ ⇒ A ≤ A'
                → ⟨ A , Γ ⟩ ⇒ B ≤ B'
                → Γ ⇒ Sigma A B ≤ Sigma A' B'
    ASubCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {V : Val e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ (f l ins) ≤ B
                 → Γ ⇒ CaseT V f ≤ B
    ASubCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {l : Fin n} {L L' : Subset n} {f : ∀ l → l ∈ L → Ty {n}} {ins : l ∈ L}
                 → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                 → L' ⊆ L
                 → Γ ⇒ A ≤ (f l ins)
                 → Γ ⇒ A ≤ CaseT V f
    ASubCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ (f l i) ≤ B)
               → (Γ' ++ ⟨ D , Γ ⟩) ⇒ CaseT (VVar{i = length Γ'}) f ≤ B
    ASubCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ A ≤ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩) ⇒ A ≤ CaseT (VVar{i = length Γ'}) f               
             
  data _⊢_⇒_ {n} where
    VarA : {Γ : TEnv {n}} {A : Ty {n}} {x : ℕ} → ⊢ Γ ok → x ∶ A ∈ Γ → Γ ⊢ Var x ⇒ A
    UnitAI : {Γ : TEnv {n}} → ⊢ Γ ok → Γ ⊢ UnitE ⇒ UnitT
    LabAI : {Γ : TEnv {n}} {l : Fin n} → ⊢ Γ ok → Γ ⊢ LabI l ⇒ Single (VLab{x = l}) (Label ⁅ l ⁆)
    LabAEl : {Γ : TEnv {n}} {B : Ty {n}} {L L' : Subset n} {l : Fin n} {e : Exp {n}} {V : Val e} {ins : l ∈ L} {f : ∀ l → l ∈ L → Exp {n}}
             → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
             → L' ⊆ L
             → Γ ⊢ (f l ins) ⇒ B
             → Γ ⊢ CaseE V f ⇒ B
    -- unification has problems with arbitrary functions, hence θ
    -- see https://lists.chalmers.se/pipermail/agda/2020/012293.html
    LabAEx : {Γ Γ' Θ : TEnv {n}} {D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Exp {n}} {f-t : ∀ l → l ∈ L → Ty {n}} {eq : Θ ≡ (Γ' ++ ⟨ D , Γ ⟩)}
             → Γ ⇒ D ≤ Label L
             → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ (Single (VLab{x = l}) (Label L)) , Γ ⟩) ⊢ (f l i) ⇒ (f-t l i))
             → Θ ⊢ CaseE (VVar{i = length Γ'}) f ⇒ CaseT (VVar{i = length Γ'}) f-t
    PiAI : {Γ : TEnv {n}} {A B : Ty {n}}  {M : Exp {n}} → ⟨ A , Γ ⟩ ⊢ M ⇒ B → Γ ⊢ Abs M ⇒ Pi A B
    PiAE : {Γ : TEnv {n}} {A B D : Ty {n}} {M e : Exp {n}} {V : Val e}
           → Γ ⊢ M ⇒ D
           → Γ ⊢ D ⇓ Pi A B
           → Γ ⊢ e ⇐ A
           → Γ ⊢ ([ 0 ↦ V ]ᵀ B)
           → Γ ⊢ App M V ⇒ ([ 0 ↦ V ]ᵀ B)
    SigmaAI : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
              → Γ ⊢ M ⇐ A
              → ⟨ A , Γ ⟩ ⊢ N ⇒ B
              → Γ ⊢ Prod M N ⇒ Sigma A B
    PairAI : {Γ : TEnv {n}} {A B : Ty {n}} {e N : Exp {n}} {V : Val e}
             → Γ ⊢ e ⇒ A
             → Γ ⊢ N ⇒ B
             → Γ ⊢ ProdV V N ⇒ Sigma A B
    SigmaAE : {Γ : TEnv {n}} {A B C D : Ty {n}} {M N : Exp {n}}
            → Γ ⊢ M ⇒ D
            → Γ ⊢ D ⇓ Sigma A B
            → ⟨ B , ⟨ A , Γ ⟩ ⟩ ⊢ N ⇒ C
            → (¬ (0 ∈`ᵀ C)) × (¬ (1 ∈`ᵀ C))
            → Γ ⊢ LetP M N ⇒ C
    Let : {Γ : TEnv {n}} {A B : Ty {n}} {M N : Exp {n}}
          → ¬(0 ∈`ᵀ B)
          → Γ ⊢ M ⇒ A
          → ⟨ A , Γ ⟩ ⊢ N ⇒ B
          → Γ ⊢ LetE M N ⇒ B

  data _⊢_⇓_ {n} where
    AURefl-U : {Γ : TEnv {n}} → Γ ⊢ UnitT ⇓ UnitT
    AURefl-L : {Γ : TEnv {n}} {L : Subset n} → Γ ⊢ Label L ⇓ Label L
    AURefl-P : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Pi A B ⇓ Pi A B
    AURefl-S : {Γ : TEnv {n}} {A B : Ty {n}} → Γ ⊢ Sigma A B ⇓ Sigma A B
    AUSingle : {Γ : TEnv {n}} {A D : Ty {n}} {e : Exp {n}} {V : Val e} → Γ ⊢ A ⇓ D → Γ ⊢ Single V A ⇓ D
    AUCaseL : {Γ : TEnv {n}} {D : Ty {n}} {l : Fin n} {L L' : Subset n} {ins : l ∈ L} {f : ∀ l → l ∈ L → Ty {n}} {e : Exp {n}} {V : Val e}
              → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
              → L' ⊆ L
              → Γ ⊢ (f l ins) ⇓ D
              → Γ ⊢ CaseT V f ⇓ D
    AUCaseX-P : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Pi (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ A ≡ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (VVar{i = length Γ'}) fᴮ ⇓ Pi A (CaseT (VVar{i = length Γ'}) fᴰ)
    AUCaseX-S : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {fᴬ fᴮ fᴰ : (∀ l → l ∈ L → Ty {n})}
              → Γ ⇒ D ≤ Label L
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⊢ (fᴮ l i) ⇓ Sigma (fᴬ l i) (fᴰ l i))
              → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ A ≡ (fᴬ l i))
              → (Γ' ++ ⟨ D , Γ ⟩) ⊢ CaseT (VVar{i = length Γ'}) fᴮ ⇓ Sigma A (CaseT (VVar{i = length Γ'}) fᴰ)

  data _⇒_≡_ {n} where
    AConvUnit : {Γ : TEnv {n}} → Γ ⇒ UnitT ≡ UnitT
    AConvLabel : {Γ : TEnv {n}} {L : Subset n} → Γ ⇒ Label L ≡ Label L
    AConvSingle : {Γ : TEnv {n}} {A : Ty} {e : Exp {n}} {V : Val e} {j : Γ ⊢ Single V A} → Γ ⇒ Single V A ≡ Single V A
    AConvPi : {Γ : TEnv {n}} {A A' B B' : Ty} → Γ ⇒ A ≡ A' → ⟨ A' , Γ ⟩ ⇒ B ≡ B' → Γ ⇒ Pi A B ≡ Pi A' B'
    AConvSigma : {Γ : TEnv {n}} {A A' B B' : Ty} → Γ ⇒ A ≡ A' → ⟨ A , Γ ⟩ ⇒ B ≡ B' → Γ ⇒ Sigma A B ≡ Sigma A' B'
    AConvCaseLL : {Γ : TEnv {n}} {B : Ty {n}} {e : Exp {n}} {V : Val e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                  → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                  → L' ⊆ L
                  → Γ ⇒ (f l ins) ≡ B
                  → Γ ⇒ CaseT V f ≡ B
    AConvCaseLR : {Γ : TEnv {n}} {A : Ty {n}} {e : Exp {n}} {V : Val e} {L L' : Subset n} {f : (∀ l → l ∈ L → Ty)} {l : Fin n} {ins : l ∈ L}
                  → Γ ⊢ e ⇒ Single (VLab{x = l}) (Label L')
                  → L' ⊆ L
                  → Γ ⇒ A ≡ (f l ins)
                  → Γ ⇒ A ≡ CaseT V f               
    AConvCaseXL : {Γ Γ' : TEnv {n}} {B D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ (f l i) ≡ B)
               → (Γ' ++ ⟨ D , Γ ⟩) ⇒ CaseT (VVar{i = length Γ'}) f ≡ B
    AConvCaseXR : {Γ Γ' : TEnv {n}} {A D : Ty {n}} {L : Subset n} {f : ∀ l → l ∈ L → Ty {n}}
               → Γ ⇒ D ≤ Label L
               → (∀ l → (i : l ∈ L) → (Γ' ++ ⟨ Single (VLab{x = l}) (Label L) , Γ ⟩) ⇒ A ≡ (f l i))
               → (Γ' ++ ⟨ D , Γ ⟩) ⇒ A ≡ CaseT (VVar{i = length Γ'}) f

----------------------------------------------------------------------
----------------------------------------------------------------------

module semantics where
  open syntx
  open substitution

  data _↠_ {n : ℕ} : Exp {n} → Exp {n} → Set where
    ξ-App : {e₁ e₁' e : Exp {n}} {v : Val e} → e₁ ↠ e₁' → App e₁ v ↠ App e₁' v
    ξ-LetE : {e₁ e₁' e : Exp {n}} → e₁ ↠ e₁' → LetE e₁ e ↠ LetE e₁' e
    ξ-Prod : {e₁ e₁' e : Exp {n}} → e₁ ↠ e₁' → Prod e₁ e ↠ Prod e₁' e
    ξ-ProdV : {e e₂ e₂' : Exp {n}} {v : Val e} → e₂ ↠ e₂' → ProdV v e₂ ↠ ProdV v e₂'
    ξ-LetP : {e₁ e₁' e₂ : Exp {n}} → e₁ ↠ e₁' → LetP e₁ e₂ ↠ LetP e₁' e₂
    β-App : {e e' : Exp {n}} → (v : Val e') → (App (Abs e) v) ↠ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e) ])
    β-Prod : {e e' : Exp {n}} {v : Val e} → Prod e e' ↠ ProdV v (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
    β-LetE : {e e' : Exp {n}} → (v : Val e) → LetE e e' ↠ (↑⁻¹[ ([ 0 ↦ ↑ⱽ¹[ v ] ] e') ])
    β-LetP : {e e' e'' : Exp {n}} → (v : Val e) → (v' : Val e')
                              → LetP (ProdV v e') e''
                                ↠
                                ↑ (ℤ.negsuc 1) , 0 [ ([ 0 ↦ ↑ⱽ¹[ v ] ]
                                                       ([ 0 ↦ shift-val {n} {ℤ.pos 1} {1} v' ] e'')) ]
    β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp {n}} {x : Fin n} → (ins : x ∈ s)
             → CaseE (VLab{x = x}) f ↠ f x ins
             
----------------------------------------------------------------------
----------------------------------------------------------------------

module progress where
  open syntx
  open substitution
  open typing
  open semantics

  -- To eliminate the possible typing judgement (LabAEx) for case expressions,
  -- we need ([] ≢ Γ' ++ ⟨ D , Γ ⟩. Agda does not know that no possible constructor
  -- for this equality exists, because _++_ is an arbitrary function and therefore
  -- "green slime" (see the link @ (LabAEx) rule).
  --
  -- Workaround: Argue with length of environments
  env-len-++ : {n : ℕ} {Γ Γ' : TEnv {n}} → length (Γ ++ Γ') ≡ length Γ +ᴺ length Γ'
  env-len-++ {n} {[]} {Γ'} = refl
  env-len-++ {n} {⟨ T , Γ ⟩} {Γ'} = cong ℕ.suc (env-len-++ {n} {Γ} {Γ'})
  
  env-len-> : {n : ℕ} {Γ : TEnv {n}} {T : Ty {n}} → length ⟨ T , Γ ⟩ >ᴺ 0
  env-len-> {n} {Γ} {T} = s≤s z≤n

  env-len->-++ : {n : ℕ} {Γ Γ' : TEnv {n}} → length Γ' >ᴺ 0 → length (Γ ++ Γ') >ᴺ 0
  env-len->-++ {n} {Γ} {⟨ T , Γ' ⟩} gt rewrite (env-len-++ {n} {Γ} {⟨ T , Γ' ⟩})= ≤-trans gt (m≤n+m (length ⟨ T , Γ' ⟩) (length Γ))

  env-len-eq : {n : ℕ} {Γ : TEnv {n}} {Γ' : TEnv {n}} → Γ ≡ Γ' → length Γ ≡ length Γ'
  env-len-eq {n} {Γ} {.Γ} refl = refl
  
  env-empty-++ : {n : ℕ} {Γ' Γ : TEnv {n}} {D : Ty {n}} → ¬ ([] ≡ Γ' ++ ⟨ D , Γ ⟩)
  env-empty-++ {n} {Γ} {Γ'} {D} eq = contradiction (env-len-eq eq) (<⇒≢ (env-len->-++ (env-len->{T = D})))

  -- Canonical forms
  canonical-forms-pi : {n : ℕ} {e : Exp {n}} {A B D : Ty {n}} → [] ⊢ e ⇒ D → [] ⊢ D ⇓ Pi A B → Val e → (∃[ e' ](e ≡ Abs e'))
  canonical-forms-pi {n} {.(LabI _)} {A} {B} {.(Single VLab (Label ⁅ _ ⁆))} (LabAI x) (AUSingle ()) v
  canonical-forms-pi {n} {.(Abs _)} {A} {B} {.(Pi _ _)} (PiAI{M = M} j) u v = M , refl

  canonical-forms-sigma : {n : ℕ} {e : Exp {n}} {A B D : Ty {n}} → [] ⊢ e ⇒ D → [] ⊢ D ⇓ Sigma A B → Val e → (∃{A = Exp {n}} λ e' → ∃{A = Val e'} λ v → ∃ λ e'' → e ≡ ProdV{e = e'} v e'')
  canonical-forms-sigma {n} {.(LabI _)} {A} {B} {.(Single VLab (Label ⁅ _ ⁆))} (LabAI x) (AUSingle ()) v
  canonical-forms-sigma {n} {.(ProdV _ _)} {A} {B} {.(Sigma _ _)} (PairAI{e = e}{N}{V} j j₁) u v = e , (V , (N , refl))

  -- Main theorem
  data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ⇒ T} : Set where
    step : {e' : Exp{n}} → e ↠ e' → Progress e
    value : Val e → Progress e

  progress : {n : ℕ} {e : Exp {n}} {T : Ty} → (j : [] ⊢ e ⇒ T) → Progress e {T} {j}
  progress {n} {Var x} {T} (VarA x₁ x₂) = value VVar
  progress {n} {UnitE} {.UnitT} (UnitAI x) = value VUnit
  progress {n} {Abs e} {.(Pi _ _)} (PiAI j) = value VFun
  progress {n} {App e x} {.([ 0 ↦ x ]ᵀ _)} (PiAE{A = A}{B = B}{D = D} j x₁ x₂ x₃)
    with progress {n} {e} {D} j
  ...  | step x₄ = step (ξ-App x₄)
  ...  | value x₄
       with canonical-forms-pi {n} {e} {A} {B} {D} j x₁ x₄
  ...     | fst , snd rewrite snd = step (β-App x)
  progress {n} {LabI x} {.(Single VLab (Label ⁅ x ⁆))} (LabAI x₁) = value VLab
  progress {n} {Prod e e₁} {.(Sigma A B)} (SigmaAI {A = A} {B = B} (SubTypeA{A = A₁} x x₂) x₁)
    with progress {n} {e} {A₁} x
  ...  | step x₃ = step (ξ-Prod x₃)
  ...  | value x₃ = step (β-Prod{v = x₃})
  progress {n} {ProdV x e} {.(Sigma _ _)} (PairAI{A = A} {B = B} j j₁)
    with progress {n} {e} {B} j₁
  ...  | step x₁ = step (ξ-ProdV x₁)
  ...  | value x₁ = value (VProd x x₁)
  progress {n} {LetP e e₁} {T} (SigmaAE{A = A}{B = B}{D = D} j x j₁ x₁)
    with progress {n} {e} {D} j
  ...  | step x₂ = step (ξ-LetP x₂)
  ...  | value x₂
       with canonical-forms-sigma {n} {e} {A} {B} {D} j x x₂
  ...     | fst , fst₁ , fst₂ , snd rewrite snd
          with x₂
  ...        | VProd v v₁ = step (β-LetP v v₁)
  progress {n} {LetE e e₁} {T} (Let{A = A} x j j₁)
    with progress {n} {e} {A} j
  ...  | step x₁ = step (ξ-LetE x₁)
  ...  | value x₁ = step (β-LetE x₁)
  progress {n} {CaseE {e = .(Var _)} VVar f} {T} (LabAEl {l = l} {ins = ins} (VarA x₁ ()) x j₁)
  progress {n} {CaseE {e = .(LabI _)} VLab f} {T} (LabAEl {l = _} {ins = ins} (LabAI x₁) x j₁) = step (β-LabE ins)
  progress {n} {CaseE .VVar f} {.(CaseT VVar _)} (LabAEx{eq = eq} x x₁) = contradiction eq env-empty-++
