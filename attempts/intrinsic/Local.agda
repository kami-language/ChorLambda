module Local where

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_)

open import Base
open import Utils

----------------------------------------------------
-- local types

data ILType (Θ : Roles) : Set where
  _⇒_ : ILType Θ → ILType Θ → ILType Θ
  _＋_ : ILType Θ → ILType Θ → ILType Θ
  _⋆_ : ILType Θ → ILType Θ → ILType Θ
  o : ILType Θ
  ⊥ : ILType Θ

mutual

  infix 3 _⊢ᵥ_
  data _⊢ᵥ_ {Θ} (Γ : List (ILType Θ)) : ILType Θ -> Set where
    ntsend : ∀ {T1 : ILType Θ} (R : Role Θ)
             ------------------------------
           → Γ ⊢ᵥ T1 ⇒ ⊥
 
    ntrecv : ∀ {T} (R : Role Θ)
             ------------------
           → Γ ⊢ᵥ ⊥ ⇒ T

    ntvar : ∀ {T} → T ∈ Γ
             --------------
          → Γ ⊢ᵥ T
          
    ntunit : Γ ⊢ᵥ o
    
    ntbotm : Γ ⊢ᵥ ⊥
    
    ntabs : ∀ {T T′} → (T ∷ Γ) ⊢ₘ T′
             -----------------------
           → Γ ⊢ᵥ T ⇒ T′

    ntpair : ∀ {T T′ : ILType Θ} → Γ ⊢ᵥ T → Γ ⊢ᵥ T′
          -----------------------------------------
          → Γ ⊢ᵥ (T ⋆ T′)
          
    ntproj1 : ∀ {T T′ : ILType Θ}
             ------------------------------------
           → Γ ⊢ᵥ (T ⋆ T′) ⇒ T

    ntproj2 : ∀ {T T′ : ILType Θ}
             ------------------------------------
            → Γ ⊢ᵥ (T ⋆ T′) ⇒ T′

    ntinl : ∀ {T T′ : ILType Θ}
          → Γ ⊢ᵥ T
            -------------------------------
         → Γ ⊢ᵥ T ＋ T′

    ntinr : ∀ {T T′ : ILType Θ}
          → Γ ⊢ᵥ T′
            -------------------------------
          → Γ ⊢ᵥ T ＋ T′



  infix 3 _⊢ₘ_
  data _⊢ₘ_ {Θ} (Γ : List (ILType Θ)) : ILType Θ -> Set where
    ntval : ∀ {T} → Γ ⊢ᵥ T
            ----------------
          → Γ ⊢ₘ T
          
    ntchor⊕ : ∀ {T} (R : Role Θ) (l : Label) → Γ ⊢ₘ T
             --------------------------------------------
           → Γ ⊢ₘ T

    ntoff& : ∀ {T} → Role Θ → List (Label × (Γ ⊢ₘ T))
            ----------------------------------------
          → Γ ⊢ₘ T

    ntcase : ∀ {T₁ T₂ T} → Γ ⊢ₘ (T₁ ＋ T₂) → (T₁ ∷ Γ) ⊢ₘ T → (T₂ ∷ Γ) ⊢ₘ T
             --------------------------------------------------------------------
           → Γ ⊢ₘ T
           
    ntapp : ∀ {T T′} → Γ ⊢ₘ (T ⇒ T′) → Γ ⊢ₘ T
            -------------------------------------
          → Γ ⊢ₘ T′
           
    ntapp2 : Γ ⊢ₘ ⊥ → Γ ⊢ₘ ⊥
            ----------------------
           → Γ ⊢ₘ ⊥

    nt⊔ : ∀ {Γ′ Γ″ : List (ILType Θ)} {T T′} → Γ′ ⊢ₘ T → Γ″ ⊢ₘ T′
            -------------------------------------
          → Γ ⊢ₘ T


-------------------------------------------------------------------
-- variable renaming

mutual
  renameₘ : ∀ {Θ} {Γ Γ′ : List (ILType Θ)} {A : ILType Θ} → Γ ⊆ Γ′ → Γ ⊢ₘ A → Γ′ ⊢ₘ A
  renameₘ Γ⊆Γ′ (ntval x) = nt⊔ (ntval x) (ntval x)
  renameₘ Γ⊆Γ′ (ntchor⊕ R l M) = renameₘ Γ⊆Γ′ M
  renameₘ Γ⊆Γ′ (ntoff& x x₁) = ntoff& x []
  renameₘ Γ⊆Γ′ (ntcase M M₁ M₂) = nt⊔ M₂ M₂
  renameₘ Γ⊆Γ′ (ntapp M M₁) = ntapp (renameₘ Γ⊆Γ′ M) (renameₘ Γ⊆Γ′ M₁)
  renameₘ Γ⊆Γ′ (ntapp2 M M₁) = renameₘ Γ⊆Γ′ M₁
  renameₘ Γ⊆Γ′ (nt⊔ M M₁) = nt⊔ M M₁
  
  renameᵥ : ∀ {Θ} {Γ Γ′ : List (ILType Θ)} {A : ILType Θ} → Γ ⊆ Γ′ → Γ ⊢ᵥ A → Γ′ ⊢ᵥ A
  renameᵥ Γ⊆Γ′ (ntsend R) = ntsend R
  renameᵥ Γ⊆Γ′ (ntrecv R) = ntrecv R
  renameᵥ Γ⊆Γ′ (ntvar x) = ntvar (Γ⊆Γ′ x)
  renameᵥ Γ⊆Γ′ ntunit = ntunit
  renameᵥ Γ⊆Γ′ ntbotm = ntbotm
  renameᵥ Γ⊆Γ′ (ntabs x) = ntabs (renameₘ (keep Γ⊆Γ′) x)
  renameᵥ Γ⊆Γ′ (ntpair Ts Ts₁) = ntpair (renameᵥ Γ⊆Γ′ Ts) (renameᵥ Γ⊆Γ′ Ts₁)
  renameᵥ Γ⊆Γ′ ntproj1 = ntproj1
  renameᵥ Γ⊆Γ′ ntproj2 = ntproj2
  renameᵥ Γ⊆Γ′ (ntinl Ts) = ntinl (renameᵥ Γ⊆Γ′ Ts)
  renameᵥ Γ⊆Γ′ (ntinr Ts) = ntinr (renameᵥ Γ⊆Γ′ Ts)
