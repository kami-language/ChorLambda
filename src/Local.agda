module Local where

open import Prelude
open import Base

----------------------------------------------------
-- local types


data LType : Set where
  _⟶_ : LType  → LType  → LType
  _⋆_ : LType  → LType  → LType
  _＋_ : LType  → LType  → LType
  ⦅⦆ : LType
  ⊥ : LType
  

----------------------------------------------------
-- behaviours

Context = List (LType)

mutual

  infix 3 _⊢ᵥ_
  data _⊢ᵥ_ (Γ : Context) : LType → Set where
    ntsend : ∀ {T : LType} (r : Role)
             --------------------------------------
           → Γ ⊢ᵥ T ⟶ ⊥

    ntrecv : ∀ {T : LType} (r : Role)
             --------------------------------------
           → Γ ⊢ᵥ ⊥ ⟶ T

    ntvar : ∀ {T : LType}
          → T ∈ Γ
            ------------
          → Γ ⊢ᵥ T
          
    ntunit : Γ ⊢ᵥ ⦅⦆
    
    ntbotm : Γ ⊢ᵥ ⊥
    
    ntabs : ∀ {T T′ : LType}
          → T ∷ Γ ⊢ₘ T′
            -----------------
          → Γ ⊢ᵥ T ⟶ T′

    ntpair : ∀ {T T′ : LType}
           → Γ ⊢ᵥ T → Γ ⊢ᵥ T′
          --------------------
           → Γ ⊢ᵥ (T ⋆ T′)
          
    ntproj1 : ∀ {T T′ : LType}
             -----------------------------------------------
           → Γ ⊢ᵥ (T ⋆ T′) ⟶ T

    ntproj2 : ∀ {T T′ : LType}
             -----------------------------------------------
            → Γ ⊢ᵥ (T ⋆ T′) ⟶ T′

    ntinl : ∀ {T T′ : LType}
          → Γ ⊢ᵥ T
            -----------
         → Γ ⊢ᵥ T ＋ T′

    ntinr : ∀ {T T′ : LType}
          → Γ ⊢ᵥ T′
            ------------
          → Γ ⊢ᵥ T ＋ T′


  infix 3 _⊢ₘ_
  data _⊢ₘ_ (Γ : Context) : LType → Set where

    ntval : ∀ {T : LType}
          → Γ ⊢ᵥ T
            -------
          → Γ ⊢ₘ T
          
    ntchor⊕ : ∀ {T : LType}
             → (r : Role) (l : Label) → Γ ⊢ₘ T
               --------------------------------------------
             → Γ ⊢ₘ T

    ntoff& : ∀ {T : LType}
           → (r : Role) → List (Label × (Γ ⊢ₘ T))
             ----------------------------------------
           → Γ ⊢ₘ T

    ntcase : ∀ {T₁ T₂ T : LType}
           → Γ ⊢ₘ T₁ ＋ T₂ →  T₁ ∷ Γ ⊢ₘ T → T₂ ∷ Γ ⊢ₘ T
             --------------------------------------------------------------------
           → Γ ⊢ₘ T
           
    ntapp : ∀ {T T′ : LType}
          → Γ ⊢ₘ (T ⟶ T′) → Γ ⊢ₘ T
            -------------------------------------
          → Γ ⊢ₘ T′
           
    ntapp2 : Γ ⊢ₘ ⊥ → Γ ⊢ₘ ⊥
            ----------------------
           → Γ ⊢ₘ ⊥

    nt⊔ : ∀ {Γ′ Γ″ : Context} {T T′ : LType}
        → Γ′ ⊢ₘ T → Γ″ ⊢ₘ T′
          -------------------------------------
        → Γ ⊢ₘ T

