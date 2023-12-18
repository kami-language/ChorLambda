module Local where

open import Prelude
open import Base

----------------------------------------------------
-- local types


data LType : (ℝ : Roles) → Set where
  _⟶_ : ∀ {R S} → LType R → LType S → LType (R ++ S)
  _⋆_ : ∀ {R S} → LType R → LType S → LType (R ++ S)
  _＋_ : ∀ {R S} → LType R → LType S → LType (R ++ S)
  ⦅⦆ : LType []
  ⊥ : LType []
  

----------------------------------------------------
-- behaviours

SomeLType = Σ Roles LType

Context = List (SomeLType)

mutual

  infix 3 _⊢ᵥ_
  data _⊢ᵥ_ (Γ : Context) : {R : Roles} → LType R → Set where
    ntsend : ∀ {R : Roles} {T : LType R} (r : Role)
             --------------------------------------
           → Γ ⊢ᵥ T ⟶ ⊥

    ntrecv : ∀ {R : Roles} {T : LType R} (r : Role)
             --------------------------------------
           → Γ ⊢ᵥ ⊥ ⟶ T

    ntvar : ∀ {R : Roles} {T : LType R}
          → (_ , T) ∈ Γ
            ------------
          → Γ ⊢ᵥ T
          
    ntunit : Γ ⊢ᵥ ⦅⦆
    
    ntbotm : Γ ⊢ᵥ ⊥
    
    ntabs : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
          → (_ , T) ∷ Γ ⊢ₘ T′
            -----------------
          → Γ ⊢ᵥ T ⟶ T′

    ntpair : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
           → Γ ⊢ᵥ T → Γ ⊢ᵥ T′
          --------------------
           → Γ ⊢ᵥ (T ⋆ T′)
          
    ntproj1 : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
             -----------------------------------------------
           → Γ ⊢ᵥ (T ⋆ T′) ⟶ T

    ntproj2 : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
             -----------------------------------------------
            → Γ ⊢ᵥ (T ⋆ T′) ⟶ T′

    ntinl : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
          → Γ ⊢ᵥ T
            -----------
         → Γ ⊢ᵥ T ＋ T′

    ntinr : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
          → Γ ⊢ᵥ T′
            ------------
          → Γ ⊢ᵥ T ＋ T′



  infix 3 _⊢ₘ_
  data _⊢ₘ_ (Γ : Context) : {R : Roles} → LType R → Set where

    ntval : ∀  {R : Roles} {T : LType R}
          → Γ ⊢ᵥ T
            -------
          → Γ ⊢ₘ T
          
    ntchor⊕ : ∀ {R : Roles} {T : LType R}
             → (r : Role) (l : Label) → Γ ⊢ₘ T
               --------------------------------------------
             → Γ ⊢ₘ T

    ntoff& : ∀ {R : Roles} {T : LType R}
           → (r : Role) → List (Label × (Γ ⊢ₘ T))
             ----------------------------------------
           → Γ ⊢ₘ T

    ntcase : ∀ {R₁ R₂ R : Roles} {T₁ : LType R₁} {T₂ : LType R₂} {T : LType R}
           → Γ ⊢ₘ T₁ ＋ T₂ → (_ , T₁) ∷ Γ ⊢ₘ T → (_ , T₂) ∷ Γ ⊢ₘ T
             --------------------------------------------------------------------
           → Γ ⊢ₘ T
           
    ntapp : ∀ {R R′ : Roles} {T : LType R} {T′ : LType R′}
          → Γ ⊢ₘ (T ⟶ T′) → Γ ⊢ₘ T
            -------------------------------------
          → Γ ⊢ₘ T′
           
    ntapp2 : Γ ⊢ₘ ⊥ → Γ ⊢ₘ ⊥
            ----------------------
           → Γ ⊢ₘ ⊥

    nt⊔ : ∀ {Γ′ Γ″ : Context} {R R′ : Roles} {T : LType R} {T′ : LType R′}
        → Γ′ ⊢ₘ T → Γ″ ⊢ₘ T′
          -------------------------------------
        → Γ ⊢ₘ T

