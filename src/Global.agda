{-# OPTIONS --rewriting #-}

module Global where

open import Prelude
open import Base
open import Types
open import Renaming

----------------------------------------------------
-- choreographies

SomeGType = Σ Roles GType

Context = List (SomeGType)

mutual

  infix 3 _⊩ᵥ_
  data _⊩ᵥ_ (Γ : Context) : {R : Roles} → GType R → Set₁ where

    tabs : {R R′ : Roles} {T : GType R} {T′ : GType R′}
         → (ρ : List Role) → (R , T) ∷ Γ ⊩ₘ T′
           -----------------------------------
         → Γ ⊩ᵥ T ⇒⟨ ρ ⟩ T′
         
    tvar : {R : Roles} {T : GType R}
         → (R , T) ∈ Γ
           ------------
         → Γ ⊩ᵥ T
 
    tunit : (r : Role)
           --------------
          → Γ ⊩ᵥ ◎＠ r
 
    tcom : (s r : Role) → {S : Roles} → {sim : S ≈ [ s ]} → {T : GType S}
           --------------------------------------------------------
         → Γ ⊩ᵥ T ⇒⟨ [] ⟩ (renameAll r T)
         
    tpair : {R R′ : Roles} {T : GType R} {T′ : GType R′}
         → Γ ⊩ᵥ T → Γ ⊩ᵥ T′
           ----------------
         → Γ ⊩ᵥ T ⊛ T′
         
    tproj1 : {R R′ : Roles} {T : GType R} {T′ : GType R′}
           ---------------------------------------------
           → Γ ⊩ᵥ (T ⊛ T′) ⇒⟨ [] ⟩ T

    tproj2 : {R R′ : Roles} {T : GType R} {T′ : GType R′}
           ----------------------------------------------
           → Γ ⊩ᵥ (T ⊛ T′) ⇒⟨ [] ⟩  T′
           
    tinl : {R R′ : Roles} {T : GType R} {T′ : GType R′}
         → Γ ⊩ᵥ T
           ------------
         → Γ ⊩ᵥ T ⊕ T′
         
    tinr : {R R′ : Roles} {T : GType R} {T′ : GType R′}
         → Γ ⊩ᵥ T′
           ------------
         → Γ ⊩ᵥ T ⊕ T′

  infix 3 _⊩ₘ_
  data _⊩ₘ_ (Γ : Context) : {R : Roles} → GType R → Set₁ where
  
    tval : {R : Roles} {T : GType R}
         → Γ ⊩ᵥ T
           -------
         → Γ ⊩ₘ T
         
    tapp : {R R′ : Roles} {T : GType R} {T′ : GType R′} {ρ : List Role}
           → Γ ⊩ₘ T ⇒⟨ ρ ⟩ T′ → Γ ⊩ₘ T
           ---------------------------
           → Γ ⊩ₘ T′
           
    tsel : {R : Roles} {T : GType R}
           → Γ ⊩ₘ T → (r s : Role) → (l : Label)
           -------------------------------------
           → Γ ⊩ₘ T

    tcase : {R₁ R₂ R : Roles} {T₁ : GType R₁} {T₂ : GType R₂} {T : GType R}
          → Γ ⊩ₘ (T₁ ⊕ T₂)
          → (Ts₁ : (_ , T₁) ∷ Γ ⊩ₘ T)
          → (Ts₂ : (_ , T₂) ∷ Γ ⊩ₘ T)
          ---------------------------
          → Γ ⊩ₘ T
