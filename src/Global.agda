module Global where

open import Prelude

----------------------------------------------------
-- global types

Role = Nat
Roles = List Role

data GType : (ℝ : Roles) → Set where
  ⇒ : ∀ {R S} → (ρ : List Role) → GType R → GType S → GType (ρ ++ R ++ S)
  _⊛_ : ∀ {R S} → GType R → GType S → GType (R ++ S)
  _⊕_ : ∀ {R S} → GType R → GType S → GType (R ++ S)
  ⦅⦆＠ : (r : Role) → GType [ r ]
  

----------------------------------------------------
-- role renaming

{-
renameSingle : ∀ {r} → (s : Role) → GType [ r ] → GType [ s ]
renameSingle s T = {!!}
-}

rename : ∀ {R} → (f : Nat → Nat) → GType R → GType (map f R)
rename f (⇒ ρ T T₁) = {!!}
rename f (T ⊛ T₁) = {!!}
rename f (T ⊕ T₁) = coe (rename f T ⊕ rename f T₁) {!cong GType ?!}
rename f (⦅⦆＠ r) = ⦅⦆＠ (f r)

----------------------------------------------------
-- choreographies

SomeGType = Σ Roles GType

Context = List (SomeGType)

mutual

  infix 3 _⊩ᵥ_
  data _⊩ᵥ_ (Γ : Context) : {R : Roles} → GType R -> Set where

    tabs : {R R′ : Roles} {T : GType R} {T′ : GType R′}
         → (ρ : List Role) → (R , T) ∷ Γ ⊩ₘ T′
           -----------------------------------
         → Γ ⊩ᵥ ⇒ ρ T T′
         
    tvar : {R : Roles} {T : GType R}
         → (R , T) ∈ Γ
           ------------------------
         → Γ ⊩ᵥ T
 
    tunit : (r : Role)
           --------------
          → Γ ⊩ᵥ ⦅⦆＠ r
 
    tcom : (r s : Role) → {T : GType [ s ]}
           ------------------------
         → Γ ⊩ᵥ ⇒ [] T (rename (λ x → r) T) 

  infix 3 _⊩ₘ_
  data _⊩ₘ_ (Γ : Context) : {R : Roles} → GType R -> Set where
