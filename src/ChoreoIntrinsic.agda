
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup) renaming ([_] to ⟨_⟩)

open import Base
open import ChoreoTyping


-- a type is parametrized by the maximal number of different roles it uses
data IType (R : Roles) : Set where
  ⟶ :  (ρ : List (Role R)) → IType R → IType R → IType R -- abstraction type: R may also participate in addition to roles T and roles T'
  _＋_ : IType R → IType R → IType R -- sum type
  _mul_ : IType R → IType R → IType R -- product type
  o＠ : (r : (Fin R)) → IType R -- unit type at role r


-- map over the roles of a type
mapRoles : {R Θ : Roles} → IType R → (Fin R → Fin Θ) → IType Θ
mapRoles (⟶ x T T₁) f = ⟶ (map f x) (mapRoles T f) (mapRoles T₁ f)
mapRoles (T ＋ T₁) f = (mapRoles T f) ＋ mapRoles T₁ f
mapRoles (T mul T₁) f = (mapRoles T f) mul (mapRoles T₁ f)
mapRoles (o＠ r) f = o＠ (f r)


-- role renaming
_⟦_⟧i : {R Θ : Roles} → IType R → (Injection R Θ) → IType Θ
_⟦_⟧i T rename = mapRoles T (Injection.inj rename)

-- embed a single role type by giving its role the given name
iembed : ∀{Θ} → IType 1 → Role Θ → IType Θ
iembed = λ T n → T ⟦ (fromVec ⟨ n ⟩ (rest empty empty)) ⟧i

mutual

  data _⊢ᵥ_ {Θ} (Γ : List (IType Θ)) : IType Θ -> Set where

    tabs : {Tʻ : IType Θ}
         → (ρ : List (Role Θ)) → (T : IType Θ) → ((T ∷ Γ) ⊢ₘ Tʻ)
           -------------------------------
         → (Γ ⊢ᵥ ⟶ ρ T Tʻ)

    tvar : {T : IType Θ}
         → (T ∈ Γ)
           --------------------
         → (Γ ⊢ᵥ T)

    tunit : (r : Role Θ)
          -------------------------
          → (Γ ⊢ᵥ o＠ r)

    tcom : {T : IType 1} (r s : Role Θ)
        -----------------------------------------------------
        → (Γ ⊢ᵥ ⟶ [] (iembed T r) (iembed T s))

    tpair : ∀ {T T′ : IType Θ}
          → (Γ ⊢ᵥ T) → (Γ ⊢ᵥ T′)
          -------------------------------------
          → (Γ ⊢ᵥ (T mul T′))

    tproj1 : ∀ {T T′ : IType Θ}
             ----------------------------------------
           → (Γ ⊢ᵥ (⟶ [] (T mul T′) T))

    tproj2 : ∀ {T T′ : IType Θ}
             ------------------------------------------
           → (Γ ⊢ᵥ (⟶ [] (T mul T′) T′))

    tinl : ∀ {T T′ : IType Θ}
        → (Γ ⊢ᵥ T)
        -------------------------------
        → (Γ ⊢ᵥ (T ＋ T′))

    tinr : ∀ {T T′ : IType Θ}
        → (Γ ⊢ᵥ T′)
        -------------------------------
        → (Γ ⊢ᵥ (T ＋ T′))

  data _⊢ₘ_ {Θ} (Γ : List (IType Θ)) : IType Θ -> Set where

    tval : ∀ {T}
        → (Γ ⊢ᵥ T)
          ------------
        → (Γ ⊢ₘ T)

    tapp : ∀ {T T'} {ρ : List (Role Θ)}
        → (Γ ⊢ₘ (⟶ ρ T T')) → (Γ ⊢ₘ T)
          -------------------
        → (Γ ⊢ₘ T')

    tsel : {T : IType Θ}
        → (Γ ⊢ₘ T ) → (r s : Role Θ) → (l : Label)
        --------------------------
        → (Γ ⊢ₘ T)

    tcase : ∀  {T₁ T₂ T : IType Θ}
          → (Γ ⊢ₘ (T₁ ＋ T₂)) → ((T₁ ∷ Γ) ⊢ₘ T) → ((T₂ ∷ Γ) ⊢ₘ T)
          --------------------------------------
          → (Γ ⊢ₘ T)

