
open import Data.List using (List; []; _++_; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; _>>=_; just; nothing) renaming (map to _⟫_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Function using (case_of_)

open import Base
open import Utils
open import ChoreoIntrinsic

----------------------------------------------------
-- roles extraction (oh if only we had strict Θ in the type...)

-- carful! duplicates!
iroles : ∀ {Θ} → IType Θ → List (Role Θ)
iroles (⟶ x₁ t t₁) = x₁ ++ (iroles t ++ iroles t₁)
iroles (t ＋ t₁) = iroles t ++ iroles t₁
iroles (t mul t₁) = iroles t ++ iroles t₁
iroles (o＠ r) = [ r ]

itroles : ∀ {Θ Γ} {T : IType Θ} → (Γ ⊢ₘ T) → List (Role Θ)
itroles {T = T} _ = iroles T

mutual

  -- carful! duplicates!
  ivroles : ∀ {Θ Γ} {T : IType Θ} → (Γ ⊢ᵥ T) → List (Role Θ)
  ivroles (tabs ρ T x) = iroles T ++ icroles x
  ivroles (tvar x) = []
  ivroles (tunit r) = [ r ]
  ivroles (tcom r s) = r ∷ [ s ]
  ivroles (tpair Ts Ts₁) = ivroles Ts ++ ivroles Ts₁
  ivroles tproj1 = []
  ivroles tproj2 = []
  ivroles (tinl Ts) = ivroles Ts
  ivroles (tinr Ts) = ivroles Ts

  icroles : ∀ {Θ Γ} {T : IType Θ} → (Γ ⊢ₘ T) → List (Role Θ)
  icroles (tapp Ts Ts₁) = icroles Ts ++ icroles Ts₁
  icroles (tsel Ts r s l) = r ∷ s ∷ (icroles Ts)
  icroles (tcase Ts Ts₁ Ts₂) = icroles Ts ++ icroles Ts₁ ++ icroles Ts₂
  icroles (tval v) = ivroles v


----------------------------------------------------
-- local types

data ILType (Θ : Roles) : Set where
  _⇒_ : ILType Θ → ILType Θ → ILType Θ
  _＋_ : ILType Θ → ILType Θ → ILType Θ
  _mul_ : ILType Θ → ILType Θ → ILType Θ
  o : ILType Θ
  ⊥ : ILType Θ

mutual

  data _⊩ᵥ_ {Θ} (Γ : List (ILType Θ)) : ILType Θ -> Set where
    ntsend : ∀ {T1 : ILType Θ} → (R : Role Θ)
             --------------------------------
           → (Γ ⊩ᵥ (T1 ⇒ ⊥))
 
    ntrecv : ∀ {T} → (R : Role Θ)
             --------------------
           → (Γ ⊩ᵥ (⊥ ⇒ T))

    ntvar : ∀ {T} → (T ∈ Γ)
             --------------
          → (Γ ⊩ᵥ T)
          
    ntunit : (Γ ⊩ᵥ o)
    
    ntbotm : (Γ ⊩ᵥ ⊥)

    ntpair : ∀ {T T′ : ILType Θ}
          --------------------------------
          → (Γ ⊩ᵥ (T ⇒ (T′ ⇒ (T mul T′))))
          
    ntproj1 : ∀ {T T′ : ILType Θ}
             -----------------------
           → (Γ ⊩ᵥ ((T mul T′) ⇒ T))

    ntproj2 : ∀ {T T′ : ILType Θ}
             -------------------------
           → (Γ ⊩ᵥ ( (T mul T′) ⇒ T′))



  data _⊩ₘ_ {Θ} (Γ : List (ILType Θ)) : ILType Θ -> Set where
    ntval : ∀ {T} → (Γ ⊩ᵥ T)
            ----------------
          → (Γ ⊩ₘ T)
          
    ntchor : ∀ {T} → (R : Role Θ) → (l : Label) → (Γ ⊩ₘ T)
             ---------------------------------------------
           → (Γ ⊩ₘ T)

    ntoff : ∀ {T} → Role Θ → List (Label × (Γ ⊩ₘ T))
            ----------------------------------------
          → (Γ ⊩ₘ T)

    ntcase : ∀ {T₁ T₂ T} → (Γ ⊩ₘ (T₁ ＋ T₂)) → ((T₁ ∷ Γ) ⊩ₘ T) → ((T₂ ∷ Γ) ⊩ₘ T)
             --------------------------------------------------------------------
           → (Γ ⊩ₘ T)
           
    ntapp : ∀ {T T′} → (Γ ⊩ₘ (T ⇒ T′)) → (Γ ⊩ₘ T)
            -------------------------------------
          → (Γ ⊩ₘ T′)
           
    ntapp2 : (Γ ⊩ₘ ⊥) → (Γ ⊩ₘ ⊥)
            ----------------------
           → (Γ ⊩ₘ ⊥)



----------------------------------------------------
{-
project-∙ : ∀ {Θ} {P : Set} → Behaviour Θ → Behaviour Θ → Dec P → Maybe (Behaviour Θ)
project-∙ M N (yes _) = just (M ∙ N)
project-∙ (V ⊥) (V ⊥) (no _) = just (V ⊥)
project-∙ M (V ⊥) (no _) = just M
project-∙ _ N (no _) = just N
-}

projectIntrinsicValue : ∀ {Θ Γ} {T : IType Θ} → Role Θ → (Γ ⊢ᵥ T) → Maybe (ILType Θ)
projectIntrinsicValue R Ts = {!!}


projectIntrinsicChoreo : ∀ {Θ Γ} {T : IType Θ} → Role Θ → (Γ ⊢ₘ T) → Maybe (Σ (List (ILType Θ)  × ILType Θ) (λ { (Γₗ , Tₗ) → Γₗ ⊩ₘ Tₗ }))
projectIntrinsicChoreo R (tval v) = {!!}
projectIntrinsicChoreo R (tapp Ts Ts₁) = do
  (Γₘ , M) ← projectIntrinsicChoreo R Ts
  (Γₙ , N) ← projectIntrinsicChoreo R Ts₁
  case (R ∈? (itroles Ts)) ⊎-dec ((R ∈? (icroles Ts)) ×-dec (R ∈? (icroles Ts₁))) of
    λ {(yes a) → just ( {!!} , ntapp {!!} N) ;
       (no a) → case ((M , N)) of (
         λ { (ntval ntbotm , ntval ntbotm) → just ({!!} , (ntval ntbotm));
             (M , ntval ntbotm) → just (Γₘ , M);
             (M , N) → just (Γₙ , N)})}

{-
c (R ∈? croles (M ∙ N)))
  -}
projectIntrinsicChoreo R (tsel Ts r s l) = {!!}
projectIntrinsicChoreo R (tcase Ts Ts₁ Ts₂) = {!!}
