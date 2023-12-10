
open import Data.List using (List; []; _++_; _∷_; [_]; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; _>>=_; just; nothing) renaming (map to _⟫_)
open import Data.Product using (Σ; _×_; _,_; _,′_; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Function using (case_of_)
open import Data.Fin.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; refl)

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

    nt⊔ : ∀ {T T′} → (Γ ⊩ₘ T) → (Γ ⊩ₘ T′)
            -------------------------------------
          → (Γ ⊩ₘ T)



----------------------------------------------------
{-
project-∙ : ∀ {Θ} {P : Set} → Behaviour Θ → Behaviour Θ → Dec P → Maybe (Behaviour Θ)
project-∙ M N (yes _) = just (M ∙ N)
project-∙ (V ⊥) (V ⊥) (no _) = just (V ⊥)
project-∙ M (V ⊥) (no _) = just M
project-∙ _ N (no _) = just N
-}

  

projectIType : ∀ {Θ} → Role Θ → IType Θ → ILType Θ
projectIType R T with R ∈? iroles T
... | no _ = ⊥
projectIType R (⟶ ρ T T₁) | yes _ = projectIType R T ⇒ projectIType R T₁
projectIType R (T ＋ T₁) | yes _ = projectIType R T ＋ projectIType R T₁
projectIType R (T mul T₁) | yes _ = projectIType R T mul projectIType R T₁
projectIType R (o＠ r) | yes _ = o

projectIntrinsicValue : ∀ {Θ Γ} {T : IType Θ} → (R : Role Θ) → (Γ ⊢ₘ T) → ((map (projectIType R) Γ) ⊩ᵥ (projectIType R T))
projectIntrinsicValue R Ts = {!!}


projectIntrinsicChoreo : ∀ {Θ Γ} {T : IType Θ} → (R : Role Θ) → (Γ ⊢ₘ T) → ((map (projectIType R) Γ) ⊩ₘ (projectIType R T))
projectIntrinsicChoreo R (tval v) = ?
projectIntrinsicChoreo R (tapp {T} {T′} {ρ} Ts Ts₁) with R ∈? iroles (⟶ ρ T T′) | projectIntrinsicChoreo R Ts | projectIntrinsicChoreo R Ts₁
... | yes a | M | N = ntapp {!M!} N
... | no a | M | N = {!!}
projectIntrinsicChoreo R (tsel Ts r s l) = {!!}
projectIntrinsicChoreo R (tcase Ts Ts₁ Ts₂) = {!!}

{-

projectIntrinsicValue : ∀ {Θ Γ} {T : IType Θ} → (R : Role Θ) → (Γ ⊢ᵥ T) → Σ (List (ILType Θ)) (λ Γ′ → Γ′ ⊩ᵥ (projectIType R T)) -- ((map (projectIType R) Γ) ⊩ₘ (projectIType R T))
projectIntrinsicValue R Ts = {!!}


projectIntrinsicChoreo : ∀ {Θ Γ} {T : IType Θ} → (R : Role Θ) → (Γ ⊢ₘ T) → Σ (List (ILType Θ)) (λ Γ′ → Γ′ ⊩ₘ (projectIType R T))
projectIntrinsicChoreo R (tval v) = let (A , B) = projectIntrinsicValue R v
                                    in (A , ntval B)
projectIntrinsicChoreo R (tapp {T} {T′} {ρ} Ts Ts₁) with R ∈? iroles (⟶ ρ T T′) | R ∈? iroles T′
... | yes a | yes b = let (A , B) = (projectIntrinsicChoreo R Ts)
                          (_ , C) = (projectIntrinsicChoreo R Ts₁)
                      in (A , ntapp {!C!} {!Cäh hupsi eingepennt ^^
                      !} )
... | yes a | no b = {!!} --ntapp (projectIntrinsicChoreo R Ts) (projectIntrinsicChoreo R Ts₁)
... | no a | _ =  {!!}
{-
... | yes a = ntapp (projectIntrinsicChoreo R {!T!}) (projectIntrinsicChoreo R Ts₁)
... | no _ with projectIntrinsicChoreo R Ts | (projectIntrinsicChoreo R Ts₁)
... | M | N = {!M!} -}
projectIntrinsicChoreo R (tsel Ts r s l) = {!!}
projectIntrinsicChoreo R (tcase Ts Ts₁ Ts₂) = {!!}
-}
