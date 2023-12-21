module EndpointProjection where

open import Prelude
open import Base
open import Global
open import Local

mutual
  π-GType : ∀ {R : Roles} → (r : Role) → Dec (r ∈ R) → (T : GType R) → LType
  π-GType r (yes p) (T ⇒⟨ ρ ⟩ T₁) = (πT r T) ⟶ (πT r T₁)
  π-GType r (yes p) (T ⊛ T₁) = (πT r T) ⋆ (πT r T₁)
  π-GType r (yes p) (T ⊕ T₁) = (πT r T) ＋ (πT r T₁)
  π-GType r (yes p) (⦅⦆＠ r₁) = ⦅⦆
  π-GType r (no ¬p) T = ⊥
  
  πT : ∀ {R : Roles} → (r : Role) → (T : GType R) → LType
  πT {R} r t = π-GType r (r ∈? R) t

postulate
  project⇒ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} {ρ : Roles} → (r ∈ ((R ++ ρ) ++ R′)) → πT r (T ⇒⟨ ρ ⟩ T′) ≡ (πT r T) ⟶ (πT r T′)
  
project⊕ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} → (r ∈ (R ++ R′)) → πT r (T ⊕ T′) ≡ (πT r T) ＋ (πT r T′)
project⊕ {R} {R′} {T} {T′} {r} r∈RR′ = cong (λ p → π-GType r p (T ⊕ T′)) (snd (∈→∈? r∈RR′))


project⊥ : ∀ {R : Roles} {T : GType R} {r : Role} → (r ∉ R) → πT r T ≡ ⊥
project⊥ {R} {T} {r} r∉RR′ =
  let
    r-no : (r ∈? R) ≡ no _
    r-no = snd (∉→∈? r∉RR′)
  in cong (λ rr → π-GType r rr T) r-no
  
transp-⊢ᵥ : ∀ {T T′ : LType} {Γ} -> T′ ≡ T -> Γ ⊢ᵥ T -> Γ ⊢ᵥ T′
transp-⊢ᵥ refl Ts = Ts

transp-⊢ₘ : ∀ {T T′ : LType} {Γ} -> T ≡ T′ -> Γ ⊢ₘ T -> Γ ⊢ₘ T′
transp-⊢ₘ refl Ts = Ts

mutual
  πC : ∀ {Γ R} {T : GType R} → (r : Role) → Γ ⊩ₘ T → map (λ (_ , t) → πT r t) Γ ⊢ₘ (πT r T)
  πC {R = R} r t = π-Choreo r (r ∈? R) t


  π-Choreo : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ₘ T → map (λ (_ , t) → πT r t) Γ ⊢ₘ (πT r T)
  
  π-Choreo r r∈R (tval x) = ntval (π-Value r r∈R x)
  
  π-Choreo r _ (tapp {R} {R′} {ρ = ρ} x x₁) with r ∈? ((R ++ ρ) ++ R′)
  ... | yes r∈rrr = ntapp (transp-⊢ₘ (project⇒ r∈rrr) (πC r x)) (πC r x₁)
  ... | (no r∉rrr) =
    let
      r∉R : r ∉ R
      r∉R = left-∉ R ρ (left-∉ (R ++ ρ) R′ r∉rrr)
    
      x⊥ = transp-⊢ₘ (project⊥ r∉rrr) (π-Choreo r (no r∉rrr) x)
      x₁⊥ = transp-⊢ₘ (project⊥ r∉R) (π-Choreo r (no r∉R) x₁)

      T≡⊥ = sym (project⊥ (right-∉ (R ++ ρ) R′ r∉rrr))
    in transp-⊢ₘ T≡⊥ (ntapp2 x⊥ x₁⊥)
  
  π-Choreo r r∈R (tsel x r₁ s l) with s ≟ r | r₁ ≟ r | s ≟ r₁
  ... | yes s=R | no r≠R | no s≠r = ntchor⊕ r l (πC r x)
  ... | no s≠R | yes r=R | no s≠r = ntoff& s [ (l , (πC r x)) ]
  ... | _ | _ | _ = πC r x

  π-Choreo r r∈R (tcase {R₁ = R₁} {R₂} x x₁ x₂) with r ∈? (R₁ ++ R₂)
  ... | yes a = ntcase (transp-⊢ₘ (project⊕ a) (πC r x)) (πC r x₁) (πC r x₂)
  ... | no a = ntapp (ntval (ntabs (nt⊔ (πC r x₁) (πC r x₂)))) (πC r x)


  πV : ∀ {Γ R} {T : GType R} (r : Role) → Γ ⊩ᵥ T → map (λ (_ , t) → πT r t) Γ ⊢ᵥ (πT r T)
  πV {R = R} r t = π-Value r (r ∈? R) t


  π-Value : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ᵥ T → map (λ (_ , t) → πT r t) Γ ⊢ᵥ (πT r T)
  π-Value r r∈R (tabs ρ x) = {!!}
  π-Value r r∈R (tvar x) = {!!}
  π-Value r r∈R (tunit r₁) = {!!}
  π-Value r r∈R (tcom r₁ s) = {!!}
  π-Value r r∈R (tpair x x₁) = {!!}
  π-Value r r∈R tproj1 = {!!}
  π-Value r (yes p) tproj2 = {!!}
  π-Value r (no ¬p) tproj2 = {!!}
  
  π-Value r (yes p) (tinl x) = transp-⊢ᵥ (project⊕ p) (ntinl (πV r x))
  π-Value r (no ¬p) (tinl x) = {!!}
  
  π-Value r (yes p) (tinr x) = {!!}
  π-Value r (no ¬p) (tinr x) = {!transp-⊢ᵥ (project⊥ ¬p) ntbotm!}
