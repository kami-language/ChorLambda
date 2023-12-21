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
  project⇒ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} {ρ : Roles} → (r ∈ (ρ ++ R ++ R′)) → πT r (T ⇒⟨ ρ ⟩ T′) ≡ (πT r T) ⟶ (πT r T′)
  
project⊕ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} → (r ∈ (R ++ R′)) → πT r (T ⊕ T′) ≡ (πT r T) ＋ (πT r T′)
project⊕ {R} {R′} {T} {T′} {r} r∈RR′ = cong (λ p → π-GType r p (T ⊕ T′)) (snd (∈→∈? r∈RR′))
                                           

  
transp-⊢ᵥ : ∀ {T T′ : LType} {Γ} -> T ≡ T′ -> Γ ⊢ᵥ T -> Γ ⊢ᵥ T′
transp-⊢ᵥ refl Ts = Ts

transp-⊢ₘ : ∀ {T T′ : LType} {Γ} -> T ≡ T′ -> Γ ⊢ₘ T -> Γ ⊢ₘ T′
transp-⊢ₘ refl Ts = Ts

mutual
  πC : ∀ {Γ R} {T : GType R} → (r : Role) → Γ ⊩ₘ T → map (λ (_ , t) → πT r t) Γ ⊢ₘ (πT r T)
  πC {R = R} r t = π-Choreo r (r ∈? R) t


  π-Choreo : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ₘ T → map (λ (_ , t) → πT r t) Γ ⊢ₘ (πT r T)
  
  π-Choreo r r∈R (tval x) = ntval (π-Value r r∈R x)
  
  π-Choreo r (yes p) (tapp {R} {R′} {ρ = ρ} x x₁) = ntapp {!transp-⊢ₘ (project⇒ (right-∈ {as = ρ ++ R} p)) (πC r x)!} (πC r x₁)
  π-Choreo r (no ¬p) (tapp {R} {R′} x x₁) = {!!}
  
  π-Choreo r r∈R (tsel x r₁ s l) with s ≟ r | r₁ ≟ r | s ≟ r₁
  ... | yes s=R | no r≠R | no s≠r = ntchor⊕ r l (πC r x)
  ... | no s≠R | yes r=R | no s≠r = ntoff& s [ (l , (πC r x)) ]
  ... | _ | _ | _ = πC r x

  π-Choreo r r∈R (tcase {R₁ = R₁} {R₂} x x₁ x₂) with r ∈? (R₁ ++ R₂)
  ... | yes a = ntcase (transp-⊢ₘ (project⊕ a) (πC r x)) (πC r x₁) (πC r x₂)
  ... | no a = ntapp (ntval (ntabs (nt⊔ (πC r x₁) (πC r x₂)))) (πC r x)

  π-Value : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ᵥ T → map (λ (_ , t) → πT r t) Γ ⊢ᵥ (πT r T)
  π-Value r r∈R x = {!!}
