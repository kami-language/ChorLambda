{-# OPTIONS --rewriting #-}

module EndpointProjection where

open import Prelude
open import Base
open import Types
open import Renaming
open import Global
open import Local

------------------------------------------------------------------------
-- Projecting Types

mutual
  π-GType : ∀ {R : Roles} → (r : Role) → Dec (r ∈ R) → (T : GType R) → LType
  π-GType r (yes p) (T ⇒⟨ ρ ⟩ T₁) = (πT r T) ⟶ (πT r T₁)
  π-GType r (yes p) (T ⊛ T₁) = (πT r T) ⋆ (πT r T₁)
  π-GType r (yes p) (T ⊕ T₁) = (πT r T) ＋ (πT r T₁)
  π-GType r (yes p) (◎＠ r₁) = ○
  π-GType r (no ¬p) T = ∅
  
  πT : ∀ {R : Roles} → (r : Role) → (T : GType R) → LType
  πT {R} r t = π-GType r (r ∈? R) t

π⋆ : Role → Global.Context → Local.Context
π⋆ r = map (λ { (_ , t) → πT r t })

π∈ : ∀ {R T Γ r} → (R , T) ∈ Γ → _∈_ (πT r T) (π⋆ r Γ)
π∈ here = here
π∈ (there x) = there (π∈ x)

------------------------------------------------------------------------
-- properties of projection to participant roles

project⇒ : ∀ {r ρ R R′} {T : GType R} {T′ : GType R′} → (r ∈ (R ++ ρ) ++ R′) → πT r (T ⇒⟨ ρ ⟩ T′) ≡ πT r T ⟶ πT r T′
project⇒ {r} {ρ} {T = T} {T′} r∈RρR′ = cong (λ p → π-GType r p (T ⇒⟨ ρ ⟩ T′)) (snd (∈→∈? r∈RρR′))
  
project⊕ : ∀ {r R R′} {T : GType R} {T′ : GType R′} → (r ∈ R ++ R′) → πT r (T ⊕ T′) ≡ πT r T ＋ πT r T′
project⊕ {r} {T = T} {T′} r∈RR′ = cong (λ p → π-GType r p (T ⊕ T′)) (snd (∈→∈? r∈RR′))

project⊛ : ∀ {r R R′} {T : GType R} {T′ : GType R′} → (r ∈ R ++ R′) → πT r (T ⊛ T′) ≡ πT r T ⋆ πT r T′
project⊛ {r} {T = T} {T′} r∈RR′ = cong (λ p → π-GType r p (T ⊛ T′)) (snd (∈→∈? r∈RR′))

project○ : ∀ {r s} → r ∈ [ s ] → πT r (◎＠ s) ≡ ○
project○ {r} {s} r=s = cong (λ p → π-GType r p (◎＠ s)) (snd (∈→∈? r=s))

project∅ : ∀ {R} {T : GType R} {r : Role} → (r ∉ R) → πT r T ≡ ∅
project∅ {T = T} {r} r∉RR′ = cong (λ rr → π-GType r rr T) (snd (∉→∈? r∉RR′))

------------------------------------------------------------------------
-- projection of tcom gets a lot of special attention


lem7 : ∀ {r s S} {T : GType S} (p : S ≈ [ s ]) → π-GType r (r ∈? S) T ≅ π-GType r (r ∈? map (λ _ → s) S) (renameAll s T)
lem7 {r} p = icong₂ (λ R → Dec (r ∈ R)) (≈cmap p) (π-GType r) (lem6 p) (renameAllSingle p)


rename∅ : ∀ {s s′ S′} {T : GType S′} → {S′ ≈ [ s′ ]} → s ≢ s′ → πT s′ (renameAll s T) ≡ ∅
rename∅ {s} {s′} {T = T} {S′≈[s′]} s≢s′ = cong (λ S → π-GType s′ S (renameAll s T)) (snd (∉→∈? (≈∉ (λ {here → refl ↯ s≢s′}) (≈map (λ _ → s) S′≈[s′]))))


projectSend : ∀ {s s′ S′} {T : GType S′} {sim : S′ ≈ [ s′ ]} → s ≢ s′ → πT s′ (T ⇒⟨ [] ⟩ renameAll s T) ≡ (πT s′ T ⟶ ∅)
projectSend {s} {s′} {T = T} {S′≈[s′]} s≢s′ = πT s′ (T ⇒⟨ [] ⟩ renameAll s T)
                            ≡⟨ project⇒ (left-∈ (left-∈ (≈∈ here S′≈[s′]))) ⟩
                              πT s′ T ⟶ πT s′ (renameAll s T)
                            ≡⟨ cong (πT s′ T ⟶_) (rename∅ {T = T} {S′≈[s′]} s≢s′) ⟩
                              πT s′ T ⟶ ∅
                            ∎ where open ≡-Reasoning


projectRecv : ∀ {s s′ S′} {T : GType S′} {sim : S′ ≈ [ s′ ]} → s ≢ s′ → πT s (T ⇒⟨ [] ⟩ renameAll s T) ≡ (∅ ⟶ πT s (renameAll s T))
projectRecv {s} {s′} {S′} {T = T} {S′≈[s′]} s≢s′ =
                              πT s (T ⇒⟨ [] ⟩ renameAll s T)
                            ≡⟨ project⇒ (right-∈ {as = (S′ ++ [])} (map-∈ {f = (λ x → s)} (≈∈ here S′≈[s′]))) ⟩
                              πT s T ⟶ πT s (renameAll s T)
                            ≡⟨ cong (_⟶ πT s (renameAll s T)) (project∅ (≈∉ (λ {here → refl ↯ s≢s′}) S′≈[s′])) ⟩
                              ∅ ⟶ πT s (renameAll s T)
                            ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- transport

transp-⊢ᵥ : ∀ {T T′ : LType} {Γ} -> T′ ≡ T -> Γ ⊢ᵥ T -> Γ ⊢ᵥ T′
transp-⊢ᵥ refl Ts = Ts

transp-⊢ₘ : ∀ {T T′ : LType} {Γ} -> T ≡ T′ -> Γ ⊢ₘ T -> Γ ⊢ₘ T′
transp-⊢ₘ refl Ts = Ts

bottom : ∀ {r Γ R} {T : GType R} → ¬ r ∈ R → π⋆ r Γ ⊢ᵥ πT r T 
bottom ¬p = transp-⊢ᵥ (project∅ ¬p) ntbotm

------------------------------------------------------------------------
-- here we go!

mutual
  πC : ∀ {Γ R} {T : GType R} → (r : Role) → Γ ⊩ₘ T → π⋆ r Γ ⊢ₘ (πT r T)
  πC {R = R} r t = π-Choreo r (r ∈? R) t


  π-Choreo : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ₘ T → π⋆ r Γ ⊢ₘ (πT r T)
  
  π-Choreo r r∈R (tval x) = ntval (π-Value r r∈R x)
  
  π-Choreo r _ (tapp {R} {R′} {ρ = ρ} x x₁) with r ∈? ((R ++ ρ) ++ R′)
  ... | yes r∈rrr = ntapp (transp-⊢ₘ (project⇒ r∈rrr) (πC r x)) (πC r x₁)
  ... | (no r∉rrr) =
    let
      r∉R : r ∉ R
      r∉R = left-∉ R ρ (left-∉ (R ++ ρ) R′ r∉rrr)
    
      x∅ = transp-⊢ₘ (project∅ r∉rrr) (π-Choreo r (no r∉rrr) x)
      x₁∅ = transp-⊢ₘ (project∅ r∉R) (π-Choreo r (no r∉R) x₁)

      T≡∅ = sym (project∅ (right-∉ (R ++ ρ) R′ r∉rrr))
    in transp-⊢ₘ T≡∅ (ntapp2 x∅ x₁∅)
  
  π-Choreo r r∈R (tsel x r₁ s l) with s ≟ r | r₁ ≟ r | s ≟ r₁
  ... | yes s=R | no r≠R | no s≠r = ntchor⊕ r l (πC r x)
  ... | no s≠R | yes r=R | no s≠r = ntoff& s [ (l , (πC r x)) ]
  ... | _ | _ | _ = πC r x

  π-Choreo r r∈R (tcase {R₁ = R₁} {R₂} x x₁ x₂) with r ∈? (R₁ ++ R₂)
  ... | yes a = ntcase (transp-⊢ₘ (project⊕ a) (πC r x)) (πC r x₁) (πC r x₂)
  ... | no a = ntapp (ntval (ntabs (nt⊔ (πC r x₁) (πC r x₂)))) (πC r x)



  πV : ∀ {Γ R} {T : GType R} (r : Role) → Γ ⊩ᵥ T → π⋆ r Γ ⊢ᵥ (πT r T)
  πV {R = R} r t = π-Value r (r ∈? R) t


  π-Value : ∀ {Γ R} {T : GType R} (r : Role) → Dec (r ∈ R) → Γ ⊩ᵥ T → π⋆ r Γ ⊢ᵥ (πT r T)
  
  π-Value r (yes p) (tvar x) = transp-⊢ᵥ refl (ntvar (π∈ x)) -- TODO sure?
  π-Value r (no ¬p) (tvar x) = bottom ¬p

  π-Value r (yes p) (tcom s s′ {S} {sim = sim} {T = T}) with s′ ≟ s
  ... | yes refl = transp-⊢ᵥ (project⇒ p) (ntabs (ntval (ntvar (here≡ (sym (≅-to-≡ (lem7 sim)))))))
  ... | no s′≠s with r ≟ s | r ≟ s′
  ... | yes refl | _ = transp-⊢ᵥ (projectSend {sim = sim} s′≠s) (ntsend s′)
  ... | _ | yes refl = transp-⊢ᵥ (projectRecv {sim = sim} s′≠s) (ntrecv s)
  π-Value r (yes p) (tcom s s′ {S} {sim = both S⊆[s] [s]⊆S} {T = T}) | no s′≠s | no r≠s | no r≠s′ = case (∈-++⁻ (S ++ []) p) of λ {
                             (inj₁ r∈S[]) → ∈-singleton (S⊆[s] (++[]-∈ r∈S[])) ↯ r≠s;
                             (inj₂ r∈S′) → ∈-singleton (≈∈ r∈S′ (≈map (λ _ → s′) (both [s]⊆S S⊆[s]))) ↯ r≠s′}

  π-Value r (no ¬p) (tcom r₁ s) = bottom ¬p
  
  π-Value r (yes p) (tproj1 {R} {R′} {T} {T′}) = let
      πproj = begin
          πT r ((T ⊛ T′) ⇒⟨ [] ⟩ T)
        ≡⟨ project⇒ p ⟩
          (πT r (T ⊛ T′)) ⟶ (πT r T)
        ≡⟨  cong (_⟶ (πT r T)) (project⊛
          (case ∈-++⁻ ((R ++ R′) ++ []) p of λ {
            (inj₁ r∈RR′[]) → ++[]-∈ r∈RR′[] ;
            (inj₂ r∈R) → ∈-++⁺ˡ r∈R }
          )) ⟩
          (((πT r T) ⋆ (πT r T′)) ⟶ (πT r T))
        ∎
    in transp-⊢ᵥ πproj ntproj1  where open ≡-Reasoning
  π-Value r (no ¬p) tproj1 = bottom ¬p
  
  π-Value r (yes p) (tproj2 {R} {R′} {T} {T′}) =
    let
      πproj = begin
          πT r ((T ⊛ T′) ⇒⟨ [] ⟩ T′)
        ≡⟨ project⇒ p ⟩
          (πT r (T ⊛ T′)) ⟶ (πT r T′)
        ≡⟨ cong (_⟶ (πT r T′)) (project⊛
          (case ∈-++⁻ ((R ++ R′) ++ []) p of λ {
            (inj₁ r∈RR′[]) → ++[]-∈ r∈RR′[] ;
            (inj₂ r∈R′) → ∈-++⁺ʳ R r∈R′}
          )) ⟩
          (((πT r T) ⋆ (πT r T′)) ⟶ (πT r T′))
        ∎
    in transp-⊢ᵥ πproj ntproj2 where open ≡-Reasoning
  π-Value r (no ¬p) tproj2 = bottom ¬p
  
  π-Value r (yes p) (tabs ρ x) = transp-⊢ᵥ (project⇒ p) (ntabs (πC r x))
  π-Value r (no ¬p) (tabs ρ x) = bottom ¬p
  
  π-Value r (yes p) (tunit r₁) = transp-⊢ᵥ (project○ p) ntunit
  π-Value r (no ¬p) (tunit r₁) = bottom ¬p
  
  π-Value r (yes p) (tpair x x₁) = transp-⊢ᵥ (project⊛ p) (ntpair (πV r x) (πV r x₁))
  π-Value r (no ¬p) (tpair x x₁) = bottom ¬p
  
  π-Value r (yes p) (tinl x) = transp-⊢ᵥ (project⊕ p) (ntinl (πV r x))
  π-Value r (no ¬p) (tinl x) = bottom ¬p
  
  π-Value r (yes p) (tinr x) = transp-⊢ᵥ (project⊕ p) (ntinr (πV r x))
  π-Value r (no ¬p) (tinr x) = bottom ¬p
