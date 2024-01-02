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
  π-GType r (yes p) (◎＠ r₁) = ○
  π-GType r (no ¬p) T = ∅
  
  πT : ∀ {R : Roles} → (r : Role) → (T : GType R) → LType
  πT {R} r t = π-GType r (r ∈? R) t

project⇒ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} {ρ : Roles} → (r ∈ ((R ++ ρ) ++ R′)) → πT r (T ⇒⟨ ρ ⟩ T′) ≡ (πT r T) ⟶ (πT r T′)
project⇒ {R} {R′} {T} {T′} {r} {ρ} r∈RρR′ = cong (λ p → π-GType r p (T ⇒⟨ ρ ⟩ T′)) (snd ((∈→∈? r∈RρR′)))
  
project⊕ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} → (r ∈ (R ++ R′)) → πT r (T ⊕ T′) ≡ (πT r T) ＋ (πT r T′)
project⊕ {R} {R′} {T} {T′} {r} r∈RR′ = cong (λ p → π-GType r p (T ⊕ T′)) (snd (∈→∈? r∈RR′))

project⊛ : ∀ {R R′ : Roles} {T : GType R} {T′ : GType R′} {r : Role} → (r ∈ (R ++ R′)) → πT r (T ⊛ T′) ≡ (πT r T) ⋆ (πT r T′)
project⊛ {R} {R′} {T} {T′} {r} r∈RR′ = cong (λ p → π-GType r p (T ⊛ T′)) (snd (∈→∈? r∈RR′))

project○ : ∀ {r s : Role} → r ∈ [ s ] → πT r (◎＠ s) ≡ ○
project○ {r} {s} r=s = cong (λ p → π-GType r p (◎＠ s)) (snd (∈→∈? r=s))

project∅ : ∀ {R : Roles} {T : GType R} {r : Role} → (r ∉ R) → πT r T ≡ ∅
project∅ {R} {T} {r} r∉RR′ =
  let
    r-no : (r ∈? R) ≡ no _
    r-no = snd (∉→∈? r∉RR′)
  in cong (λ rr → π-GType r rr T) r-no
  
transp-⊢ᵥ : ∀ {T T′ : LType} {Γ} -> T′ ≡ T -> Γ ⊢ᵥ T -> Γ ⊢ᵥ T′
transp-⊢ᵥ refl Ts = Ts

transp-⊢ₘ : ∀ {T T′ : LType} {Γ} -> T ≡ T′ -> Γ ⊢ₘ T -> Γ ⊢ₘ T′
transp-⊢ₘ refl Ts = Ts

π⋆ : Role → Global.Context → Local.Context
π⋆ r = map (λ { (_ , t) → πT r t })


bottom : ∀ {r Γ R} {T : GType R} → ¬ r ∈ R → π⋆ r Γ ⊢ᵥ πT r T 
bottom ¬p = transp-⊢ᵥ (project∅ ¬p) ntbotm

π∈ : ∀ {R T Γ r} → (R , T) ∈ Γ → _∈_ (πT r T) (π⋆ r Γ)
π∈ here = here
π∈ (there x) = there (π∈ x)

terrible : ∀ {s s′ : Role} {S′ : Roles} {T : GType S′} → {S′ ≈ [ s′ ]} → s ≢ s′ → πT s′ (rename (λ _ → s) T) ≡ ∅
terrible {s} {s′} {T = T} {S′≈[s′]} s≢s′ = cong (λ S → π-GType s′ S  (rename (λ _ → s) T)) (snd (∉→∈? (≈∉ (λ {here → refl ↯ s≢s′}) (≈map (λ _ → s) S′≈[s′]))))

{-
terible : ∀ {s : Role} {S : Roles} {T : GType S} → {S≈[s] : S ≈ [ s ]} → rename (λ _ → s) T ≡ coe T (cong GType (≈cmap S≈[s]))
terible = {!!}


terrible2 : ∀ {r s : Role} {S : Roles} {T : GType S} → {S ≈ [ s ]} → r ∈ S → πT r (rename (λ _ → s) T) ≡ πT r T
terrible2 {r} {s} {T = T} {S≈[s]} r∈S = cong (πT r) terible -- πT r (rename (λ _ → s) T) ≡⟨ {!!} ⟩ πT r T ∎
-}

terible : ∀ {s S T} (S≈[s] : S ≈ [ s ]) → rename (λ _ → s) T ≡ coe T (cong GType (≈cmap S≈[s]))
terible S≈[s] = {!!}

terrible2 : ∀ {r s : Role} {S : Roles} {T : GType S} → {sim : S ≈ [ s ]} → r ∈ S → πT r (rename (λ _ → s) T) ≡ πT r T
terrible2 {r} {s} {S} {T} {S≈[s]} r∈S =
  begin
    πT r (rename (λ _ → s) T)
  ≡⟨⟩
    π-GType r (r ∈? map (λ _ → s) S) (rename (λ _ → s) T)
  ≡⟨ cong (π-GType r _) (terible S≈[s]) ⟩
    π-GType r (r ∈? map (λ _ → s) S) (coe T (cong GType (≈cmap S≈[s])))
  ≡⟨ {!!} ⟩
    π-GType r (r ∈? S) T
  ≡⟨⟩
    πT r T
  ∎

terrrible : ∀ {s s′ : Role} {S′ : Roles} {T : GType S′} {sim : S′ ≈ [ s′ ]} → s ≢ s′ → πT s′ (T ⇒⟨ [] ⟩ rename (λ x → s) T) ≡ (πT s′ T ⟶ ∅)
terrrible {s} {s′} {T = T} {S′≈[s′]} s≢s′ = πT s′ (T ⇒⟨ [] ⟩ rename (λ _ → s) T)
                            ≡⟨ project⇒ (left-∈ (left-∈ (≈∈ here S′≈[s′]))) ⟩
                              πT s′ T ⟶ (πT s′ (rename (λ _ → s) T))
                            ≡⟨ cong (πT s′ T ⟶_) (terrible {T = T} {S′≈[s′]} s≢s′) ⟩
                              πT s′ T ⟶ ∅
                            ∎
                            
terrrible2 : ∀ {s s′ : Role} {S′ : Roles} {T : GType S′} {sim : S′ ≈ [ s′ ]} → s ≢ s′ → πT s (T ⇒⟨ [] ⟩ rename (λ x → s) T) ≡ (∅ ⟶ (πT s (rename (λ x → s) T)))
terrrible2 {s} {s′} {T = T} {S′≈[s′]} s≢s′ =
                              πT s (T ⇒⟨ [] ⟩ rename (λ x → s) T)
                            ≡⟨ project⇒ (right-∈ (map-∈ {f = (λ x → s)} (≈∈ here S′≈[s′]))) ⟩
                              πT s T ⟶ (πT s (rename (λ x → s) T))
                            ≡⟨ cong (_⟶ πT s (rename (λ x → s) T)) (project∅ (≈∉ (λ {here → refl ↯ s≢s′}) S′≈[s′])) ⟩
                              (∅ ⟶ (πT s (rename (λ x → s) T)))
                            ∎
                            
here≡ : ∀ {x} {X : Set x} {A B : X} {L : List X} → A ≡ B → A ∈ (B ∷ L)
here≡ refl = here

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
  ... | yes refl = transp-⊢ᵥ (project⇒ p) (ntabs (ntval (ntvar (here≡ (terrible2 {sim = sim} (case (∈-++⁻ (S ++ []) p) of λ {(inj₁ left) → ++[]-∈ left; (inj₂ right) → ≡-∈ right (≈cmap sim)}))))))
  ... | no s′≠s with r ≟ s | r ≟ s′
  ... | yes refl | _ = transp-⊢ᵥ (terrrible {sim = sim} s′≠s) (ntsend s′)
  ... | _ | yes refl = transp-⊢ᵥ (terrrible2 {sim = sim} s′≠s) (ntrecv s)

  π-Value r (no ¬p) (tcom r₁ s) = bottom ¬p
  
  π-Value r (yes p) (tproj1 {R} {R′} {T} {T′}) = let
      πproj = begin
          πT r ((T ⊛ T′) ⇒⟨ [] ⟩ T)
        ≡⟨ project⇒ p ⟩
          (πT r (T ⊛ T′)) ⟶ (πT r T)
        ≡⟨  cong (λ x → (x ⟶ (πT r T))) (project⊛
          (case ∈-++⁻ ((R ++ R′) ++ []) p of λ {
            (inj₁ r∈RR′[]) → ++[]-∈ r∈RR′[] ;
            (inj₂ r∈R) → ∈-++⁺ˡ r∈R }
          )) ⟩
          (((πT r T) ⋆ (πT r T′)) ⟶ (πT r T))
        ∎
    in transp-⊢ᵥ πproj ntproj1
  π-Value r (no ¬p) tproj1 = bottom ¬p
  
  π-Value r (yes p) (tproj2 {R} {R′} {T} {T′}) =
    let
      πproj = begin
          πT r ((T ⊛ T′) ⇒⟨ [] ⟩ T′)
        ≡⟨ project⇒ p ⟩
          (πT r (T ⊛ T′)) ⟶ (πT r T′)
        ≡⟨ cong (λ x → (x ⟶ (πT r T′))) (project⊛
          (case ∈-++⁻ ((R ++ R′) ++ []) p of λ {
            (inj₁ r∈RR′[]) → ++[]-∈ r∈RR′[] ;
            (inj₂ r∈R′) → ∈-++⁺ʳ R r∈R′}
          )) ⟩
          (((πT r T) ⋆ (πT r T′)) ⟶ (πT r T′))
        ∎
    in transp-⊢ᵥ πproj ntproj2
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
