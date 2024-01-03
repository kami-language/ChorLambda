{-# OPTIONS --rewriting #-}

module Renaming where

open import Prelude
open import Base
open import Types

----------------------------------------------------
-- role renaming

rename : ∀ {R} → (f : Nat → Nat) → GType R → GType (map f R)
rename f (_⇒⟨_⟩_ T ρ T₁) = rename f T ⇒⟨ map f ρ ⟩ rename f T₁
rename f (_⊛_ T T₁) = rename f T ⊛ rename f T₁
rename f (_⊕_ T T₁) = rename f T ⊕ rename f T₁
rename f (◎＠ r) = ◎＠ (f r)

renameAll : ∀ {R} → (s : Role) → (T : GType R) → GType (map (λ _ → s) R)
renameAll s T = rename (λ _ → s) T


----------------------------------------------------
-- properties of single participant type renaming

renameAllSingle : ∀ {s S} {T : GType S} (p : S ≈ [ s ]) → T ≅ renameAll s T
renameAllSingle {s} {S = M} {T = _⇒⟨_⟩_ {R} {S} T ρ T₁} sim = let
    (Rρ⊆M , S⊆M) = ⊆-++ {M = M} {L = (R ++ ρ)} refl
    (R⊆Rρ , ρ⊆Rρ) = ⊆-++ {M = (R ++ ρ)} {L = R} refl
    R⊆M = ⊆-++⁺ˡ R⊆Rρ
    ρ⊆M = ⊆-++⁺ˡ ρ⊆Rρ
    conR = ≈const⊆ sim R⊆M
    conρ = ≈const⊆ sim ρ⊆M
    conS = ≈const⊆ sim S⊆M
  in begin (T ⇒⟨ ρ ⟩ T₁)
     ≅⟨ icong (λ _ → List Nat) (≈cmap conρ) (T ⇒⟨_⟩ T₁) (≡-to-≅ (≈cmap conρ)) ⟩
       T ⇒⟨ map (λ _ → s) ρ ⟩ T₁
     ≅⟨ icong GType (≈cmap conR) (_⇒⟨ map (λ _ → s) ρ ⟩ T₁) (renameAllSingle {T = T} conR) ⟩
       renameAll s T ⇒⟨ map (λ _ → s) ρ ⟩ T₁
     ≅⟨ icong GType (≈cmap conS) (renameAll s T ⇒⟨ map (λ _ → s) ρ ⟩_) (renameAllSingle {T = T₁} conS) ⟩
       renameAll s T ⇒⟨ map (λ _ → s) ρ ⟩ renameAll s T₁ ∎
  where open ≅-Reasoning

renameAllSingle {s} {S = M} {T = _⊛_ {R} {S} T T₁} sim = let
    (left , right) = ⊆-++ {M = M} {L = R} refl
    conl = renameAllSingle {T = T} (≈const⊆ sim left)
    conr = renameAllSingle {T = T₁} (≈const⊆ sim right)
  in begin T ⊛ T₁
     ≅⟨ icong GType (≈cmap (≈const⊆ sim left)) (_⊛ T₁) conl ⟩
       renameAll s T ⊛ T₁
     ≅⟨ icong GType (≈cmap (≈const⊆ sim right)) (renameAll s T ⊛_) conr ⟩
       renameAll s T ⊛ renameAll s T₁ ∎
   where open ≅-Reasoning

renameAllSingle {s} {S = M} {T = _⊕_ {R} {S} T T₁} sim =
  let
    (left , right) = ⊆-++ {M = M} {L = R} refl
    conl = renameAllSingle {T = T} (≈const⊆ sim left)
    conr = renameAllSingle {T = T₁} (≈const⊆ sim right)
  in begin T ⊕ T₁
     ≅⟨ icong GType (≈cmap (≈const⊆ sim left)) (_⊕ T₁) conl ⟩
       renameAll s T ⊕ T₁
     ≅⟨ icong GType (≈cmap (≈const⊆ sim right)) (renameAll s T ⊕_) conr ⟩
       renameAll s T ⊕ renameAll s T₁ ∎
  where open ≅-Reasoning
  
renameAllSingle {s} {T = ◎＠ r} (both S⊆[s] [s]⊆S) = icong (λ _ → Nat) (≈cmap (both S⊆[s] [s]⊆S)) ◎＠ (≡-to-≅ (∈-singleton (S⊆[s] here)))


