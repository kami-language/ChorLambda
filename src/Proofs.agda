module Proofs where

open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Base
open import Global
open import EndpointProjection
open import Local
open import ChoreoTyping
open import Utils

closed : ∀ {Θ} → Choreography Θ → Set
closed C = (fv C) ≡ []

adequateEPP : ∀ {Θ Γ T R} → (M : Choreography Θ) → closed M → (Ts : Γ ⊢ M ⦂ T) → R ∉ ((croles M) ++ (roles T)) → ((projectChoreo R M Ts) ≡ just (V ⊥))
adequateEPP .(V (Λ _ _ _)) clsd (tabs Ts ρ) rls = {!!}
adequateEPP .(_ ∙ _) clsd (tapp Ts Ts₁) rls = {!!}
adequateEPP .(case _ (_ , _) (_ , _)) clsd (tcase Ts Ts₁ Ts₂) rls = {!!}
adequateEPP .(select _ _ _ _) clsd (tsel Ts) rls = {!!}
adequateEPP .(V (O＠ _)) clsd tunit rls = {!!}
adequateEPP .(V (com _ _)) clsd tcom rls = {!!}
adequateEPP .(V (Pair _ _)) clsd (tpair Ts Ts₁) rls = {!!}
adequateEPP .(V fst) clsd tproj1 rls = {!!}
adequateEPP .(V snd) clsd tproj2 rls = {!!}
adequateEPP .(V (Inl _)) clsd (tinl Ts) rls = {!!}
adequateEPP .(V (Inr _)) clsd (tinr Ts) rls = {!!}


lemma35 : ∀ {Θ Γ T R w} → (v : Value Θ) → (Ts : Γ ⊢ (V v) ⦂ T) → R ∈ (croles (V v)) → ((projectVal R v Ts) ≡ just w)
lemma35 (Λ x x₁ x₂) Ts rls = {!!}
lemma35 (Inl v) Ts rls = {!!}
lemma35 (Inr v) Ts rls = {!!}
lemma35 (Pair v v₁) Ts rls = {!!}
lemma35 (O＠ x)  Ts rls = {!!}
lemma35 (com x x₁) Ts rls = {!!}

lemma36 : ∀ {Θ R} → (T : Type Θ) → R ∉ (roles T) → ((projectType R T) ≡ ⊥)
lemma36 {R = R} T rls with (R ∈? roles T)
... | yes i = i ↯ rls 
... | no ¬i = refl


lemma37 : ∀ {Θ Γ T R} → (v : Value Θ) → (Ts : Γ ⊢ (V v) ⦂ T) → R ∉ (roles T) → ((projectVal R v Ts) ≡ just ⊥)
lemma37 {T = T} {R = R} (var x) Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {R = R} (Λ x x₁ x₂) Ts rls = {!!}
lemma37 {R = R} (Inl v) Ts rls = {!!}
lemma37 {R = R} (Inr v) Ts rls = {!!}
lemma37 {T = T} {R = R} fst Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T} {R = R} snd Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {R = R} (Pair v v₁) (tpair {T = ⟶ x T T₁} Ts Ts₁) rls = ?
lemma37 {R = R} (Pair v v₁) (tpair {T = T ＋ T₁} Ts Ts₁) rls = ?
lemma37 {R = R} (Pair v v₁) (tpair {T = T mul T₁} Ts Ts₁) rls = ?
lemma37 {R = R} (Pair v v₁) (tpair {T = o＠ x} Ts Ts₁) rls = ?
lemma37 {T = T} {R = R} (O＠ x) Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {R = R} (com x x₁) Ts rls = {!!}
