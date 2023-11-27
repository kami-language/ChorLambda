module Proofs where

open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality

open import Base
open import Global
open import EndpointProjection
open import Local
open import ChoreoTyping

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
lemma35 = {!!}

lemma36 : ∀ {Θ R} → (T : Type Θ) → R ∉ (roles T) → ((projectType R T) ≡ ⊥)
lemma36 (⟶ x T T₁) rls = {!!}
lemma36 (T ＋ T₁) rls = {!!}
lemma36 (T mul T₁) rls = {!!}
lemma36 (o＠ x) rls = {!!}

lemma37 : ∀ {Θ Γ T R} → (v : Value Θ) → (Ts : Γ ⊢ (V v) ⦂ T) → R ∉ (roles T) → ((projectVal R v Ts) ≡ just ⊥)
lemma37 = {!!}
