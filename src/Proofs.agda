module Proofs where

open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties renaming (++⁺ʳ to anyConcL; ++⁺ˡ to anyConc)
open import Data.Fin using (Fin; #_)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Vec using (Vec; _∷_; lookup) renaming ([_] to ⟪_⟫)

open import Base
open import Global
open import EndpointProjection
open import Local
open import ChoreoTyping
open import Utils

closed : ∀ {Θ} → Choreography Θ → Set
closed C = (fv C) ≡ []
{-
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
-}

postulate
 rolesInc : ∀ {Θ} {C : Choreography Θ} {R : Role Θ} {T : Type Θ} {Γ : TCtx Θ} → Γ ⊢ C ⦂ T → R ∈ croles C → R ∈ roles T

lemma35 : ∀ {Θ Γ T R} → (v : Value Θ) → (Ts : Γ ⊢ (V v) ⦂ T) → R ∈ (croles (V v)) → Σ (LValue Θ) (λ w → ((projectVal R v Ts) ≡ just w))
lemma35 (Λ x T M) (tabs Ts ρ) rls = {!!}
lemma35 {Θ = Θ} {T = T ＋ T′} {R = R} (Inl v) (tinl Ts) rls with R ∈? croles (V (Inl v)) | R ∈? roles (T ＋ T′)
... | yes A | yes B = lemma35 v Ts rls
... | yes A | no B = (rolesInc (tinl Ts) A) ↯ B
... | no A | _ = rls ↯ A
lemma35 (Inr v) Ts rls = {!!}
lemma35 (Pair v v₁) Ts rls = {!!}
lemma35 {T = T} {R = R} (O＠ r) tunit rls with R ∈? roles T
... | yes A = O , refl
... | no A = ⊥ , refl
lemma35 (com r s) Ts rls = {!!}

lemma36 : ∀ {Θ R} → (T : Type Θ) → R ∉ (roles T) → ((projectType R T) ≡ ⊥)
lemma36 {R = R} T rls with (R ∈? roles T)
... | yes i = i ↯ rls 
... | no ¬i = refl


embedRoles : ∀  {Θ} {R : Role Θ} (T : Type 1) → R ∈ (roles (embed T R))
embedRoles {Θ} {R} (⟶ ρ T T₁) = anyConcL (map (lookup ⟪ R ⟫) ρ) (anyConc (embedRoles T)) 
embedRoles (T ＋ T₁) = anyConc (embedRoles T)
embedRoles (T mul T₁) = anyConc (embedRoles T)
embedRoles (o＠ Data.Fin.zero) = here refl


lemma37 : ∀ {Θ Γ T R} → (v : Value Θ) → (Ts : Γ ⊢ (V v) ⦂ T) → R ∉ (roles T) → ((projectVal R v Ts) ≡ just ⊥)
lemma37 {T = T} {R = R} (var x) Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = ⟶ ρ T T₁} {R = R} (Λ x .T x₂) (tabs Ts .ρ) rls with (R ∈? ( ρ ++ roles T ++ roles T₁))
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T} {R = R} (Inl v) (tinl Ts) rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T} {R = R} (Inr v) (tinr Ts) rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T} {R = R} fst Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T} {R = R} snd Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = T₁ mul T₂} {R = R} (Pair v v₁) (tpair Ts Ts₁) rls with (R ∈? (roles T₁ ++ roles T₂))
... | yes a = a ↯ rls
... | no ¬a with (projectVal R v Ts) | (projectVal R v₁ Ts₁) | lemma37 {R = R} v Ts (λ x → anyConc x ↯ rls) | lemma37 {R = R} v₁ Ts₁ (λ x → anyConcL (roles T₁) x ↯ rls)
...            | just ⊥ | just ⊥ | refl | refl = refl
lemma37 {T = T} {R = R} (O＠ x) Ts rls with (R ∈? roles T)
... | yes i = i ↯ rls
... | no ¬i = refl
lemma37 {T = (⟶ [] T₁ T₂)} {R} (com r s) (tcom {T}) rls with R ∈? roles (⟶ [] T₁ T₂)
... | yes a = a ↯ rls
lemma37 {T = (⟶ [] T₁ T₂)} {R} (com r s) (tcom {T}) rls | no ¬a with r ≟ s
lemma37 {T = (⟶ [] T₁ T₂)} {R} (com r s) (tcom {T}) rls | no ¬a | yes refl with R ≟ r
... | yes refl = anyConc (embedRoles T) ↯ rls
... | no _ = refl
lemma37 {T = (⟶ [] T₁ T₂)} {R} (com r s) (tcom {T}) rls | no ¬b | no r≠s with R ≟ r | R ≟ s 
... | yes refl | _ = anyConc (embedRoles T) ↯ rls
... | no a | yes refl = anyConcL (roles (embed T r)) (embedRoles T) ↯ rls
... | no _ | no _  = refl
