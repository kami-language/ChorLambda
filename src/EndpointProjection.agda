module EndpointProjection where

open import Prelude
open import Base
open import Global
open import Local

data onlyR : (r : Role) → (L : Roles) → Set where
  empty : ∀ {r} → onlyR r []
  suc : ∀ {r L} → onlyR r L → onlyR r (r ∷ L)

π-GType : ∀ {R rR : Roles} → (r : Role) → {r ∈ R} → (onlyR r rR) → (T : GType R) → LType rR
π-GType r rR (T ⇒⟨ ρ ⟩ T₁) = {!π-GType r T ⟶ π-GType r T₁!}
π-GType r rR (T ⊛ T₁) = {!!}
π-GType r rR (T ⊕ T₁) = {!!}
π-GType r rR (⦅⦆＠ r₁) = {!!}
