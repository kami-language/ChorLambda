open import Data.Bool using (Bool ; true ; false ; _∨_ ; not ; T)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary using (¬_)

infix 1 _⇒_
_⇒_ : Bool → Bool → Bool
true ⇒ true = true
true ⇒ false = false
false ⇒ true = true
false ⇒ false = true

thm : ∀ (a b c : Bool) → T ((not a ⇒ b ∨ c) ⇒ (not a ⇒ b) ∨ (not a ⇒ c))
thm false false false = tt
thm false false true = tt
thm false true false = tt
thm false true true = tt
thm true false false = tt
thm true false true = tt
thm true true false = tt
thm true true true = tt

no-thm : ∀ {a b c : Set} → (a → b ⊎ c) → (a → b) ⊎ (a → c)
no-thm = λ x → {!!}
