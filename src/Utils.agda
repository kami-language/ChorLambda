module Utils where

open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟-str_)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)


----------------------------------------------------
-- list stuff

record DecEquable (A : Set) : Set where
  field
    _==_ : ∀ (x y : A) → Dec (x ≡ y)

open DecEquable {{...}} public

instance
  decequable-string : DecEquable String
  decequable-string = record { _==_ = _≟-str_ }

  decequable-role : ∀ {Θ} → DecEquable (Fin Θ)
  decequable-role = record { _==_ = _≟_}


_∉?_ : ∀ {V} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∉ L)
r ∉? [] = yes λ ()
r ∉? (x ∷ L) with (r == x) |  r ∉? L
... | yes proof | _ = no λ x₁ → x₁ (here proof)
... | no proof | yes proof₁ = yes λ { (here px) → px ↯ proof ; (there x₁) → proof₁ x₁}
... | no proof | no proof₁ = no λ {x₁ → (λ a → x₁ (there a) ) ↯ proof₁}




_∈?_ : ∀ {V} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∈ L)
r ∈? [] = no λ ()
r ∈? (x ∷ L) with (r == x)
...               | yes a = yes (here a)
...               | no a with r ∈? L
...                         | yes b = yes (there b)
...                         | no b = no λ { (here px) → a px; (there nono) → b nono}


_∖_ : ∀ {A} {{_ : DecEquable A}} → List A → A → List A
[] ∖ a = []
(x ∷ L) ∖ a with a == x
... | yes _ = L ∖ a
... | no _ = x ∷ (L ∖ a)

-- carefule this does random things with duplicates
_∩_ : ∀ {V} {{_ : DecEquable V}} → List V → List V → List V
[] ∩ L′ = []
(x ∷ L) ∩ L′ with x ∈? L′
... | yes _ = x ∷ (L ∩ L′)
... | no _ = L ∩ L′


------------------------------------------------------------------------
-- Proofs

open import Data.List using (_++_)

postulate
  left-∈ : ∀{A : Set} {a : A} {as bs} -> a ∈ as -> a ∈ as ++ bs
  right-∈ : ∀{A : Set} {a : A} {as bs} -> a ∈ bs -> a ∈ as ++ bs

left-∉ : ∀{A : Set} {a : A} as bs -> a ∉ as ++ bs -> a ∉ as
left-∉ _ _ p = λ x → p (left-∈ x)

right-∉ : ∀{A : Set} {a : A} as bs -> a ∉ as ++ bs -> a ∉ bs
right-∉ _ _ p = λ x → p (right-∈ x)

