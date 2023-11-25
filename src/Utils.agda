module Utils where

open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟-str_)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Relation.Unary.Any using (here; there)

----------------------------------------------------
-- list stuff

record DecEquable (A : Set) : Set where
  field
    _==_ : ∀ (x y : A) → Dec (x ≡ y)

open DecEquable {{...}}

instance
  decequable-string : DecEquable String
  decequable-string = record { _==_ = _≟-str_ }

  decequable-role : ∀ {Θ} → DecEquable (Fin Θ)
  decequable-role = record { _==_ = _≟_}


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

