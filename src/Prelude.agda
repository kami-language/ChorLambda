module Prelude where

open import Level using (Level)
open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Nat public using (Nat; zero; suc)
open import Agda.Builtin.List public using (List; []; _∷_)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_) -- this might be forbidden

------------------------------------------------------------------------
-- product
    
_×_ : ∀ {ℓ 𝓂} (A : Set ℓ) (B : Set 𝓂) → Set (ℓ ⊔ 𝓂)
A × B = Σ A (λ x → B)

------------------------------------------------------------------------
-- equality stuff

cong : ∀ {ℓ 𝓂} {A : Set ℓ} {B : Set 𝓂} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {ℓ} {X Y : Set ℓ} (eq : X ≡ Y) → (Y ≡ X)
sym refl = refl

coe : ∀ {ℓ} {X Y : Set ℓ} (x : X) (eq : X ≡ Y) → Y
coe x refl = x

trans : ∀ {ℓ} {X Y Z : Set ℓ} (eq : X ≡ Y) (eq₁ : Y ≡ Z) → X ≡ Z
trans refl refl = refl

------------------------------------------------------------------------
-- decidability stuff

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A


map′ : ∀ {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
map′ A→B B→A (yes p) = yes (A→B p)
map′ A→B B→A (no ¬p) = no λ b → B→A b ↯ ¬p


record DecEquable (A : Set) : Set where
  field
    _==_ : ∀ (x y : A) → Dec (x ≡ y)

open DecEquable {{...}} public

------------------------------------------------------------------------
-- numbers

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → (i : Fin n) → Fin (suc n)


suc-injective : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

infix 4 _≟_
_≟_ : ∀ {n} → (x y : Fin n) → Dec (x ≡ y)
zero ≟ zero  = yes refl
zero ≟ suc y = no λ()
suc x ≟ zero = no λ()
suc x ≟ suc y = map′ (cong suc) suc-injective (x ≟ y)


instance
 -- decequable-string : DecEquable String
 -- decequable-string = record { _==_ = _≟-str_ }

  decequable-role : ∀ {Θ} → DecEquable (Fin Θ)
  decequable-role = record { _==_ = _≟_}


------------------------------------------------------------------------
-- list stuff

[_] : ∀ {A : Set} (a : A) → List A
[ a ] = a ∷ []

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs


infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


infix 4 _∈_
data _∈_ {x} {X : Set x} : X → List X → Set x where
  here : ∀ {A Γ} → A ∈ (A ∷ Γ)
  there : ∀ {A B Γ} → A ∈ Γ → A ∈ (B ∷ Γ)


infix 4 _∉_
_∉_ : ∀ {x} {X : Set x} → X → List X → Set x
A ∉ Γ = ¬ (A ∈ Γ)


_∈?_ : ∀ {V} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∈ L)
r ∈? [] = no λ ()
r ∈? (x ∷ L) with (r == x)
...               | yes refl = yes here
...               | no a with r ∈? L
...                         | yes b = yes (there b)
...                         | no b = no λ { here → refl ↯ a; (there nono) → b nono}


_∉?_ : ∀ {V} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∉ L)
r ∉? [] = yes λ ()
r ∉? (x ∷ L) with (r == x) |  r ∉? L
... | yes refl | _ = no λ x₁ → x₁ here
... | no proof | yes proof₁ = yes λ { here → refl ↯ proof ; (there x₁) → proof₁ x₁}
... | no proof | no proof₁ = no λ {x₁ → (λ a → x₁ (there a) ) ↯ proof₁}


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

infixl 3 _⊆_
_⊆_ : ∀ {A : Set} → (List A) → (List A) → Set
Γ ⊆ Γ′ = ∀ {A} → A ∈ Γ → A ∈ Γ′

data _≈_ : ∀ {A : Set} → (List A) → (List A) → Set (Level.suc Level.zero) where
  both : ∀ {A} {L L′ : List A} → L ⊆ L′ → L′ ⊆ L → L ≈ L′


keep : ∀ {A : Set} {L L′ : List A} {a : A} → L ⊆ L′ → (a ∷ L) ⊆ (a ∷ L′)
keep LL = λ { here → here ; (there x) → there (LL x) }

------------------------------------------------------------------------
-- list stuff proofs

left-∈ : ∀{A : Set} {a : A} {as bs} -> a ∈ as -> a ∈ (as ++ bs)
left-∈ here = here
left-∈ (there a∈as) = there (left-∈ a∈as)

right-∈ : ∀{A : Set} {a : A} {as bs} -> a ∈ bs -> a ∈ as ++ bs
right-∈ {as = []} a∈bs = a∈bs
right-∈ {as = x ∷ as} a∈bs = there (right-∈ a∈bs)

left-∉ : ∀{A : Set} {a : A} as bs -> a ∉ as ++ bs -> a ∉ as
left-∉ _ _ p = λ x → p (left-∈ x)

right-∉ : ∀{A : Set} {a : A} as bs -> a ∉ as ++ bs -> a ∉ bs
right-∉ _ _ p = λ x → p (right-∈ x)

map-∈ : ∀ {A B : Set} {a : A} {L : List A} {f : A → B} → a ∈ L → f a ∈ map f L
map-∈ here = here
map-∈ (there a∈L) = there (map-∈ a∈L)

≡-∷ : {A : Set} {a : A} {L M : List A} → L ≡ M → a ∷ L ≡ a ∷ M
≡-∷ {a = a} refl = cong (λ x → a ∷ x) refl

map-++ : {A B : Set} (L M : List A) {f : A → B} → map f L ++ map f M ≡ map f (L ++ M) 
map-++ [] M = refl
map-++ (x ∷ L) M = ≡-∷ (map-++ L M)

≡-++ : {A : Set} {L M N : List A} → L ≡ M → N ++ L ≡ N ++ M
≡-++ refl = refl
