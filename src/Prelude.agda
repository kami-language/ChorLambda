module Prelude where

open import Level using (Level)
open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Nat public using (Nat; zero; suc)
open import Agda.Builtin.List public using (List; []; _∷_)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public

------------------------------------------------------------------------
-- negation

record Irrelevant {𝒶} (A : Set 𝒶) : Set 𝒶 where
  constructor ⟦_⟧
  field .irrelevant : A

open Irrelevant public

private
  data Empty : Set where

⊥ : Set
⊥ = Irrelevant Empty

infix 3 ¬_
¬_ : ∀ {𝒶} → Set 𝒶 → Set 𝒶
¬ A = A → ⊥

⊥-elim : ∀ {𝒶} {A : Set 𝒶} → ⊥ → A
⊥-elim ()

_↯_ : ∀ {𝒶 ℓ : Level} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

------------------------------------------------------------------------
-- product and sum
    
_×_ : ∀ {ℓ 𝓂} (A : Set ℓ) (B : Set 𝓂) → Set (ℓ ⊔ 𝓂)
A × B = Σ A (λ x → B)

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B
  
------------------------------------------------------------------------
-- functions

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

case_return_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a}  {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f
------------------------------------------------------------------------
-- bool
{-
infix  0 if_then_else_

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f
-}
------------------------------------------------------------------------
-- equality stuff

infix 4 _≢_
_≢_ : ∀ {ℓ} {A : Set ℓ} (a b : A) → Set ℓ
a ≢ b = ¬ (a ≡ b)

cong : ∀ {ℓ 𝓂} {A : Set ℓ} {B : Set 𝓂} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {ℓ} {Ξ : Set ℓ} {X Y : Ξ} (eq : X ≡ Y) → (Y ≡ X)
sym refl = refl

coe : ∀ {ℓ} {X Y : Set ℓ} (x : X) (eq : X ≡ Y) → Y
coe x refl = x

trans : ∀ {ℓ} {A : Set ℓ} {X Y Z : A} (eq : X ≡ Y) (eq₁ : Y ≡ Z) → X ≡ Z
trans refl refl = refl


infix  1 begin_
infixr 2 _≡⟨⟩_ step-≡
infix  3 _∎

begin_ : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≡ y
    -----
  → x ≡ y
begin x≡y  =  x≡y

_≡⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y : A}
  → x ≡ y
    -----
  → x ≡ y
x ≡⟨⟩ x≡y  =  x≡y

step-≡ : ∀ {ℓ} {A : Set ℓ} (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ x y≡z x≡y  =  trans x≡y y≡z

syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

_∎ : ∀ {ℓ} {A : Set ℓ} (x : A)
    -----
  → x ≡ x
x ∎  =  refl

------------------------------------------------------------------------
-- decidability stuff

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : (p : A) → Dec A
  no : (¬p : ¬ A) → Dec A


map′ : ∀ {ℓ} {A B : Set ℓ} → (A → B) → (B → A) → Dec A → Dec B
map′ A→B B→A (yes p) = yes (A→B p)
map′ A→B B→A (no ¬p) = no λ b → B→A b ↯ ¬p


record DecEquable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _==_ : ∀ (x y : A) → Dec (x ≡ y)

open DecEquable {{...}} public

------------------------------------------------------------------------
-- numbers

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → (i : Fin n) → Fin (suc n)


suc-injective : ∀ {i j : Nat} → suc i ≡ suc j → i ≡ j
suc-injective refl = refl

infix 4 _≟_
_≟_ : (x y : Nat) → Dec (x ≡ y)
zero ≟ zero  = yes refl
zero ≟ suc y = no λ()
suc x ≟ zero = no λ()
suc x ≟ suc y = map′ (cong suc) suc-injective (x ≟ y)

instance
 -- decequable-string : DecEquable String
 -- decequable-string = record { _==_ = _≟-str_ }

  decequable-nat : DecEquable Nat
  decequable-nat = record { _==_ = _≟_}
  
 -- decequable-role : ∀ {Θ} → DecEquable (Fin Θ)
 -- decequable-role = record { _==_ = _≟_}


------------------------------------------------------------------------
-- list stuff

[_] : ∀ {A : Set} (a : A) → List A
[ a ] = a ∷ []

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs


infixr 5 _++_
_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infix 4 _∈_
data _∈_ {x} {X : Set x} : X → List X → Set x where
  here : ∀ {A Γ} → A ∈ (A ∷ Γ)
  there : ∀ {A B Γ} → A ∈ Γ → A ∈ (B ∷ Γ)


infix 4 _∉_
_∉_ : ∀ {x} {X : Set x} → X → List X → Set x
A ∉ Γ = ¬ (A ∈ Γ)


_∈?_ : ∀ {ℓ} {V : Set ℓ} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∈ L)
r ∈? [] = no λ ()
r ∈? (x ∷ L) with (r == x) | r ∈? L
...               | yes refl | _ = yes here
...               | no _ | yes r∈L = yes (there r∈L)
...               | no r≠x | no r∉L = no λ { here → refl ↯ r≠x; (there r∈L) → r∈L ↯ r∉L}



_∉?_ : ∀ {ℓ} {V : Set ℓ} {{_ : DecEquable V}} → (R : V) → (L : List V) → Dec (R ∉ L)
r ∉? [] = yes λ ()
r ∉? (x ∷ L) with (r == x) |  r ∉? L
... | yes refl | _ = no λ x₁ → x₁ here
... | no proof | yes proof₁ = yes λ { here → refl ↯ proof ; (there x₁) → proof₁ x₁}
... | no proof | no proof₁ = no λ {x₁ → (λ a → x₁ (there a) ) ↯ proof₁}


_∖_ : ∀ {ℓ} {A : Set ℓ} {{_ : DecEquable A}} → List A → A → List A
[] ∖ a = []
(x ∷ L) ∖ a with a == x
... | yes _ = L ∖ a
... | no _ = x ∷ (L ∖ a)


-- carefule this does random things with duplicates
_∩_ : ∀ {ℓ} {V : Set ℓ} {{_ : DecEquable V}} → List V → List V → List V
[] ∩ L′ = []
(x ∷ L) ∩ L′ with x ∈? L′
... | yes _ = x ∷ (L ∩ L′)
... | no _ = L ∩ L′

infixl 3 _⊆_
_⊆_ : ∀ {ℓ} {A : Set ℓ} → (List A) → (List A) → Set ℓ
Γ ⊆ Γ′ = ∀ {A} → A ∈ Γ → A ∈ Γ′

data _≈_ : ∀ {A : Set} → (List A) → (List A) → Set where
--  both : ∀ {A} {L L′ : List A} → L ⊆ L′ → L′ ⊆ L → L ≈ L′

postulate
  ≈∈ : ∀ {A : Set} {r : A} {R S} → r ∈ R → S ≈ R → r ∈ S
  ≈∉ : ∀ {A : Set} {r : A} {R S} → r ∉ R → S ≈ R → r ∉ S
  ≈map : ∀ {A B : Set} {R S : List A} → (f : A → B) → S ≈ R → map f S ≈ map f R
  ≈cmap : ∀ {A B : Set} {R S : List A} {s : A} → S ≈ [ s ] → S ≡ map (λ _ → s) S


keep : ∀ {A : Set} {L L′ : List A} {a : A} → L ⊆ L′ → (a ∷ L) ⊆ (a ∷ L′)
keep LL = λ { here → here ; (there x) → there (LL x) }

------------------------------------------------------------------------
-- list stuff proofs

++-assoc : ∀ {ℓ} {A : Set ℓ} (x y z : List A) → (x ++ (y ++ z)) ≡ ((x ++ y) ++ z)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

left-∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs} -> a ∈ as -> a ∈ (as ++ bs)
left-∈ here = here
left-∈ (there a∈as) = there (left-∈ a∈as)

right-∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs} -> a ∈ bs -> a ∈ as ++ bs
right-∈ {as = []} a∈bs = a∈bs
right-∈ {as = x ∷ as} a∈bs = there (right-∈ a∈bs)

left-∉ : ∀ {ℓ} {A : Set ℓ} {a : A} as bs -> a ∉ as ++ bs -> a ∉ as
left-∉ _ _ p = λ x → p (left-∈ x)

right-∉ : ∀ {ℓ} {A : Set ℓ} {a : A} as bs -> a ∉ as ++ bs -> a ∉ bs
right-∉ _ _ p = λ x → p (right-∈ x)

map-∈ : ∀ {ℓ} {A B : Set ℓ} {a : A} {L : List A} {f : A → B} → a ∈ L → f a ∈ map f L
map-∈ here = here
map-∈ (there a∈L) = there (map-∈ a∈L)

∷-∈ : ∀ {ℓ} {A : Set ℓ} {a b : A} as -> a ∈ as -> a ∈ b ∷ as
∷-∈ = λ as → there

≡-∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {L M : List A} → a ∈ M → L ≡ M → a ∈ L
≡-∈ a∈M refl = a∈M

++[]-∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {L : List A} → a ∈ L ++ [] → a ∈ L
++[]-∈ {L = x ∷ L} here = here
++[]-∈ {L = x ∷ L} (there a∈L) = there (++[]-∈ a∈L)


≡-∷ : ∀ {ℓ} {A : Set ℓ} {a : A} {L M : List A} → L ≡ M → a ∷ L ≡ a ∷ M
≡-∷ {a = a} refl = cong (λ x → a ∷ x) refl

map-++ : ∀ {ℓ} {A B : Set ℓ} (L M : List A) {f : A → B} → map f L ++ map f M ≡ map f (L ++ M) 
map-++ [] M = refl
map-++ (x ∷ L) M = ≡-∷ (map-++ L M)

≡-++ : ∀ {ℓ} {A : Set ℓ} {L M N : List A} → L ≡ M → N ++ L ≡ N ++ M
≡-++ refl = refl

≡-++-right : ∀ {ℓ} {A : Set ℓ} {L M N : List A} → L ≡ M → L ++ N ≡ M ++ N
≡-++-right refl = refl

{-
dec-no : ∀ {ℓ} {A : Set ℓ} {{_ : DecEquable A}} {r : A} {R} → r ∈ R → Σ (r ∈ R) (λ p → r ∈? R ≡ yes p)
dec-no {r = r} {R = R} X with r ∈? R
... | yes p = _ , refl
... | no ¬p = X ↯ ¬p
-}

∈→∈? : ∀ {ℓ} {A : Set ℓ} {{_ : DecEquable A}} {r : A} {R} → r ∈ R → Σ (r ∈ R) (λ p → r ∈? R ≡ yes p)
∈→∈? {r = r} {R = R} X with r ∈? R
... | yes p = _ , refl
... | no ¬p = X ↯ ¬p

∉→∈? : ∀ {ℓ} {A : Set ℓ} {{_ : DecEquable A}} {r : A} {R} → r ∉ R → Σ (r ∉ R) (λ p → r ∈? R ≡ no p)
∉→∈? {r = r} {R = R} X with r ∈? R
... | no ¬p = _ , refl
... | yes p = p ↯ X

∈-++⁺ˡ : ∀ {ℓ} {V : Set ℓ} {xs ys : List V} {v : V} → v ∈ xs → v ∈ xs ++ ys
∈-++⁺ˡ here    = here
∈-++⁺ˡ (there k) = there (∈-++⁺ˡ k)

∈-++⁺ʳ : ∀ {ℓ} {V : Set ℓ} xs {ys : List V} {v : V} → v ∈ ys → v ∈ xs ++ ys
∈-++⁺ʳ []       k = k
∈-++⁺ʳ (x ∷ xs) k = there (∈-++⁺ʳ xs k)
  
∈-++⁻ : ∀ {a} {A : Set a} xs → {ys : List A} {v : A} → v ∈ xs ++ ys → v ∈ xs ⊎ v ∈ ys
∈-++⁻ []       k       = inj₂ k
∈-++⁻ (x ∷ xs) here    = inj₁ here
∈-++⁻ (x ∷ xs) (there k) = case (∈-++⁻ xs k) of λ {
  (inj₁ k′) → inj₁ (there k′) ;
  (inj₂ k′) → inj₂ k′ }

++-∈-absorb : ∀ {ℓ} {A : Set ℓ} {a : A} {R L : List A} → a ∈ (L ++ R) ++ R → a ∈ L ++ R
++-∈-absorb {R = R} {L = L} a∈LR = case ∈-++⁻ (L ++ R) a∈LR of λ {
  (inj₁ x) → x;
  (inj₂ x) → ∈-++⁺ʳ L x }
