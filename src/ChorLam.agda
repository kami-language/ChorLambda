open import Data.Nat using (ℕ; zero)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.Product
open import Data.Sum
open import Data.String
open import Data.String.Properties
open import Agda.Builtin.Char
open import Level using (Level; 0ℓ; suc; _⊔_)
open import Data.Unit
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality using (_≡_)
open import Function

Var : Set
Var = String

TVar : Set
TVar = String

Role : Set
Role = String

Name : Set
Name = String

Label : Set
Label = String

----------------------------------------------------
-- Sets

data 𝒮  (A : Set) : Set where
  ⦃⦄ : 𝒮 A
  ⦃-_-⦄ : A → 𝒮 A
  _∪_ : 𝒮 A → 𝒮 A → 𝒮 A

data _∈_ {A : Set} (a : A) : (X : 𝒮 A) -> Set where
  incl : a ∈ ⦃- a -⦄
  left : ∀{X Y} -> a ∈ X -> a ∈ (X ∪ Y)
  right : ∀{X Y} -> a ∈ Y -> a ∈ (X ∪ Y)

_⊆_ : {A : Set} → 𝒮 A → 𝒮 A → Set
_⊆_ {A} s1 s2 = {a : A} → (a ∈ s1) → (a ∈ s2)

{-
refl⊆ : {A : Set} (S : 𝒮 A) → S ⊆ S
refl⊆ = λ S z → z

trans⊆ : {A : Set} {a b c : 𝒮 A} → a ⊆ b → b ⊆ c → a ⊆ c
trans⊆ = λ z z₁ z₂ → z₁ (z z₂)
-}

_≐_ : {A : Set} → 𝒮 A → 𝒮 A → Set
s1 ≐ s2 = (s1 ⊆ s2) × (s2 ⊆ s1)

{-
refl≐ : {A : Set} (S : 𝒮 A) → S ≐ S
refl≐ = λ S → (λ x → x) , (λ x → x)

trans≐ : {A : Set} {a b c : 𝒮 A} → a ≐ b → b ≐ c → a ≐ c
trans≐ = λ x x₁ → (λ z → proj₁ x₁ (proj₁ x z)) , (λ z → proj₂ x (proj₂ x₁ z))
-}

-- "instantiate" a specific set
ins : {A : Set} → 𝒮 A -> Set
ins {A} S = Σ A (_∈ S)

𝒮map : ∀ {A B : Set} → (A → B) → 𝒮 A → 𝒮 B
𝒮map f ⦃⦄ = ⦃⦄
𝒮map f ⦃- x -⦄  = ⦃- (f x) -⦄
𝒮map f (a ∪ b) = (𝒮map f a) ∪ (𝒮map f b)

----------------------------------------------------
-- language

data Type : Set where
 ⟶ : 𝒮 Role → Type → Type → Type -- abstraction type: R may also participate in addition to roles T and roles T'
 _＋_ : Type → Type → Type -- sum type
 _mul_ : Type → Type → Type -- product type
 _＠_ : TVar → 𝒮 Role → Type -- typevar at location TODO: really a set and not a list?
 o＠ : Role → Type -- unit type at role R

data Choreography : Set

data Value : Set where
 var : Var -> Value
 Λ : Var -> Type -> Choreography -> Value -- lambda abstraction
 Inl : Value → Value -- sum ctor
 Inr : Value → Value -- sum ctor
 fst : Value -- pair destructor
 snd : Value  -- pair destructor
 Pair : Value → Value → Value
 O＠ : Role → Value -- unit value at role R
 com : Role → Role → Value -- communicate: take value at role R and return it at role S

data Choreography where
 V : Value -> Choreography
 _⦅_⦆ : Name -> 𝒮 Role -> Choreography -- evaluate to choreo f instantiated with roles R
 _∙_ : Choreography -> Choreography -> Choreography -- application
 case : Choreography -> (Var × Choreography) -> (Var × Choreography) -> Choreography -- sum destructor
 select : Role -> Role -> Label -> Choreography -> Choreography -- S informs R it has selected l then continues with M

----------------------------------------------------
-- roles extraction

roles : Type → 𝒮 Role 
roles (⟶ x₁ t t₁) = x₁ ∪ (roles t ∪ roles t₁)
roles (t ＋ t₁) = roles t ∪ roles t₁
roles (t mul t₁) = roles t ∪ roles t₁
roles (t ＠ r) = r
roles (o＠ r) = ⦃- r -⦄

----------------------------------------------------
-- role renaming


record Biject (A B : Set) : Set where
 field
  f : A → B
  g : B → A

  one : (b : B) → ((f ∘ g) b) ≡ b
  two : (a : A) → ((g ∘ f) a) ≡ a

open Biject

Rename : (R Rʻ : 𝒮 Role) → Set
Rename R Rʻ =  Biject (ins R) (ins Rʻ)

singleRename : (r : Role) → (s : Role) → Rename ⦃- r -⦄ ⦃- s -⦄
singleRename r s = record { f = λ x → (s , incl) ;
                            g = λ x → (r , incl) ;
                            one = λ { (s , incl) → _≡_.refl } ;
                            two = λ { (r , incl) → _≡_.refl }
                          }

choiceset : {A : Set} → (S : 𝒮 A) → 𝒮 (Σ A (_∈ S))
choiceset ⦃⦄ = ⦃⦄
choiceset ⦃- x -⦄ = ⦃- x , incl -⦄
choiceset (S ∪ S₁) = (𝒮map (λ (x , p) → x , left p) (choiceset S)) ∪ (𝒮map (λ (x , p) → x , right p) (choiceset S₁))

-- actually do the renaming
_⟦_,_⟧ : {R Rʻ : 𝒮 Role} → (T : Type) → (rename : Rename R Rʻ) → roles T ⊆ R → Type
⟶ X T T₁ ⟦ r , p ⟧ = ⟶ (𝒮map (λ (x , xinX) → proj₁ (f r (x , (λ z → p (left z)) xinX))) (choiceset X)) (T ⟦ r , (λ z → p (right (left z))) ⟧) (T₁ ⟦ r , (λ z → p (right (right z))) ⟧)
(T ＋ T₁) ⟦ r , p ⟧ = ((T ⟦ r , (λ z → p (left z)) ⟧) ＋ (T₁ ⟦ r , (λ z → p (right z)) ⟧))
(T mul T₁) ⟦ r , p ⟧ = (T ⟦ r , (λ z → p (left z)) ⟧) mul (T₁ ⟦ r , (λ z → p (right z)) ⟧)
(x ＠ x₁) ⟦ r , p ⟧ = x ＠ x₁
o＠ x ⟦ r , p ⟧ = o＠ (proj₁ (f r (x , p incl)))

----------------------------------------------------
-- contexts

RCtx : Set
RCtx = 𝒮 Role

data TypingStmt : Set where
  _⦂_ : Var → Type → TypingStmt
  _＠_⦂_ : Name → 𝒮 Role → Type → TypingStmt -- may also not be set

TCtx : Set
TCtx = 𝒮 TypingStmt

data TDef : Set where
  _＠_＝_ : TVar → (R : 𝒮 Role) → (T : Type) → (R ≐ (roles T)) → TDef

TRCtx : Set
TRCtx = 𝒮 TDef -- really set? distinct yes but what about order

----------------------------------------------------
-- typing rules

data _⨾_⨾_⊢_⦂_ : RCtx -> TRCtx -> TCtx -> Choreography → Type -> Set where
 tvar : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {x : Var} {T : Type}
      → ((x ⦂ T) ∈ Γ) → (roles T) ⊆ Θ
       ----------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ V (var x) ⦂ T)

 tapp : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {N M : Choreography} {T T' : Type} {R : 𝒮 Role}
      → (Θ ⨾ Σ ⨾ Γ ⊢ N ⦂ (⟶ R T T')) → (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ T)
       ---------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ (N ∙ M) ⦂ T')

 tdef : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {T : Type} {R Rʻ : 𝒮 Role} {f : Name}
      → ((f ＠ Rʻ ⦂ T) ∈ Γ) → (p : (roles T) ⊆ Rʻ) → R ⊆ Θ → (r : (Rename Rʻ R))
       --------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ f ⦅ R ⦆ ⦂ (T ⟦ r , p ⟧))
 
 tabs : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {M : Choreography} {T Tʻ : Type} {x : Var} {R : 𝒮 Role}
      → ((R ∪ (roles T ∪ roles Tʻ)) ⨾ Σ ⨾ (Γ ∪ ⦃- x ⦂ T -⦄) ⊢ M ⦂ Tʻ) → (R ∪ (roles T ∪ roles Tʻ)) ⊆ Θ
       -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ V (Λ x T M) ⦂ ⟶ R T Tʻ)

 tcom : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {T : Type} {r s : Role}
      → (p : (roles T) ≐  ⦃- s -⦄) → (⦃- s -⦄ ∪ ⦃- r -⦄) ⊆ Θ
      -----------------------------------------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ V (com s r) ⦂ ⟶ ⦃⦄ T (T ⟦ singleRename s r , proj₁ p ⟧))

 tsel : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {M : Choreography} {T : Type} {r s : Role} {l : Label}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ T ) → (⦃- s -⦄ ∪ ⦃- r -⦄) ⊆ Θ
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ select s r l M ⦂ T)

 teq : {Θ : RCtx} {Σ : TRCtx} {Γ : TCtx} {M : Choreography} {T : Type} {R Rʻ : 𝒮 Role} {t : TVar} {p : R ≐ (roles T)}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (t ＠ Rʻ)) → ((t ＠ R ＝ T) p ∈ Σ) → Rʻ ⊆ Θ → (rename : Rename R Rʻ)
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (T ⟦ rename , proj₂ p ⟧))


{-
myName : String
myName = primShowChar (primNatToChar zero)

varterm : (r : Role) → ｛ r ｝ ⨾ ∅ ⨾ ｛ myName ⦂ (o＠ r) ｝ ⊢ (V (var myName)) ⦂ (o＠ r)
varterm r = tvar _≡_.refl (λ x → x)

data _∈_ : ∀ {A : Set} → A → List A → Set where
 top : ∀ {A as} {a : A} → a ∈ (a ∷ as)
 pop : ∀ {A as b} {a : A} → a ∈ as → a ∈ (b ∷ as)

emptyempty : ∀ {A : Set} {a : A} → ¬(a ∈ [])
emptyempty = λ ()

_⊆_ : {A : Set} → List A → List A → Set
as ⊆ bs = ∀ {a} → (a u∈ as) → (a ∈ bs)

refl⊆ : {A : Set} (L : List A) → L ⊆ L
refl⊆ = λ L z → z 

trans⊆ : {A : Set} {a b c : List A} → a ⊆ b → b ⊆ c → a ⊆ c
trans⊆ = λ z z₁ z₂ → z₁ (z z₂) 

data _⊆_ {A : Set} : List A → List A → Set where
  empty : {L : List A} → [] ⊆ L
  left : {a : A} {L LL : List A} → a ∈ LL → L ⊆ LL → (a ∷ L) ⊆ LL

⊆prop1 : ∀ {A : Set} (as bs : List A) → (∀ {a} → (a ∈ as) → (a ∈ bs)) → as ⊆ bs 
⊆prop1 [] bs x = empty
⊆prop1 (x₁ ∷ as) bs x = left (x top) (⊆prop1 as bs (λ z → x (pop z)))

⊆prop : ∀ {A : Set} {as bs : List A} {a : A} → as ⊆ bs → (a ∈ as) → (a ∈ bs)
⊆prop (left x x₂) top = x
⊆prop (left x x₂) (pop x₁) = ⊆prop x₂ x₁

refl⊆ : {A : Set} (L : List A) → L ⊆ L
refl⊆ = λ L → ⊆prop1 L L (λ x → x)

trans⊆ : {A : Set} (a b c : List A) → a ⊆ b → b ⊆ c → a ⊆ c
trans⊆ = λ a b c x x₁ → ⊆prop1 a c (⊆prop x₁ ∘ ⊆prop x)
-}


{-
data ⊥ : Set where

data _In_  {A : Set} : A → List A → Set where
  top : ∀ {a l} → a In (a ∷ l) 
  pop : ∀ {a b l} → a In l → a In (b ∷ l)

data Sset (A : Set) : Set where
 empty : Sset A
 singleton : A → Sset A
 ⋃ : List (Sset A) → Sset A

_∪_ : {A : Set} -> Sset A → Sset A → Sset A
empty ∪ s = s
s ∪ empty = s
(singleton a) ∪ (singleton b) = ⋃ ((singleton a) ∷ [(singleton b)])
(singleton a) ∪ ⋃ s1 = ⋃ ((singleton a) ∷ s1)
⋃ s1 ∪ (singleton a) = ⋃ ((singleton a) ∷ s1)
⋃ s1 ∪ ⋃ s2 = ⋃ (s1 ++ s2)

data Sort : Set where
 unit : Sort
 nat : Sort
 int : Sort
 bool : Sort
 _+_ : Sort → Sort → Sort
 _*_ : Sort → Sort → Sort

data HybridType : Set where
 end : HybridType
 X : HybridType
 _∥_ : HybridType → HybridType → HybridType
 μ : TVar -> HybridType -> HybridType
 ! : Role → Role → List (Label × Sort × HybridType) → HybridType
 ？ : Role → Role → List (Label × Sort × HybridType) → HybridType
 ⟶ : Role →  Role → List (Label × Sort × HybridType) → HybridType

{-# TERMINATING #-}
epart : HybridType → Sset Role
epart end = empty
epart X = empty
epart (x ∥ x₁) = (epart x) ∪ (epart x₁)
epart (μ x x₁) = epart x₁
epart (! p q hs) = (singleton p) ∪ (⋃ (map (λ {(_ , _ , h) → (epart h)}) hs))
epart (？ p q hs) = (singleton q) ∪ (⋃ (map (λ {(_ , _ , h) → (epart h)}) hs))
epart (⟶ p q hs) = ((singleton q) ∪ (singleton p)) ∪ (⋃ (map (λ {(_ , _ , h) → (epart h)}) hs))

{-# TERMINATING #-}
ipart : HybridType → Sset Role
ipart end = empty
ipart X = empty
ipart (x ∥ x₁) = (ipart x) ∪ (ipart x₁)
ipart (μ x x₁) = ipart x₁
ipart (! p q hs) = (singleton p) ∪ (⋃ (map (λ {(_ , _ , h) → (ipart h)}) hs))
ipart (？ p q hs) = (singleton q) ∪ (⋃ (map (λ {(_ , _ , h) → (ipart h)}) hs))
ipart (⟶ p q hs) = ((singleton q) ∪ (singleton p)) ∪ (⋃ (map (λ {(_ , _ , h) → (ipart h)}) hs))

data _∈_ : {A : Set} -> A -> (Sset A) -> Set1 where
 singletonC : {A : Set} (a : A) -> (a ∈ (singleton a))
 uuC : {A : Set} (a : A) (s1 : List (Sset A)) (s : Sset A) (i : s In s1) -> a ∈ s -> a ∈ (⋃ s1)

data disjoint : {A : Set} -> (Sset A) -> (Sset A) -> Set1 where
 emptyD : {A : Set} -> (a : Sset A) → disjoint empty a
 inD : {A : Set} (a : A) (s1 s2 : Sset A) (i : a ∈ s1) -> (j : ¬ (a ∈ s2)) -> (disjoint s1 s2)

disjointPart : ∀ (h : HybridType) → disjoint (ipart h) (epart h)
disjointPart end = emptyD empty
disjointPart X = emptyD empty
disjointPart (h ∥ h₁) = {!!}
disjointPart (μ x h) = disjointPart h
disjointPart (! p q hs) = {!!}
disjointPart (？ p q hs) = {!!}
disjointPart (⟶ x x₁ x₂) = {!!}
-}
