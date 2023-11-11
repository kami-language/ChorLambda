open import Data.Fin using (Fin; #_)
open import Data.Fin.Permutation using (Permutation′; _⟨$⟩ʳ_; transpose ; id; insert)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; zero; suc)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.String using (String)
open import Agda.Builtin.Equality using (_≡_)

Var : Set
Var = String

TVar : Set
TVar = String

Name : Set
Name = String

Label : Set
Label = String

----------------------------------------------------
-- language

-- "sets" of role indices are represented by their size
Roles : Set
Roles = Nat

-- individual roles are indexed from a finite set
Role : Nat → Set
Role = Fin

-- a type is parametrized by the maximal number of different roles it uses
data Type : Roles -> Set where
 ⟶ : ∀{U} → List (Role U) → Type U → Type U → Type U -- abstraction type: R may also participate in addition to roles T and roles T'
 _＋_ : ∀{U} -> Type U → Type U → Type U -- sum type
 _mul_ : ∀{U} → Type U → Type U → Type U -- product type
 _＠_ : ∀{U} → TVar → (R : List (Role U)) → Type U -- typevar at location TODO: really a set and not a list?
 o＠ : ∀{r} → (Fin r) → Type r -- unit type at role r


{-}
data Type : Set where
 ⟶ : 𝒮 Role → Type → Type → Type -- abstraction type: R may also participate in addition to roles T and roles T'
 _＋_ : Type → Type → Type -- sum type
 _mul_ : Type → Type → Type -- product type
 _＠_ : TVar → 𝒮 Role → Type -- typevar at location TODO: really a set and not a list?
 o＠ : Role → Type -- unit type at role R
-}

data Choreography : Set

data Value : Set where
 var : Var -> Value
 Λ : Var -> {R : Roles} → Type R -> Choreography -> Value -- lambda abstraction
 Inl : Value → Value -- sum ctor
 Inr : Value → Value -- sum ctor
 fst : Value -- pair destructor
 snd : Value  -- pair destructor
 Pair : Value → Value → Value
 O＠ : ∀{r} Role r → Value -- unit value at role R
 com : ∀{r s} Role r → Role s → Value -- communicate: take value at role R and return it at role S

data Choreography where
 V : Value -> Choreography
 _⦅_⦆ : Name -> Roles -> Choreography -- evaluate to choreo f instantiated with roles R
 _∙_ : Choreography -> Choreography -> Choreography -- application
 case : Choreography -> (Var × Choreography) -> (Var × Choreography) -> Choreography -- sum destructor
 select : ∀{r s} Role r -> Role s -> Label -> Choreography -> Choreography -- S informs R it has selected l then continues with M

----------------------------------------------------
-- contexts

RCtx : Set
RCtx = Roles

data TypingStmt : Set where
  _⦂_ : ∀{Θ} → Var → Type Θ → TypingStmt
  _＠⦂_ : ∀{Θ} Name → Type Θ → TypingStmt -- may also not be set

TCtx : Set
TCtx = List TypingStmt

data TDef : Set where
  _＠_＝_ : TVar → (R : Roles) → (T : Type R) → TDef
--  _＠_＝_ : TVar → (R : 𝒮 Role) → (T : Type) → (R ≐ (roles T)) → TDef

TRCtx : Set
TRCtx = List TDef 


_⟦_⟧ : {Θ : Roles} → Type Θ → (Permutation′ Θ) → Type Θ
⟶ Θ x x₁ ⟦ rename ⟧ = ⟶ Θ (x ⟦ rename ⟧) (x₁ ⟦ rename ⟧)
(x ＋ x₁) ⟦ rename ⟧ = (x ⟦ rename ⟧) ＋ (x₁ ⟦ rename ⟧)
(x mul x₁) ⟦ rename ⟧ = (x ⟦ rename ⟧) mul (x₁ ⟦ rename ⟧)
(x ＠ Θ) ⟦ rename ⟧ = x ＠ (map (λ y → rename ⟨$⟩ʳ y) Θ)
o＠ x ⟦ rename ⟧ = o＠ (rename ⟨$⟩ʳ x)

data singleRole : {Θ : Roles} → Type Θ → Set where

getSingle : ∀{Θ} → (T : Type Θ) → singleRole T → Role Θ
getSingle = {!!}

----------------------------------------------------
-- typing rules

data _⨾_⊢_⦂_ {Θ} (Σ : TRCtx) (Γ : TCtx) : Choreography → Type Θ -> Set where
 tvar : {x : Var} {T : Type Θ}
      → ((x ⦂ T) ∈ Γ)
       ----------------------------
      → (Σ ⨾ Γ ⊢ V (var x) ⦂ T)

 tapp : ∀ {N M : Choreography} {T T'} {ρ : List (Role Θ)}
      → (Σ ⨾ Γ ⊢ N ⦂ (⟶ ρ T T')) → (Σ ⨾ Γ ⊢ M ⦂ T)
       ---------------------------
      → (Σ ⨾ Γ ⊢ (N ∙ M) ⦂ T')

 tdef :  {Θʻ : Roles} {T : Type Θ} {f : Name}
      → ((f ＠⦂ T) ∈ Γ) → (rename : Permutation′ Θ)
       --------------------------------------
      → (Σ ⨾ Γ ⊢ (f ⦅ Θ ⦆) ⦂ (T ⟦ rename ⟧))

 tabs : {M : Choreography} {T Tʻ : Type Θ} {x : Var}
      → (Σ ⨾ (x ⦂ T) ∷ Γ ⊢ M ⦂ Tʻ) → (ρ : List (Role Θ))
       -------------------------------------
      → (Σ ⨾ Γ ⊢ V (Λ x T M) ⦂ ⟶ ρ T Tʻ)

 tcom : {T : Type Θ} {r s : Role Θ}
      → (p : singleRole T)
      -----------------------------------------------------------------------
      → (Σ ⨾ Γ ⊢ (V (com {!!} (getSingle T p) s)) ⦂ ⟶ [] T (T ⟦ transpose (getSingle T p) s ⟧))
{-}
 tsel : {M : Choreography} {T : Type} {r s : Role} {l : Label}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ T ) → (⦃- s -⦄ ∪ ⦃- r -⦄) ⊆ Θ
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ select s r l M ⦂ T)

 teq : {M : Choreography} {T : Type} {R Rʻ : 𝒮 Role} {t : TVar} {p : R ≐ (roles T)}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (t ＠ Rʻ)) → ((t ＠ R ＝ T) p ∈ Σ) → Rʻ ⊆ Θ → (rename : Rename R Rʻ)
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (T ⟦ rename , proj₂ p ⟧))
-}
