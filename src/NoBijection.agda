open import Data.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product
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
 ⟶ : ∀{v w} -> (u : Roles) → Type v → Type w → Type (u + v + w) -- abstraction type: R may also participate in addition to roles T and roles T'
 _＋_ : ∀{U V} -> Type U → Type V → Type (U + V) -- sum type
 _mul_ : ∀{U V} -> Type U → Type V → Type (U + V) -- product type
 _＠_ : TVar → (U : Roles) → Type U -- typevar at location TODO: really a set and not a list?
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
  _＠_⦂_ : ∀{N} → Name → (n : Fin N) → TypingStmt -- may also not be set

TCtx : Set
TCtx = List TypingStmt

data TDef : Set where
  _＠_＝_ : TVar → (R : Roles) → (T : Type R) → TDef
--  _＠_＝_ : TVar → (R : 𝒮 Role) → (T : Type) → (R ≐ (roles T)) → TDef

TRCtx : Set
TRCtx = List TDef -- really set? distinct yes but what about order

----------------------------------------------------
-- typing rules

data _⨾_⊢_⦂_ {Θ} (Σ : TRCtx) (Γ : TCtx) : Choreography → Type Θ -> Set where
 tvar : {x : Var} {T : Type Θ}
      → ((x ⦂ T) ∈ Γ)
       ----------------------------
      → (Σ ⨾ Γ ⊢ V (var x) ⦂ T)

 tapp : ∀ {N M : Choreography} {T T'} {R : Roles}
      → (Σ ⨾ Γ ⊢ N ⦂ (⟶ R T T')) → (Σ ⨾ Γ ⊢ M ⦂ T)
       ---------------------------
      → (Σ ⨾ Γ ⊢ (N ∙ M) ⦂ T')

{-}
 tdef :  {n : ℕ} {R : Roles} {T : Type R} {f : Name}
      → ((f ＠ n ⦂ T) ∈ Γ) -- → (p : (roles T) ⊆ Rʻ) → R ⊆ Θ -- → (r : (Rename Rʻ R))
       --------------------------------------
      → (Σ ⨾ Γ ⊢ (f ⦅ R ⦆) ⦂ T)
-}

 tabs : {R Rʻ ρ : Roles} {M : Choreography} {T : Type R} {Tʻ : Type Rʻ} {x : Var}
      → (Σ ⨾ (x ⦂ T) ∷ Γ ⊢ M ⦂ Tʻ)
       -------------------------------------
      → (Σ ⨾ Γ ⊢ V (Λ x T M) ⦂ ⟶ ρ T Tʻ)
{-}
 tcom : {T : Type} {r s : Role}
      → (p : (roles T) ≐  ⦃- s -⦄) → (⦃- s -⦄ ∪ ⦃- r -⦄) ⊆ Θ
      -----------------------------------------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ V (com s r) ⦂ ⟶ ⦃⦄ T (T ⟦ singleRename s r , proj₁ p ⟧))

 tsel : {M : Choreography} {T : Type} {r s : Role} {l : Label}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ T ) → (⦃- s -⦄ ∪ ⦃- r -⦄) ⊆ Θ
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ select s r l M ⦂ T)

 teq : {M : Choreography} {T : Type} {R Rʻ : 𝒮 Role} {t : TVar} {p : R ≐ (roles T)}
      →  (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (t ＠ Rʻ)) → ((t ＠ R ＝ T) p ∈ Σ) → Rʻ ⊆ Θ → (rename : Rename R Rʻ)
      -------------------------------------
      → (Θ ⨾ Σ ⨾ Γ ⊢ M ⦂ (T ⟦ rename , proj₂ p ⟧))
-}
