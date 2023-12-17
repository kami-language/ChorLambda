module Global where

open import Data.List using (List; map)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)

open import Base

----------------------------------------------------
-- language for choreographies

-- a type is parametrized by the maximal number of different roles it uses
data Type (R : Roles) : Set where
  ⟶ :  (ρ : List (Role R)) → Type R → Type R → Type R -- abstraction type: R may also participate in addition to roles T and roles T'
  _＋_ : Type R → Type R → Type R -- sum type
  _mul_ : Type R → Type R → Type R -- product type
  o＠ : (r : (Fin R)) → Type R -- unit type at role r

-- map over the roles of a type
mapRoles : {R Θ : Roles} → Type R → (Fin R → Fin Θ) → Type Θ
mapRoles (⟶ x T T₁) f = ⟶ (map f x) (mapRoles T f) (mapRoles T₁ f)
mapRoles (T ＋ T₁) f = (mapRoles T f) ＋ mapRoles T₁ f
mapRoles (T mul T₁) f = (mapRoles T f) mul (mapRoles T₁ f)
mapRoles (o＠ r) f = o＠ (f r)

data Choreography (R : Roles) : Set

data Value (R : Roles) : Set where
  var : (v : Var) → Value R
  Λ : (x : Var) → (T : Type R) → (M : Choreography R) → Value R -- lambda abstraction
  Inl : (v : Value R) → Value R -- sum ctor
  Inr : (v : Value R) → Value R -- sum ctor
  fst : Value R -- pair destructor
  snd : Value R -- pair destructor
  Pair : (a : Value R) → (b : Value R) → Value R
  O＠ : (r : Role R) → Value R -- unit value at role R
  com : (r : Role R) → (s : Role R) → Value R -- communicate: take value at role R and return it at role S

data Choreography R where
  V : (v : Value R) → Choreography R
--  _⦅_⦆ : ∀{Θ} → Name → List (Role Θ) → Choreography R -- evaluate to choreo f instantiated with roles R
  _∙_ : (M : Choreography R) → (N : Choreography R) → Choreography R -- application
  case : (M : Choreography R) → (N : Var × Choreography R) → (N′ : Var × Choreography R) → Choreography R -- sum destructor
  select : (r : Role R) → (s : Role R) → (l : Label) → (M : Choreography R) → Choreography R -- S informs R it has selected l then continues with M
