module Global where

open import Data.List using (List; map)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)

open import Base

----------------------------------------------------
-- language for choreographies

-- a type is parametrized by the maximal number of different roles it uses
data Type : Roles -> Set where
  ⟶ : ∀ {U} → List (Role U) → Type U → Type U → Type U -- abstraction type: R may also participate in addition to roles T and roles T'
  _＋_ : ∀ {U} -> Type U → Type U → Type U -- sum type
  _mul_ : ∀ {U} → Type U → Type U → Type U -- product type
  o＠ : ∀ {r} → (Fin r) → Type r -- unit type at role r

-- map over the roles of a type
mapRoles : {R Θ : Roles} → Type R → (Fin R → Fin Θ) → Type Θ
mapRoles (⟶ x T T₁) f = ⟶ (map f x) (mapRoles T f) (mapRoles T₁ f)
mapRoles (T ＋ T₁) f = (mapRoles T f) ＋ mapRoles T₁ f
mapRoles (T mul T₁) f = (mapRoles T f) mul (mapRoles T₁ f)
mapRoles (o＠ r) f = o＠ (f r)

data Choreography (R : Roles) : Set

data Value (R : Roles) : Set where
  var : Var -> Value R
  Λ : Var -> Type R -> Choreography R -> Value R -- lambda abstraction
  Inl : Value R → Value R -- sum ctor
  Inr : Value R → Value R -- sum ctor
  fst : Value R -- pair destructor
  snd : Value R -- pair destructor
  Pair : Value R → Value R → Value R
  O＠ : Role R → Value R -- unit value at role R
  com : Role R → Role R → Value R -- communicate: take value at role R and return it at role S

data Choreography R where
  V : Value R -> Choreography R
--  _⦅_⦆ : ∀{Θ} → Name -> List (Role Θ) -> Choreography R -- evaluate to choreo f instantiated with roles R
  _∙_ : Choreography R -> Choreography R -> Choreography R -- application
  case : Choreography R -> (Var × Choreography R) -> (Var × Choreography R) -> Choreography R -- sum destructor
  select : Role R -> Role R -> Label -> Choreography R -> Choreography R -- S informs R it has selected l then continues with M
