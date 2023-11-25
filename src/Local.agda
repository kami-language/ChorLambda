
module Local where

open import Data.Product using (_×_)
open import Data.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×-dec_)
open import Relation.Nullary.Negation using (¬_) renaming (contradiction to _↯_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import NoBijection


----------------------------------------------------
-- a language for local behaviour, to project the choreography to

-- local types
data LType : Set where
  _⟶_ : LType → LType → LType
  _＋_ : LType → LType → LType
  _mul_ : LType → LType → LType
  o : LType
  ⊥ : LType

data Behaviour (R : Roles) : Set

-- local values
data LValue (R : Roles) : Set where
  var : Var -> LValue R
  Λ : Var -> LType -> Behaviour R -> LValue R -- lambda abstraction
  Inl : LValue R → LValue R -- sum ctor
  Inr : LValue R → LValue R -- sum ctor
  fst : LValue R -- pair destructor
  snd : LValue R  -- pair destructor
  Pair : LValue R → LValue R → LValue R
  O : LValue R -- unit value at role r
  send : Role R → LValue R -- send value to role r
  recv : Role R → LValue R -- receive value from role r
  ⊥ : LValue R

data Behaviour R where
  V : LValue R -> Behaviour R
  _∙_ : Behaviour R -> Behaviour R -> Behaviour R -- application
  case : Behaviour R -> (Var × Behaviour R) -> (Var × Behaviour R) -> Behaviour R -- sum destructor
  ⊕ : Role R -> Label -> Behaviour R -> Behaviour R -- choose 
  & : Role R → List (Label × Behaviour R) -> Behaviour R -- offer role r options for how to continue

_＝ₜ_ : (T : LType) → (T′ : LType) → Dec (T ≡ T′)
(T ⟶ T₁) ＝ₜ (S ⟶ S₁) with T ＝ₜ S | T₁ ＝ₜ S₁
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no λ { refl → refl ↯ ¬q }
... | no ¬p | _ = no λ { refl → refl ↯ ¬p }
(T ⟶ T₁) ＝ₜ (S ＋ S₁) = no λ ()
(T ⟶ T₁) ＝ₜ (S mul S₁) = no λ ()
(T ⟶ T₁) ＝ₜ o = no λ ()
(T ⟶ T₁) ＝ₜ ⊥ = no λ ()
(T ＋ T₁) ＝ₜ (S ⟶ S₁) = no λ ()
(T ＋ T₁) ＝ₜ (S ＋ S₁)  with T ＝ₜ S | T₁ ＝ₜ S₁
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no λ { refl → refl ↯ ¬q }
... | no ¬p | _ = no λ { refl → refl ↯ ¬p }
(T ＋ T₁) ＝ₜ (S mul S₁) = no λ ()
(T ＋ T₁) ＝ₜ o = no λ ()
(T ＋ T₁) ＝ₜ ⊥ = no λ ()
(T mul T₁) ＝ₜ (S ⟶ S₁) = no λ ()
(T mul T₁) ＝ₜ (S ＋ S₁) = no λ ()
(T mul T₁) ＝ₜ (S mul S₁)  with T ＝ₜ S | T₁ ＝ₜ S₁
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no λ { refl → refl ↯ ¬q }
... | no ¬p | _ = no λ { refl → refl ↯ ¬p }
(T mul T₁) ＝ₜ o = no λ ()
(T mul T₁) ＝ₜ ⊥ = no λ ()
o ＝ₜ (S ⟶ S₁) = no λ ()
o ＝ₜ (S ＋ S₁) = no λ ()
o ＝ₜ (S mul S₁) = no λ ()
o ＝ₜ o = yes refl
o ＝ₜ ⊥ = no λ ()
⊥ ＝ₜ ⊥ = yes refl
⊥ ＝ₜ (S ⟶ S₁) = no λ ()
⊥ ＝ₜ (S ＋ S₁) = no λ ()
⊥ ＝ₜ (S mul S₁) = no λ ()
⊥ ＝ₜ o = no λ ()


