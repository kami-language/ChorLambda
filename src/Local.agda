
module Local where

open import Data.Product using (_×_)
open import Data.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×-dec_)
open import Relation.Nullary.Negation using (¬_) renaming (contradiction to _↯_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Base
open import Utils

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
  var : (v : Var) -> LValue R
  Λ : (x : Var) -> (T : LType) -> (B : Behaviour R) -> LValue R -- lambda abstraction
  Inl : (v : LValue R) → LValue R -- sum ctor
  Inr : (v : LValue R) → LValue R -- sum ctor
  fst : LValue R -- pair destructor
  snd : LValue R  -- pair destructor
  Pair : (a : LValue R) → (b : LValue R) → LValue R
  O : LValue R -- unit value at role r
  send : (r : Role R) → LValue R -- send value to role r
  recv : (r : Role R) → LValue R -- receive value from role r
  ⊥ : LValue R

data Behaviour R where
  V : (v : LValue R) -> Behaviour R
  _∙_ : (B : Behaviour R) -> (B′ : Behaviour R) -> Behaviour R -- application
  case : (B : Behaviour R) -> (N : (Var × Behaviour R)) -> (N′ : (Var × Behaviour R)) -> Behaviour R -- sum destructor
  ⊕ : (r : Role R) -> (l : Label) -> (B : Behaviour R) -> Behaviour R -- choose 
  & : (r : Role R) → (Ls : List (Label × Behaviour R)) -> Behaviour R -- offer role r options for how to continue

_＝ₜ_ : (T T′ : LType) → Dec (T ≡ T′)
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

{-
_＝lv_ : ∀ {Θ} → (v v′ : LValue Θ) → Dec (v ≡ v′)
var x ＝lv var x₁ with (x == x₁)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
var x ＝lv Λ x₁ x₂ x₃ = no (λ ())
var x ＝lv Inl v′ = no (λ ())
var x ＝lv Inr v′ = no (λ ())
var x ＝lv fst = no (λ ())
var x ＝lv snd = no (λ ())
var x ＝lv Pair v′ v′₁ = no (λ ())
var x ＝lv O = no (λ ())
var x ＝lv send x₁ = no (λ ())
var x ＝lv recv x₁ = no (λ ())
var x ＝lv ⊥ = no (λ ())
Λ x x₁ x₂ ＝lv var x₃ = no (λ ())
Λ x x₁ x₂ ＝lv Λ x₃ x₄ x₅ = {!!}
Λ x x₁ x₂ ＝lv Inl v′ = no (λ ())
Λ x x₁ x₂ ＝lv Inr v′ = no (λ ())
Λ x x₁ x₂ ＝lv fst = no (λ ())
Λ x x₁ x₂ ＝lv snd = no (λ ())
Λ x x₁ x₂ ＝lv Pair v′ v′₁ = no (λ ())
Λ x x₁ x₂ ＝lv O = no (λ ())
Λ x x₁ x₂ ＝lv send x₃ = no (λ ())
Λ x x₁ x₂ ＝lv recv x₃ = no (λ ())
Λ x x₁ x₂ ＝lv ⊥ = no (λ ())
Inl v ＝lv var x = no (λ ())
Inl v ＝lv Λ x x₁ x₂ = no (λ ())
Inl v ＝lv Inl v′ with (v ＝lv v′)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
Inl v ＝lv Inr v′ = no (λ ())
Inl v ＝lv fst = no (λ ())
Inl v ＝lv snd = no (λ ())
Inl v ＝lv Pair v′ v′₁ = no (λ ())
Inl v ＝lv O = no (λ ())
Inl v ＝lv send x = no (λ ())
Inl v ＝lv recv x = no (λ ())
Inl v ＝lv ⊥ = no (λ ())
Inr v ＝lv var x = no (λ ())
Inr v ＝lv Λ x x₁ x₂ = no (λ ())
Inr v ＝lv Inl v′ = no (λ ())
Inr v ＝lv Inr v′ with (v ＝lv v′)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
Inr v ＝lv fst = no (λ ())
Inr v ＝lv snd = no (λ ())
Inr v ＝lv Pair v′ v′₁ = no (λ ())
Inr v ＝lv O = no (λ ())
Inr v ＝lv send x = no (λ ())
Inr v ＝lv recv x = no (λ ())
Inr v ＝lv ⊥ = no (λ ())
fst ＝lv var x = no (λ ())
fst ＝lv Λ x x₁ x₂ = no (λ ())
fst ＝lv Inl v′ = no (λ ())
fst ＝lv Inr v′ = no (λ ())
fst ＝lv fst = yes refl
fst ＝lv snd = no (λ ())
fst ＝lv Pair v′ v′₁ = no (λ ())
fst ＝lv O = no (λ ())
fst ＝lv send x = no (λ ())
fst ＝lv recv x = no (λ ())
fst ＝lv ⊥ = no (λ ())
snd ＝lv var x = no (λ ())
snd ＝lv Λ x x₁ x₂ = no (λ ())
snd ＝lv Inl v′ = no (λ ())
snd ＝lv Inr v′ = no (λ ())
snd ＝lv fst = no (λ ())
snd ＝lv snd = yes refl
snd ＝lv Pair v′ v′₁ = no (λ ())
snd ＝lv O = no (λ ())
snd ＝lv send x = no (λ ())
snd ＝lv recv x = no (λ ())
snd ＝lv ⊥ = no (λ ())
Pair v v₁ ＝lv var x = no (λ ())
Pair v v₁ ＝lv Λ x x₁ x₂ = no (λ ())
Pair v v₁ ＝lv Inl v′ = no (λ ())
Pair v v₁ ＝lv Inr v′ = no (λ ())
Pair v v₁ ＝lv fst = no (λ ())
Pair v v₁ ＝lv snd = no (λ ())
Pair v v₁ ＝lv Pair v′ v′₁ = {!!}
Pair v v₁ ＝lv O = no (λ ())
Pair v v₁ ＝lv send x = no (λ ())
Pair v v₁ ＝lv recv x = no (λ ())
Pair v v₁ ＝lv ⊥ = no (λ ())
O ＝lv var x = no (λ ())
O ＝lv Λ x x₁ x₂ = no (λ ())
O ＝lv Inl v′ = no (λ ())
O ＝lv Inr v′ = no (λ ())
O ＝lv fst = no (λ ())
O ＝lv snd = no (λ ())
O ＝lv Pair v′ v′₁ = no (λ ())
O ＝lv O = yes refl
O ＝lv send x = no (λ ())
O ＝lv recv x = no (λ ())
O ＝lv ⊥ = no (λ ())
send x ＝lv var x₁ = no (λ ())
send x ＝lv Λ x₁ x₂ x₃ = no (λ ())
send x ＝lv Inl v′ = no (λ ())
send x ＝lv Inr v′ = no (λ ())
send x ＝lv fst = no (λ ())
send x ＝lv snd = no (λ ())
send x ＝lv Pair v′ v′₁ = no (λ ())
send x ＝lv O = no (λ ())
send x ＝lv send x₁ with (x == x₁)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
send x ＝lv recv x₁ = no (λ ())
send x ＝lv ⊥ = no (λ ())
recv x ＝lv var x₁ = no (λ ())
recv x ＝lv Λ x₁ x₂ x₃ = no (λ ())
recv x ＝lv Inl v′ = no (λ ())
recv x ＝lv Inr v′ = no (λ ())
recv x ＝lv fst = no (λ ())
recv x ＝lv snd = no (λ ())
recv x ＝lv Pair v′ v′₁ = no (λ ())
recv x ＝lv O = no (λ ())
recv x ＝lv send x₁ = no (λ ())
recv x ＝lv recv x₁ with (x == x₁)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
recv x ＝lv ⊥ = no (λ ())
⊥ ＝lv var x = no (λ ())
⊥ ＝lv Λ x x₁ x₂ = no (λ ())
⊥ ＝lv Inl v′ = no (λ ())
⊥ ＝lv Inr v′ = no (λ ())
⊥ ＝lv fst = no (λ ())
⊥ ＝lv snd = no (λ ())
⊥ ＝lv Pair v′ v′₁ = no (λ ())
⊥ ＝lv O = no (λ ())
⊥ ＝lv send x = no (λ ())
⊥ ＝lv recv x = no (λ ())
⊥ ＝lv ⊥ = yes refl


_＝b_ : ∀ {Θ} → (B B′ : Behaviour Θ) → Dec (B ≡ B′)
V x ＝b V x₁ with (x ＝lv x₁)
... | yes refl = yes refl
... | no ¬a = no λ { refl → refl ↯ ¬a }
V x ＝b (B′ ∙ B′₁) = no (λ ())
V x ＝b case B′ x₁ x₂ = no (λ ())
V x ＝b ⊕ x₁ x₂ B′ = no (λ ())
V x ＝b & x₁ x₂ = no (λ ())
(B ∙ B₁) ＝b V x = no (λ ())
(B ∙ B₁) ＝b (B′ ∙ B′₁) with B ＝b B′ | B₁ ＝b B′₁
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no λ { refl → refl ↯ ¬q }
... | no ¬p | _ = no λ { refl → refl ↯ ¬p }
(B ∙ B₁) ＝b case B′ x x₁ = no (λ ())
(B ∙ B₁) ＝b ⊕ x x₁ B′ = no (λ ())
(B ∙ B₁) ＝b & x x₁ = no (λ ())
case B x x₁ ＝b V x₂ = no (λ ())
case B x x₁ ＝b (B′ ∙ B′₁) = no (λ ())
case B x x₁ ＝b case B′ x₂ x₃ = {!!}
case B x x₁ ＝b ⊕ x₂ x₃ B′ = no (λ ())
case B x x₁ ＝b & x₂ x₃ = no (λ ())
⊕ x x₁ B ＝b V x₂ = no (λ ())
⊕ x x₁ B ＝b (B′ ∙ B′₁) = no (λ ())
⊕ x x₁ B ＝b case B′ x₂ x₃ = no (λ ())
⊕ x x₁ B ＝b ⊕ x₂ x₃ B′ = {!!}
⊕ x x₁ B ＝b & x₂ x₃ = no (λ ())
& x x₁ ＝b V x₂ = no (λ ())
& x x₁ ＝b (B′ ∙ B′₁) = no (λ ())
& x x₁ ＝b case B′ x₂ x₃ = no (λ ())
& x x₁ ＝b ⊕ x₂ x₃ B′ = no (λ ())
& x x₁ ＝b & x₂ x₃ = {!!}
-}
