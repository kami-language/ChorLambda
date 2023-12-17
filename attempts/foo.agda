open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_)

data P : ℕ -> Set where
  isZero : P 0
  isOne : P 1

mycheck : ∀{m n} -> P n -> P (m + n) -> ℕ
mycheck x y = {!!}

data Q : ℕ -> Set where
  isZero : ∀{m} -> m ≡ 0 -> Q m
  isOne : ∀{m} -> m ≡ 1 -> Q m

mycheckq : ∀{m n} -> Q n -> Q (m + n) -> ℕ
mycheckq x y = {!!}
