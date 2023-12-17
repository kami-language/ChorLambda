module Base where

open import Data.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)

Var : Set
Var = String

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
