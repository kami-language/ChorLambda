{-# OPTIONS --rewriting #-}

module Base where

open import Prelude

-- labels are just numbers for now
Label : Set
Label = Nat

-- "sets" of role indices are represented by their size
Role : Set
Role = Nat

-- individual roles are indexed from a finite set
Roles : Set
Roles = List Role
