{-# OPTIONS --rewriting #-}

module Types where

open import Prelude
open import Base

----------------------------------------------------
-- global types

data GType : (ℝ : Roles) → Set where
  _⇒⟨_⟩_ : ∀ {R S} → GType R → (ρ : List Role) → GType S → GType ((R ++ ρ) ++ S)
  _⊛_ : ∀ {R S} → GType R → GType S → GType (R ++ S)
  _⊕_ : ∀ {R S} → GType R → GType S → GType (R ++ S)
  ◎＠ : (r : Role) → GType [ r ]


----------------------------------------------------
-- local types

data LType : Set where
  _⟶_ : LType  → LType  → LType
  _⋆_ : LType  → LType  → LType
  _＋_ : LType  → LType  → LType
  ○ : LType
  ∅ : LType
  
