
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.Fin using (Fin; #_; zero; suc)
open import Agda.Builtin.Nat using (Nat) --
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
open import Relation.Nullary using (¬_)
open import Data.Vec using (Vec; []; _∷_; lookup) renaming ([_] to ⟨_⟩) --
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Base
open import Utils

----------------------------------------------------
-- global types

-- a type is parametrized by the maximal number of different roles it uses
data IType (R : Roles) : Set where
  ⟶ :  (ρ : List (Role R)) → IType R → IType R → IType R -- abstraction type: R may also participate in addition to roles T and roles T'
  _＋_ : IType R → IType R → IType R -- sum type
  _⋆_ : IType R → IType R → IType R -- product type
  o＠ : (r : (Fin R)) → IType R -- unit type at role r


-- map over the roles of a type
mapRoles : {R Θ : Roles} → IType R → (Fin R → Fin Θ) → IType Θ
mapRoles (⟶ x T T₁) f = ⟶ (map f x) (mapRoles T f) (mapRoles T₁ f)
mapRoles (T ＋ T₁) f = (mapRoles T f) ＋ mapRoles T₁ f
mapRoles (T ⋆ T₁) f = (mapRoles T f) ⋆ (mapRoles T₁ f)
mapRoles (o＠ r) f = o＠ (f r)

----------------------------------------------------
-- roles extraction (oh if only we had strict Θ in the type...)

-- carful! duplicates!
roles : ∀ {Θ} → IType Θ → List (Role Θ)
roles (⟶ x₁ t t₁) = x₁ ++ (roles t ++ roles t₁)
roles (t ＋ t₁) = roles t ++ roles t₁
roles (t ⋆ t₁) = roles t ++ roles t₁
roles (o＠ r) = [ r ]

----------------------------------------------------
-- role renaming

record Injection (M N : Nat) : Set where
  field
    inj : Fin M → Fin N
    distinct : ∀{n₁ n₂ : Fin M} → ((inj n₁) ≡ (inj n₂)) → (n₁ ≡ n₂)

open Injection

_⟦_⟧ : {R Θ : Roles} → IType R → (Injection R Θ) → IType Θ
_⟦_⟧ T rename = mapRoles T (Injection.inj rename)

data _∉ᵥ_ {R} : ∀{N} → R → Vec R N → Set where
  empty : ∀{a} → a ∉ᵥ []
  pop : ∀{a b N} {V : Vec R N} → ¬ (a ≡ b) → a ∉ᵥ V → a ∉ᵥ (b ∷ V)

data unique {R} : ∀{N} → Vec R N → Set where
  empty : unique []
  rest : ∀{a N} {V : Vec R N} → unique V → a ∉ᵥ V → unique (a ∷ V)
  
nope : ∀{R N a n} {V : Vec R N} → unique V → a ∉ᵥ V → ¬ (a ≡ lookup V n)
nope {n = zero} uniqueV (pop p q) w =  p w
nope {n = suc n} (rest uV _) (pop p q) w = nope uV q w

unique_distinct : ∀{R N n m} {v : Vec R N} → unique v → ((lookup v n) ≡ (lookup v m)) → (n ≡ m)
unique_distinct {n = zero} {zero} (rest un x) lookup_eq = _≡_.refl
unique_distinct {n = zero} {suc m} (rest un x) lookup_eq = lookup_eq ↯ (nope un x)
unique_distinct {n = suc n} {zero} (rest un x) lookup_eq = sym lookup_eq  ↯ (nope un x)
unique_distinct {n = suc n} {suc m} (rest un x) lookup_eq = cong suc (unique_distinct un lookup_eq)

-- make an injection from a vector with unique elements
fromVec : ∀{M N} → (V : Vec (Fin N) M) → unique V → Injection M N
fromVec v un = record { inj = λ n → lookup v n ;
                        distinct =  unique_distinct un }
                        
-- embed a single role type by giving its role the given name
embed : ∀{Θ} → IType 1 → Role Θ → IType Θ
embed = λ T n → T ⟦ (fromVec ⟨ n ⟩ (rest empty empty)) ⟧

----------------------------------------------------
-- choreographies

mutual

  data _⊩ᵥ_ {Θ} (Γ : List (IType Θ)) : IType Θ -> Set where

    tabs : {T T′ : IType Θ}
         → (ρ : List (Role Θ)) → ((T ∷ Γ) ⊩ₘ T′)
           -------------------------------
         → (Γ ⊩ᵥ ⟶ ρ T T′)

    tvar : {T : IType Θ}
         → (T ∈ Γ)
           --------------------
         → (Γ ⊩ᵥ T)

    tunit : (r : Role Θ)
          -------------------------
          → (Γ ⊩ᵥ o＠ r)

    tcom : {T : IType 1} (r s : Role Θ)
        -----------------------------------------------------
        → (Γ ⊩ᵥ ⟶ [] (embed T r) (embed T s))

    tpair : ∀ {T T′ : IType Θ}
          → (Γ ⊩ᵥ T) → (Γ ⊩ᵥ T′)
          -------------------------------------
          → (Γ ⊩ᵥ (T ⋆ T′))

    tproj1 : ∀ {T T′ : IType Θ}
             ----------------------------------------
           → (Γ ⊩ᵥ (⟶ [] (T ⋆ T′) T))

    tproj2 : ∀ {T T′ : IType Θ}
        ------------------------------------------
           → (Γ ⊩ᵥ (⟶ [] (T ⋆ T′) T′))

    tinl : ∀ {T T′ : IType Θ}
        → (Γ ⊩ᵥ T)
        -------------------------------
        → (Γ ⊩ᵥ (T ＋ T′))

    tinr : ∀ {T T′ : IType Θ}
        → (Γ ⊩ᵥ T′)
        -------------------------------
        → (Γ ⊩ᵥ (T ＋ T′))

  data _⊩ₘ_ {Θ} (Γ : List (IType Θ)) : IType Θ -> Set where

    tval : ∀ {T}
        → (Γ ⊩ᵥ T)
          ------------
        → (Γ ⊩ₘ T)

    tapp : ∀ {T T'} {ρ : List (Role Θ)}
        → (Γ ⊩ₘ (⟶ ρ T T')) → (Γ ⊩ₘ T)
          -------------------
        → (Γ ⊩ₘ T')

    tsel : {T : IType Θ}
        → (Γ ⊩ₘ T ) → (r s : Role Θ) → (l : Label)
        --------------------------
        → (Γ ⊩ₘ T)

    tcase : ∀  {T₁ T₂ T : IType Θ}
          → (Γ ⊩ₘ (T₁ ＋ T₂)) → (Ts₁ : ((T₁ ∷ Γ) ⊩ₘ T)) → (Ts₂ : ((T₂ ∷ Γ) ⊩ₘ T))
          --------------------------------------
          → (Γ ⊩ₘ T)

