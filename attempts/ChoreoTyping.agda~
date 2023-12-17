module ChoreoTyping where

open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Permutation using (Permutation′; _⟨$⟩ʳ_; transpose ; id; insert)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; zero; suc)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Maybe using (_>>=_)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup) renaming ([_] to ⟨_⟩)
open import Data.String using (String)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Agda.Builtin.Bool using (true; false)

open import Base
open import Global


----------------------------------------------------
-- role renaming

record Injection (M N : Nat) : Set where
  field
    inj : Fin M → Fin N
    distinct : ∀{n₁ n₂ : Fin M} → ((inj n₁) ≡ (inj n₂)) → (n₁ ≡ n₂)

open Injection

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

-- role renaming
_⟦_⟧ : {R Θ : Roles} → Type R → (Injection R Θ) → Type Θ
_⟦_⟧ T rename = mapRoles T (inj rename)

-- embed a single role type by giving its role the given name
embed : ∀{Θ} → Type 1 → Role Θ → Type Θ
embed = λ T n → T ⟦ (fromVec ⟨ n ⟩ (rest empty empty)) ⟧


----------------------------------------------------
-- contexts

data TypingStmt : Roles → Set where
  _⦂_ : ∀{Θ} → Var → Type Θ → TypingStmt Θ

TCtx : Roles → Set
TCtx Θ = List (TypingStmt Θ)


----------------------------------------------------
-- typing rules
-- we only have the Γ context from the paper.
-- role context Θ moved into the dependent type
-- type definitions context Σ is omitted for now, we use builtins instead

data _⊢_⦂_ {Θ} (Γ : TCtx Θ) : Choreography Θ → Type Θ -> Set where

  tabs : {M : Choreography Θ} {T Tʻ : Type Θ} {x : Var}
      → (((x ⦂ T) ∷ Γ) ⊢ M ⦂ Tʻ) → (ρ : List (Role Θ))
        -------------------------------
      → (Γ ⊢ V (Λ x T M) ⦂ ⟶ ρ T Tʻ)

  tvar : {x : Var} {T : Type Θ}
      → ((x ⦂ T) ∈ Γ)
        --------------------
      → (Γ ⊢ V (var x) ⦂ T)

  tapp : ∀ {N M : Choreography Θ} {T T'} {ρ : List (Role Θ)}
      → (Γ ⊢ N ⦂ (⟶ ρ T T')) → (Γ ⊢ M ⦂ T)
        -------------------
      → (Γ ⊢ (N ∙ M) ⦂ T')

  tcase : ∀ {x x′ : Var} {C M′ M′′ : Choreography Θ} {T₁ T₂ T : Type Θ}
        → (Γ ⊢ C ⦂ (T₁ ＋ T₂)) → (((x ⦂ T₁) ∷ Γ) ⊢ M′ ⦂ T) → (((x ⦂ T₂) ∷ Γ) ⊢ M′′ ⦂ T)
        --------------------------------------
        → (Γ ⊢ case C (x , M′) (x′ , M′′) ⦂ T)

  tsel : {M : Choreography Θ} {T : Type Θ} {r s : Role Θ} {l : Label}
      →  (Γ ⊢ M ⦂ T )
      --------------------------
      → (Γ ⊢ select s r l M ⦂ T)

  tunit : ∀ {r : Role Θ}
      -------------------------
      → (Γ ⊢ V (O＠ r) ⦂ o＠ r)

  tcom : {T : Type 1} {r s : Role Θ}
      -----------------------------------------------------
      → (Γ ⊢ (V (com r s)) ⦂ ⟶ [] (embed T r) (embed T s))

  tpair : ∀ {M M′ : Value Θ} {T T′ : Type Θ}
        → (Γ ⊢ (V M) ⦂ T ) → (Γ ⊢ (V M′) ⦂ T′ )
        -------------------------------------
        → (Γ ⊢ (V (Pair M M′)) ⦂ (T mul T′))

  tproj1 : ∀ {T T′ : Type Θ}
      ----------------------------------------
        → (Γ ⊢ (V fst) ⦂ (⟶ [] (T mul T′) T))

  tproj2 : ∀ {T T′ : Type Θ}
      ------------------------------------------
        → (Γ ⊢ (V snd) ⦂ (⟶ [] (T mul T′) T′))

  tinl : ∀ {v : Value Θ} {T T′ : Type Θ}
      → (Γ ⊢ (V v) ⦂ T)
      -------------------------------
      → (Γ ⊢ (V (Inl v)) ⦂ (T ＋ T′))

  tinr : ∀ {v : Value Θ} {T T′ : Type Θ}
      → (Γ ⊢ (V v) ⦂ T′)
      -------------------------------
      → (Γ ⊢ (V (Inr v)) ⦂ (T ＋ T′))
