
module EndpointProjection where

open import Agda.Primitive using (Level; lsuc)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Permutation using (Permutation′; _⟨$⟩ʳ_; transpose ; id; insert)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; zero; suc)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Maybe using (_>>=_) renaming (map to _⟫_)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _++_; map; foldr; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup) renaming ([_] to ⟨_⟩)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟-str_)
open import Agda.Builtin.String renaming (primStringAppend to _⊹_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Relation.Nullary.Decidable using (Dec; yes; no; _because_; _×-dec_; _⊎-dec_ )
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Agda.Builtin.Bool using (true; false)

open import Base
open import Global
open import ChoreoTyping
open import Local
open import Utils

----------------------------------------------------
-- free variables

fv : ∀ {Θ} → Choreography Θ → List Var

fvv : ∀ {Θ} → Value Θ → List Var
fvv (var x) = [ x ]
fvv (Λ x T N) = (fv N) ∖ x
fvv (Inl v) = fvv v
fvv (Inr v) = fvv v
fvv fst = [] 
fvv snd = []
fvv (Pair v v₁) = (fvv v) ++ (fvv v₁)
fvv (O＠ x) = []
fvv (com x x₁) = []

fv (V x) = fvv x
fv (C ∙ C₁) = (fv C) ++ (fv C₁)
fv (case C (x , M) (y , M′)) = (fv C) ++ ((fv M) ∖ x) ++ ((fv M′) ∖ y)
fv (select x x₁ x₂ C) = fv C

-- TODO this is terrible
freshVar : (List Var) → Var
freshVar [] = " x "
freshVar (x ∷ L) = x ⊹ (freshVar L)

----------------------------------------------------
-- roles extraction (oh if only we had strict Θ in the type...)

-- carful! duplicates!
roles : ∀ {Θ} → Type Θ → List (Role Θ)
roles (⟶ x₁ t t₁) = x₁ ++ (roles t ++ roles t₁)
roles (t ＋ t₁) = roles t ++ roles t₁
roles (t mul t₁) = roles t ++ roles t₁
roles (o＠ r) = [ r ]

-- carful! duplicates!
croles : ∀ {Θ} → Choreography Θ → List (Role Θ)
croles (V (var x)) = []
croles (V (Λ x T M)) = roles T ++ croles M
croles (V (Inl x)) = croles (V x)
croles (V (Inr x)) = croles (V x)
croles (V fst) = []
croles (V snd) = []
croles (V (Pair x x₁)) = croles (V x) ++ croles (V x₁)
croles (V (O＠ x)) = [ x ]
croles (V (com x x₁)) = x ∷ x₁ ∷ []
croles (C ∙ C₁) = croles C ++ croles C₁
croles (case C (x , M) (x₁ , M₁)) = croles C ++ croles M ++ croles M₁
croles (select x x₁ x₂ C) = x ∷ x₁ ∷ croles C

----------------------------------------------------
-- merge
{-}
The check for knowledge of choice supports two principles: roles do not need to receive a
selection until their behaviour is
affected by a choice made by another role; and knowledge of choice can be propagated, in the
sense that any role that has been informed of a choice through a selection can inform other
roles as well (selections do not necessarily come from the role that has made the choice).
When projecting case M of Inl x ⇒ M ′; Inr y ⇒ M ′′, roles not occurring in M cannot know
what branch of the choreography is
chosen; therefore, the projections of M ′ and M′′ must be combined in a uniquely defined
behaviour.
-}

_⊔_ : ∀ {Θ} → Behaviour Θ → Behaviour Θ → Maybe (Behaviour Θ)

removeLabel : ∀ {Θ} → Label → List (Label × Behaviour Θ) → List (Label × Behaviour Θ)
removeLabel l [] = []
removeLabel l ((l′ , x) ∷ L) with l ≟-str l′
... | yes _ = removeLabel l L
... | no _ = (l′ , x) ∷ (removeLabel l L)

findLabel : ∀ {Θ} → Label → List (Label × Behaviour Θ) → Maybe (Behaviour Θ × (List (Label × Behaviour Θ)))
findLabel l [] = nothing
findLabel l ((l′ , x) ∷ L) with l ≟-str l′
... | yes _ = just (x , removeLabel l L)
... | no _ = findLabel l L


{-# TERMINATING #-}
mapLabels : ∀ {Θ} → List (Label × (Behaviour Θ)) → List (Label × (Behaviour Θ)) → Maybe (List (Label × (Behaviour Θ)))
mapLabels [] L′ = just L′
mapLabels L [] = just L
mapLabels ((l , x) ∷ L) L′ with findLabel l L′
... | just (x′ , L′′) = do
  xx ← x ⊔ x′
  ll ← mapLabels L L′′
  just ((l , xx) ∷ ll)
... | nothing = do
  ll ← mapLabels L L′
  just ((l , x) ∷ ll)

_⊔ᵥ_ : ∀ {θ} → LValue θ → LValue θ → Maybe (LValue θ)
(var x) ⊔ᵥ (var x′) with x ≟-str x′
...                     | yes _ = just (var x)
...                     | no _ = nothing
(Λ x T B) ⊔ᵥ (Λ x′ T′ B′) with ((x ≟-str x′) ×-dec (T ＝ₜ T′))
... | yes _ = do
  BB ← B ⊔ B′
  just (Λ x T BB)
... | no _ = nothing
(Inl x) ⊔ᵥ (Inl x′) =  Inl ⟫ (x ⊔ᵥ x′)
(Inr x) ⊔ᵥ (Inr x′) = Inr ⟫ (x ⊔ᵥ x′)
fst ⊔ᵥ fst = just fst
snd ⊔ᵥ snd = just snd
(Pair L L₁) ⊔ᵥ (Pair L′ L₁′) = do
  LL ← L ⊔ᵥ L′
  LL₁ ← L′ ⊔ᵥ L₁′
  just (Pair LL LL₁)
(send x) ⊔ᵥ (send x′) with x ≟ x′
...                     | yes _ = just (send x)
...                     | no _ = nothing
(recv x) ⊔ᵥ (recv x′) with x ≟ x′
...                     | yes _ = just (recv x)
...                     | no _ = nothing
_ ⊔ᵥ _ = nothing

V x ⊔ V x′ = V ⟫ (x ⊔ᵥ x′)
(B ∙ B₁) ⊔ (B′ ∙ B₁′) = do
  BB ← B ⊔ B′
  BB₁ ← B₁ ⊔ B₁′
  just (BB ∙ BB₁)
case B (x₁ , B₁) (x₂ , B₂) ⊔ case B′ (x₁′ , B₁′) (x₂′ , B₂′) with ((x₁ ≟-str x₁′) ×-dec (x₂ ≟-str x₂′))
... | yes _ = do
  BB ← B ⊔ B′
  BB₁ ← B₁ ⊔ B₁′
  BB₂ ← B₂ ⊔ B₂′
  just (case BB (x₁ , BB₁) (x₂ , BB₂))
... | no _ = nothing
⊕ R l B ⊔ ⊕ R′ l′ B′ with ((R ≟ R′) ×-dec (l ≟-str l′))
... | yes _ = do
  BB ← B ⊔ B′
  just (⊕ R l BB)
... | no _ = nothing
& r x ⊔ & r′ x′ with r ≟ r′
... | yes _ = do
  xx ← mapLabels x x′
  just (& r xx)
... | no _ = nothing
_ ⊔ _ = nothing


----------------------------------------------------
-- enpoint projection

-- type to local type
projectType : ∀ {Θ} →  Role Θ → Type Θ → LType
projectType R T with R ∈? roles T
...                | no _ = ⊥
projectType R (⟶ x T T₁) | yes _ = _⟶_ (projectType R T) (projectType R T₁)
projectType R (T ＋ T₁) | yes _ = (projectType R T) ＋ (projectType R T₁)
projectType R (T mul T₁) | yes _ = (projectType R T) mul (projectType R T₁)
projectType R (o＠ x) | yes _ = o

-- the easy case: projection is ⊥ except if the role projected to is in the type
easy : ∀ {Θ} → Role Θ → Type Θ → Maybe (LValue Θ) → Maybe (LValue Θ)
easy R T C with R ∈? (roles T)
...           | no _ = just ⊥
...           | yes _ = C

project-∙ : ∀ {Θ} {P : Set} → Behaviour Θ → Behaviour Θ → Dec P → Maybe (Behaviour Θ)
project-∙ M N (yes _) = just (M ∙ N)
project-∙ (V ⊥) (V ⊥) (no _) = just (V ⊥)
project-∙ M (V ⊥) (no _) = just M
project-∙ _ N (no _) = just N

project-case : ∀ {Θ} {P : Set} → Behaviour Θ → (Var × Behaviour Θ) → (Var × Behaviour Θ) → Dec P → Var → Maybe (Behaviour Θ)
project-case M xN xN₁ (yes _) _ = just (case M xN xN₁)
project-case (V ⊥) (_ , (V ⊥)) (_ , (V ⊥)) (no _) _ = just (V ⊥)
project-case M (_ , (V ⊥)) (_ , (V ⊥)) (no _) _ = just M
project-case (V ⊥) (_ , N) (_ , N₁) (no _) _ = N ⊔ N₁
project-case M (_ , N) (_ , N₁) (no _) x′′ = (λ { n → (V (Λ x′′ ⊥ n)) ∙ M }) ⟫ (N ⊔ N₁) -- TODO need some x!

-- project choreography to local behaviour at role R
projectChoreo : ∀ {Θ Γ} {T : Type Θ} → Role Θ → (C : Choreography Θ) → (Γ ⊢ C ⦂ T) → Maybe (Behaviour Θ)

-- project Value to local value at role R
projectVal : ∀ {Θ Γ} {T : Type Θ} → Role Θ → (C : Value Θ) → (Γ ⊢ (V C) ⦂ T) → Maybe (LValue Θ)
projectVal {T = T} R (var x) Tc = easy R T (just (var x))
projectVal {T = (⟶ ρ T₁ T₂)} R (Λ x t c) (tabs Tc ρ) with R ∈? (roles (⟶ ρ T₁ T₂))
... | no _ = just ⊥
... | yes _ = do
  c′ ←  (projectChoreo R c Tc)
  (just (Λ x (projectType R t) c′))
projectVal {T = (T₁ ＋ T₂)} R (Inl x) (tinl Tc) = easy R (T₁ ＋ T₂) (projectVal R (x) Tc)
projectVal {T = (T₁ ＋ T₂)} R (Inr x) (tinr Tc) = easy R (T₁ ＋ T₂) (projectVal R (x) Tc)
projectVal {T = T} R (fst) Tc = easy R T (just fst)
projectVal {T = T} R (snd) Tc = easy R T (just snd)
projectVal {T = (T₁ mul T₂)} R (Pair x x₁) (tpair Tc Tc₁) with R ∈? (roles (T₁ mul T₂))
... | no _ = just ⊥
... | yes _ = do
  x′ ← projectVal R x Tc
  x₁′ ← projectVal R x₁ Tc₁
  (just (Pair x′ x₁′))
projectVal {T = T} R (O＠ S) Tc = easy R T (just O)
projectVal {T = ⟶ [] T T₁} R (com S S′) Tc with S ≟ S′
... | yes _ with R ≟ S
...  | yes _ | yes _ = {!!}
...  | yes _ | no _ = {!!}
... | no _ with R ≟ S | R ≟ S′
... | yes _ | yes _ = just (Λ " x " (projectType R T) (V (var " x ")))
... | no _ | yes _ = just ⊥
... | no _ | no _ = just ⊥
... | yes _ | no _ = just ⊥
... | no _ | no _ = just (send S′)
... | yes _ | no _ = just (recv S)


projectChoreo R (V v) Tc = do
  v′ ← projectVal R v Tc
  just (V v′)
projectChoreo {T = T} R (M ∙ N)  (tapp Tc Tc₁) = do
  MM ← projectChoreo R M Tc
  NN ← projectChoreo R N Tc₁
  project-∙ MM NN ((R ∈? roles T) ⊎-dec (R ∈? croles (M ∙ N)))
projectChoreo {T = T} R (case C (x , M) (x₁ , M₁)) (tcase Tc Tc₁ Tc₂) = do
  C′ ← (projectChoreo R C Tc)
  M′ ← (projectChoreo R M Tc₁)
  M₁′ ← (projectChoreo R M₁ Tc₂)
  project-case C′ (x , M′) (x₁ , M₁′) (R ∈? roles T) (freshVar ((fv M) ++ (fv M₁)))
projectChoreo R (select S S′ l C) (tsel Tc) with S ≟ R | S′ ≟ R | S ≟ S′
... | yes proof | no proof₁ | no proof₂ = ⊕ S′ l ⟫ (projectChoreo R C Tc)
... | no proof | yes proof₁ | no proof₂ = (λ p → & S [ (l , p) ]) ⟫ (projectChoreo R C Tc)
... | _ | _ | _ = projectChoreo R C Tc
