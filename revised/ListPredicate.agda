
module ListPredicate where

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Data.List
  using (List; []; _∷_)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; curry; uncurry; _-,-_)
open import Data.Unit
  using (⊤; tt)
open import Data.Empty
  using (⊥)

open import Relation.Unary
  using(Pred; _∈_; _∪_; _∩_)
  renaming (_⊆′_ to _⊆_)

open import Function

-- Predicates and relations

Pred[_] : ∀ {ℓ} (X : Set ℓ) → Set (lsuc ℓ)
Pred[ A ] = Pred (List A) _

-----------------------------------------------------------------------------
-- List predicate equality

infix 4 _≋_ 

_≋_ : {X : Set} → Pred[ X ] → Pred[ X ] → Set
A ≋ B = A ⊆ B × B ⊆ A

≋refl : {X : Set} {A : Pred[ X ]} → A ≋ A
≋refl = (λ xs → id) , (λ xs → id)

≋sym : {X : Set} → (A B : Pred[ X ]) →
        A ≋ B → B ≋ A
≋sym A B (A⊆B , B⊆A) = B⊆A , A⊆B 

≋trans : {X : Set} → (A B C : Pred[ X ]) →
         A ≋ B → B ≋ C → A ≋ C
≋trans A B C (A⊆B , B⊆A) (B⊆C , C⊆B) =
  (λ xs → B⊆C xs ∘ A⊆B xs) , (λ xs → B⊆A xs ∘ C⊆B xs) 


-----------------------------------------------------------------------------
-- Some special cases of substitutivity

left-disj-subst : {X : Set} → (A A′ B : Pred[ X ]) →
                  A ≋ A′ → A ∪ B ≋ A′ ∪ B
left-disj-subst A A′ B (A⊆A′ , A′⊆A) = 
  (λ xs → Sum.map (A⊆A′ xs) id) , (λ xs → Sum.map (A′⊆A xs) id)

right-disj-subst : {X : Set} → (A B B′ : Pred[ X ]) →
                   B ≋ B′ → A ∪ B ≋ A ∪ B′
right-disj-subst A A′ B (B⊆B′ , B′⊆B) =
  (λ xs → Sum.map id (B⊆B′ xs)) , (λ xs → Sum.map id (B′⊆B xs))

-----------------------------------------------------------------------------

-- The false list predicate
𝟘 : {X : Set} → Pred[ X ]
𝟘 = λ xs → ⊥


-- The true list predicate
𝟙 : {X : Set} → Pred[ X ]
𝟙 = const ⊤

-----------------------------------------------------------------------------
-- Replacement for 𝟙 ≋ A (see Coquand's note), '𝟙≋ A' is easier for
-- agda to scrutinize.

𝟙≋ : {X : Set} → Pred[ X ] → Set
𝟙≋ A = ∀ xs → A xs

-- 𝟙≋ A is equivalent with 𝟙 ≋ A
𝟙≋-𝟙≋A : {X : Set} → (A : Pred[ X ]) →
            𝟙≋ A → 𝟙 ≋ A
𝟙≋-𝟙≋A A 𝟙≋-A = const ∘ 𝟙≋-A , (λ xs → const tt)

𝟙≋A-𝟙≋ : {X : Set} → (A : Pred[ X ]) →
            𝟙 ≋ A → 𝟙≋ A
𝟙≋A-𝟙≋ A (𝟙⊆A , A⊆𝟙) xs = 𝟙⊆A xs tt

-----------------------------------------------------------------------------
-- Some list predicate operations to be used in the definition of almost full
-----------------------------------------------------------------------------
infix 1020 _·_

_·_ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P · x = λ xs → P (x ∷ xs)

-----------------------------------------------------------------------------
infix 1030 _⟪_⟫

_⟪_⟫ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P ⟪ x ⟫ = P ∪ P · x

-----------------------------------------------------------------------------
-- Some properties
-----------------------------------------------------------------------------
consDisj : {X : Set} → (A B : Pred[ X ]) → (x : X) →
           ((A ∪ B) · x) ≋ (A · x ∪ B · x)
consDisj A B x = ≋refl

-- the following two are not used:
consConj : {X : Set} → (A B : Pred[ X ]) → (x : X) →
           ((A ∩ B) · x) ≋ (A · x ∩ B · x)
consConj A B x = ≋refl

unitCons : {X : Set} → (x : X) → (𝟙 · x) ≋ 𝟙
unitCons x = ≋refl

-----------------------------------------------------------------------------
-- substitutivity of _≋_ for _·_ and _⟪_⟫ 
-----------------------------------------------------------------------------
subst-·≋ : {X : Set} → (A B : Pred[ X ]) → (x : X) →
            A ≋ B → A · x ≋ B · x
subst-·≋ A B x (a , b) = (λ xs → a (x ∷ xs)) , (λ xs → b (x ∷ xs))

-----------------------------------------------------------------------------
subst-⟪⟫≋ : {X : Set} → (A B : Pred[ X ]) → (x : X) →
            A ≋ B → A ⟪ x ⟫ ≋ B ⟪ x ⟫
subst-⟪⟫≋ A B x (a , b) =
  (λ xs → Sum.map (a xs) (a (x ∷ xs))) , (λ xs → Sum.map (b xs) (b (x ∷ xs)))

-----------------------------------------------------------------------------
-- Some properties about _⟪_⟫ and _·_
-----------------------------------------------------------------------------
distrib-∪-⟪x⟫₁ : {X : Set} → (A B : Pred[ X ]) → (x : X) →
                (A ∪ B) ⟪ x ⟫ ⊆ A ⟪ x ⟫ ∪ B ⟪ x ⟫
distrib-∪-⟪x⟫₁ A B x xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
distrib-∪-⟪x⟫₂ : {X : Set} → (A B : Pred[ X ]) → (x : X) →
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ⊆ (A ∪ B) ⟪ x ⟫
distrib-∪-⟪x⟫₂ A B x xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
distrib-∪-⟪x⟫ : {X : Set} → (A B : Pred[ X ]) → (x : X) →
  (A ∪ B) ⟪ x ⟫ ≋ A ⟪ x ⟫ ∪ B ⟪ x ⟫
distrib-∪-⟪x⟫ A B x = distrib-∪-⟪x⟫₁ A B x , distrib-∪-⟪x⟫₂ A B x

-----------------------------------------------------------------------------
-- this one is not used, but mentioned in Coquand's note:
distrib-∩-cons : {X : Set} → (A B : Pred[ X ]) → (x : X) →
               (A ∩ B) ∪ A · x ∩ B · x ≋ (A ∩ B) ⟪ x ⟫
distrib-∩-cons A B x = ≋refl

-----------------------------------------------------------------------------
monotone-⟪x⟫ : {X : Set} → (A B : Pred[ X ]) → (x : X) → 
               A ⊆ B → A ⟪ x ⟫ ⊆ B ⟪ x ⟫
monotone-⟪x⟫ A B x h xs = Sum.map (h xs) (h (x ∷ xs))

-----------------------------------------------------------------------------
distrib-subst∪≋⟪x⟫ : {X : Set} → (P B S : Pred[ X ]) → (x : X) →
                P ≋ B ∪ S → P ⟪ x ⟫ ≋ B ⟪ x ⟫ ∪ S ⟪ x ⟫
distrib-subst∪≋⟪x⟫ P B S x (a , b) =
  (λ xs → (distrib-∪-⟪x⟫₁ B S x xs) ∘ (monotone-⟪x⟫ P (B ∪ S) x a xs)) ,
  (λ xs → (monotone-⟪x⟫ (B ∪ S) P x b xs) ∘ distrib-∪-⟪x⟫₂ B S x xs)
-----------------------------------------------------------------------------
