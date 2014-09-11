
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

open import Relation.Binary
  using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Unary
  using(Pred; _∈_; _∪_; _∩_)
  renaming (_⊆′_ to _⊆_)

open import Function
import Function.Related as Related


-- Predicates and relations

Pred[_] : ∀ {ℓ} (X : Set ℓ) → Set (lsuc ℓ)
Pred[ A ] = Pred (List A) _

⊆-id : {X : Set} {A : Pred[ X ]} → A ⊆ A
⊆-id xs h = h

-----------------------------------------------------------------------------
-- List predicate equality

infix 4 _≋_ 

_≋_ : {X : Set} → Pred[ X ] → Pred[ X ] → Set
A ≋ B = A ⊆ B × B ⊆ A

≋refl : {X : Set} {A : Pred[ X ]} → A ≋ A
≋refl = (λ xs → id) , (λ xs → id)

≋sym : {X : Set} {A B : Pred[ X ]} →
        A ≋ B → B ≋ A
≋sym (A⊆B , B⊆A) = B⊆A , A⊆B 

≋trans : {X : Set} {A B C : Pred[ X ]} →
         A ≋ B → B ≋ C → A ≋ C
≋trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
  (λ xs → B⊆C xs ∘ A⊆B xs) , (λ xs → B⊆A xs ∘ C⊆B xs) 

≋setoid : ∀ {X : Set} (A : Pred[ X ]) → Setoid _ _
≋setoid {X} A = record
 { Carrier = Pred[ X ] ;
   _≈_ = _≋_ ;
   isEquivalence = record
   { refl = ≋refl ; sym = ≋sym ; trans = ≋trans } }

module ≋-Reasoning {X : Set} (A : Pred[ X ]) where
  open EqReasoning (≋setoid A) public

-----------------------------------------------------------------------------
-- Some special cases of substitutivity

left-disj-subst : {X : Set} {A A′ B : Pred[ X ]} →
                  A ≋ A′ → A ∪ B ≋ A′ ∪ B
left-disj-subst (A⊆A′ , A′⊆A) = 
  flip Sum.map id ∘ A⊆A′ , flip Sum.map id ∘ A′⊆A

right-disj-subst : {X : Set} {A B B′ : Pred[ X ]} →
                   B ≋ B′ → A ∪ B ≋ A ∪ B′
right-disj-subst (B⊆B′ , B′⊆B) =
  Sum.map id ∘ B⊆B′ , Sum.map id ∘ B′⊆B

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
𝟙≋⇒𝟙≋A : {X : Set} (A : Pred[ X ]) →
            𝟙≋ A → 𝟙 ≋ A
𝟙≋⇒𝟙≋A A 𝟙≋-A = const ∘ 𝟙≋-A , (λ xs → const tt)

𝟙≋A⇒𝟙≋ : {X : Set} → (A : Pred[ X ]) →
            𝟙 ≋ A → 𝟙≋ A
𝟙≋A⇒𝟙≋ A (𝟙⊆A , A⊆𝟙) xs = 𝟙⊆A xs tt

-----------------------------------------------------------------------------

𝟙≋-⊆⇒𝟙≋ : {X : Set} {A B : Pred[ X ]} →
             𝟙≋ A → A ⊆ B → 𝟙≋ B
𝟙≋-⊆⇒𝟙≋ 𝟙≋-A A⊆B =
  A⊆B ˢ 𝟙≋-A

-----------------------------------------------------------------------------
-- Some list predicate operations to be used in the definition of almost full
-----------------------------------------------------------------------------
--infix 1020 _·_

_·_ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P · x = λ xs → P (x ∷ xs)

-----------------------------------------------------------------------------
--infix 1030 _⟪_⟫

_⟪_⟫ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P ⟪ x ⟫ = P ∪ P · x

-----------------------------------------------------------------------------
-- Some properties
-----------------------------------------------------------------------------
consDisj : {X : Set} (A B : Pred[ X ]) (x : X) →
           ((A ∪ B) · x) ≋ (A · x ∪ B · x)
consDisj A B x = ≋refl

-- the following two are not used:
consConj : {X : Set} (A B : Pred[ X ]) (x : X) →
           ((A ∩ B) · x) ≋ (A · x ∩ B · x)
consConj A B x = ≋refl

unitCons : {X : Set} (x : X) → (𝟙 · x) ≋ 𝟙
unitCons x = ≋refl

-----------------------------------------------------------------------------
-- substitutivity of _≋_ for _·_ and _⟪_⟫ 
-----------------------------------------------------------------------------
subst-·≋ : {X : Set} {A B : Pred[ X ]} → (x : X) →
            A ≋ B → A · x ≋ B · x
subst-·≋ x (a , b) = a ∘ _∷_ x , b ∘ _∷_ x

-----------------------------------------------------------------------------
subst-⟪⟫≋ : {X : Set} {A B : Pred[ X ]} → (x : X) →
            A ≋ B → A ⟪ x ⟫ ≋ B ⟪ x ⟫
subst-⟪⟫≋ x (a , b) =
  (λ xs → Sum.map (a xs) (a (x ∷ xs))) , (λ xs → Sum.map (b xs) (b (x ∷ xs)))

-----------------------------------------------------------------------------
-- Some properties about _⟪_⟫ and _·_
-----------------------------------------------------------------------------
distrib-∪⟪⟫⊆ : {X : Set} (A B : Pred[ X ]) (x : X) →
                (A ∪ B) ⟪ x ⟫ ⊆ A ⟪ x ⟫ ∪ B ⟪ x ⟫
distrib-∪⟪⟫⊆ A B x xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
distrib-∪⟪⟫⊇ : {X : Set} (A B : Pred[ X ]) (x : X) →
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ⊆ (A ∪ B) ⟪ x ⟫
distrib-∪⟪⟫⊇ A B x xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
distrib-∪-⟪x⟫ : {X : Set} {A B : Pred[ X ]} (x : X) →
  (A ∪ B) ⟪ x ⟫ ≋ A ⟪ x ⟫ ∪ B ⟪ x ⟫
distrib-∪-⟪x⟫ {X} {A} {B} x = distrib-∪⟪⟫⊆ A B x , distrib-∪⟪⟫⊇ A B x

-----------------------------------------------------------------------------
-- this one is not used, but mentioned in Coquand's note:
distrib-∩-cons : {X : Set} {A B : Pred[ X ]} (x : X) →
               (A ∩ B) ∪ A · x ∩ B · x ≋ (A ∩ B) ⟪ x ⟫
distrib-∩-cons x = ≋refl

-----------------------------------------------------------------------------
mono-⟪x⟫ : {X : Set} (A : Pred[ X ]) (x : X) → 
               A ⊆ A ⟪ x ⟫
mono-⟪x⟫ A x xs = inj₁

-----------------------------------------------------------------------------
mono-⟪⟫ : {X : Set} {A B : Pred[ X ]} (x : X) → 
               A ⊆ B → A ⟪ x ⟫ ⊆ B ⟪ x ⟫
mono-⟪⟫ x h xs = Sum.map (h xs) (h (x ∷ xs))

-----------------------------------------------------------------------------
subst-∪⟪⟫⊆ : {X : Set} {P B S : Pred[ X ]} (x : X) →
  P ⊆ B ∪ S → P ⟪ x ⟫ ⊆ B ⟪ x ⟫ ∪ S ⟪ x ⟫
subst-∪⟪⟫⊆ {X} {P} {B} {S} x P⊆B∪S xs =
  (P ⟪ x ⟫) xs
    ∼⟨ mono-⟪⟫ x P⊆B∪S xs ⟩
  ((B ∪ S) ⟪ x ⟫) xs
    ∼⟨ distrib-∪⟪⟫⊆ B S x xs ⟩
  (B ⟪ x ⟫ ∪ S ⟪ x ⟫) xs
  ∎
  where open Related.EquationalReasoning

-----------------------------------------------------------------------------
subst-∪⟪⟫⊇ : {X : Set} {P B S : Pred[ X ]} (x : X) →
  B ∪ S ⊆ P → B ⟪ x ⟫ ∪ S ⟪ x ⟫ ⊆ P ⟪ x ⟫
subst-∪⟪⟫⊇ {X} {P} {B} {S} x B∪S⊆P xs =
  (B ⟪ x ⟫ ∪ S ⟪ x ⟫) xs
    ∼⟨ distrib-∪⟪⟫⊇ B S x xs ⟩
  ((B ∪ S) ⟪ x ⟫) xs
    ∼⟨ mono-⟪⟫ x B∪S⊆P xs ⟩
  (P ⟪ x ⟫) xs
  ∎
  where open Related.EquationalReasoning

-----------------------------------------------------------------------------
subst-∪≋⟪⟫ : {X : Set} {P B S : Pred[ X ]} (x : X) →
                P ≋ B ∪ S → P ⟪ x ⟫ ≋ B ⟪ x ⟫ ∪ S ⟪ x ⟫
subst-∪≋⟪⟫ {X} {P} {B} {S} x (P⊆B∪S , B∪S⊆P) =
  subst-∪⟪⟫⊆ x P⊆B∪S , subst-∪⟪⟫⊇ x B∪S⊆P

-----------------------------------------------------------------------------
