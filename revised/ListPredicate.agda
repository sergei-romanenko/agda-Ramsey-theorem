
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
  using (Setoid; Preorder)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Unary
  using(Pred; _∈_; _∪_; _∩_)
  renaming (_⊆′_ to _⊆_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PreorderReasoning as Pre

open import Function
import Function.Related as Related


-- Predicates and relations

Pred[_] : ∀ {ℓ} (X : Set ℓ) → Set (lsuc ℓ)
Pred[ A ] = Pred (List A) _

-----------------------------------------------------------------------------
-- ⊆-related stuff

⊆-refl : ∀ {ℓ} {X : Set ℓ} {a} {A : Pred X a} → A ⊆ A
⊆-refl x A = A

⊆-trans : ∀ {ℓ} {X : Set ℓ} {a b c}
            {A : Pred X a}{B : Pred X b}{C : Pred X c} →
  A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A⊆B B⊆C x = B⊆C x ∘ A⊆B x

≗⇒⊆ : ∀ {ℓ} {X : Set ℓ} {a} {A : Pred X a} {B : Pred X a} →
  A ≗ B → A ⊆ B
≗⇒⊆ {ℓ} {X} {a} {A} {B} A≗B x Ax rewrite sym $ A≗B x = Ax

-----------------------------------------------------------------------------
-- List predicate equality

infix 4 _≋_ 

_≋_ : ∀ {ℓ} {X : Set ℓ} {a} (A B : Pred X a) → Set (ℓ ⊔ a)
A ≋ B = A ⊆ B × B ⊆ A

≋-refl : ∀ {ℓ} {X : Set ℓ} {a} {A : Pred X a} → A ≋ A
≋-refl = ⊆-refl , ⊆-refl

≋-sym : ∀ {ℓ} {X : Set ℓ} {a} {A B : Pred X a} →
        A ≋ B → B ≋ A
≋-sym (A⊆B , B⊆A) = B⊆A , A⊆B 

≋-trans : ∀ {ℓ} {X : Set ℓ} {a} {A B C : Pred X a} →
         A ≋ B → B ≋ C → A ≋ C
≋-trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
  ⊆-trans A⊆B B⊆C , ⊆-trans C⊆B B⊆A

≋⇒⊆ : ∀ {ℓ} {X : Set ℓ} {a} {A B : Pred X a} →
  A ≋ B → A ⊆ B
≋⇒⊆ A≋B = proj₁ A≋B

≋-setoid : ∀ {ℓ} (X : Set ℓ) {a} → Setoid _ _
≋-setoid {ℓ} X {a} = record
 { Carrier = Pred X a;
   _≈_ = _≋_ ;
   isEquivalence = record
   { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans } }

module ≋-Reasoning {ℓ} {X : Set ℓ} {a} where
  open EqReasoning (≋-setoid X {a}) public

≗⊆-preorder : ∀ {ℓ} {X : Set ℓ} → Preorder (lsuc ℓ) (lsuc ℓ) ℓ
≗⊆-preorder {ℓ} {X} = record
  { Carrier = Pred X ℓ
  ; _≈_ = _≗_
  ; _∼_ = _⊆_
  ; isPreorder = record
    { isEquivalence = Setoid.isEquivalence (X →-setoid Set ℓ)
    ; reflexive = λ A≗B x Ax → ≗⇒⊆ (λ _ → A≗B x) Ax Ax
    ; trans = ⊆-trans
    }
  }

module ≗⊆-Reasoning {ℓ} {X : Set ℓ} where
  open Pre (≗⊆-preorder {ℓ} {X}) public
    renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≗⟨_⟩_; _≈⟨⟩_ to _≗⟨⟩_)

⊆-preorder : ∀ {ℓ} {X : Set ℓ} → Preorder (lsuc ℓ) ℓ ℓ
⊆-preorder {ℓ} {X} = record
  { Carrier = Pred X ℓ
  ; _≈_ = _≋_
  ; _∼_ = _⊆_
  ; isPreorder = record
    { isEquivalence = Setoid.isEquivalence (≋-setoid X)
    ; reflexive =  ≋⇒⊆
    ; trans = ⊆-trans
    }
  }

module ⊆-Reasoning {ℓ} {X : Set ℓ} where
  open Pre (⊆-preorder {ℓ} {X}) public
    renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≋⟨_⟩_; _≈⟨⟩_ to _≋⟨⟩_)

-----------------------------------------------------------------------------
-- Some special cases of substitutivity

⊆-cong : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B₁ B₂ : Pred X ℓ} →
                  A₁ ⊆ A₂ → B₁ ⊆ B₂ → A₁ ∪ B₁ ⊆ A₂ ∪ B₂
⊆-cong A₁⊆A₂ B₁⊆B₂ x =
  Sum.map (A₁⊆A₂ x) (B₁⊆B₂ x)

⊆-congˡ : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B : Pred X ℓ} →
                  A₁ ⊆ A₂ → A₁ ∪ B ⊆ A₂ ∪ B
⊆-congˡ A₁⊆A₂ = ⊆-cong A₁⊆A₂ ⊆-refl

⊆-congʳ : ∀ {ℓ} {X : Set ℓ} {A B₁ B₂ : Pred X ℓ} →
                  B₁ ⊆ B₂ → A ∪ B₁ ⊆ A ∪ B₂
⊆-congʳ B₁⊆B₂ = ⊆-cong ⊆-refl B₁⊆B₂


≋-cong : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B₁ B₂ : Pred X ℓ} →
                  A₁ ≋ A₂ → B₁ ≋ B₂ → A₁ ∪ B₁ ≋ A₂ ∪ B₂
≋-cong (A₁⊆A₂ , A₂⊆A₁) (B₁⊆B₂ , B₂⊆B₁) =
  ⊆-cong A₁⊆A₂ B₁⊆B₂ , ⊆-cong A₂⊆A₁ B₂⊆B₁

left-disj-subst : ∀ {ℓ} {X : Set ℓ} {A A′ B : Pred X ℓ} →
                  A ≋ A′ → A ∪ B ≋ A′ ∪ B
left-disj-subst A≋A′ = 
  ≋-cong A≋A′ ≋-refl

right-disj-subst : {X : Set} {A B B′ : Pred[ X ]} →
                   B ≋ B′ → A ∪ B ≋ A ∪ B′
right-disj-subst B≋B′ =
  ≋-cong ≋-refl B≋B′

-----------------------------------------------------------------------------

-- The false list predicate
𝟘 : {X : Set} → Pred[ X ]
𝟘 = const ⊥


-- The true list predicate
𝟙 : {X : Set} → Pred[ X ]
𝟙 = const ⊤

-----------------------------------------------------------------------------
-- Replacement for 𝟙 ≋ A (see Coquand's note), '𝟙≋ A' is easier for
-- agda to scrutinize.

𝟙≋ : {X : Set} → Pred[ X ] → Set
𝟙≋ A = ∀ xs → A xs

-- 𝟙≋ A is equivalent to 𝟙 ≋ A
𝟙≋⇒𝟙≋A : {X : Set} (A : Pred[ X ]) →
            𝟙≋ A → 𝟙 ≋ A
𝟙≋⇒𝟙≋A A 𝟙≋-A = const ∘ 𝟙≋-A , (λ xs → const tt)

𝟙≋A⇒𝟙≋ : {X : Set} → (A : Pred[ X ]) →
            𝟙 ≋ A → 𝟙≋ A
𝟙≋A⇒𝟙≋ A (𝟙⊆A , A⊆𝟙) xs = 𝟙⊆A xs tt

-----------------------------------------------------------------------------

mono-𝟙≋ : {X : Set} {A B : Pred[ X ]} →
             A ⊆ B → 𝟙≋ A → 𝟙≋ B
mono-𝟙≋ A⊆B 𝟙≋-A =
  A⊆B ˢ 𝟙≋-A

-----------------------------------------------------------------------------

𝟙⊆ : {X : Set} → Pred[ X ] → Set
𝟙⊆ A = ∀ xs → A xs

-- 𝟙⊆ A is equivalent to 𝟙 ⊆ A
𝟙⊆⇒𝟙⊆A : {X : Set} {A : Pred[ X ]} →
            𝟙⊆ A → 𝟙 ⊆ A
𝟙⊆⇒𝟙⊆A 𝟙⊆-A xs xs∈𝟙 = 𝟙⊆-A xs

𝟙⊆⇒𝟙≋ : {X : Set} {A : Pred[ X ]} →
            𝟙⊆ A → 𝟙≋ A
𝟙⊆⇒𝟙≋ 𝟙⊆A = 𝟙⊆A

𝟙≋⇒𝟙⊆ : {X : Set} {A : Pred[ X ]} →
            𝟙≋ A → 𝟙⊆ A
𝟙≋⇒𝟙⊆ 𝟙≋A = 𝟙≋A

𝟙≋⇒𝟙⊆A : {X : Set} {A : Pred[ X ]} →
            𝟙≋ A → 𝟙 ⊆ A
𝟙≋⇒𝟙⊆A 𝟙≋A xs xs∈𝟙 = 𝟙≋A xs

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
consDisj A B x = ≋-refl

-- the following two are not used:
consConj : {X : Set} (A B : Pred[ X ]) (x : X) →
           ((A ∩ B) · x) ≋ (A · x ∩ B · x)
consConj A B x = ≋-refl

unitCons : {X : Set} (x : X) → (𝟙 · x) ≋ 𝟙
unitCons x = ≋-refl

-----------------------------------------------------------------------------
-- substitutivity of _≋_ for _·_ and _⟪_⟫ 
-----------------------------------------------------------------------------
subst-·≋ : {X : Set} {A B : Pred[ X ]} → (x : X) →
            A ≋ B → A · x ≋ B · x
subst-·≋ x (a , b) = a ∘ _∷_ x , b ∘ _∷_ x

-----------------------------------------------------------------------------
subst-⟪⟫⊆ : {X : Set} {A B : Pred[ X ]} (x : X) →
            A ⊆ B → A ⟪ x ⟫ ⊆ B ⟪ x ⟫
subst-⟪⟫⊆ x A⊆B xs =
  Sum.map (A⊆B xs) (A⊆B (x ∷ xs))

-----------------------------------------------------------------------------
subst-⟪⟫≋ : {X : Set} {A B : Pred[ X ]} (x : X) →
            A ≋ B → A ⟪ x ⟫ ≋ B ⟪ x ⟫
subst-⟪⟫≋ x (A⊆B , B⊆A) =
  (subst-⟪⟫⊆ x A⊆B) , subst-⟪⟫⊆ x B⊆A

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
distrib-∩-cons x = ≋-refl

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
subst-∪⟪⟫⊆ {X} {P} {B} {S} x P⊆B∪S = begin
  P ⟪ x ⟫
    ⊆⟨ mono-⟪⟫ x P⊆B∪S ⟩
  (B ∪ S) ⟪ x ⟫
    ⊆⟨ distrib-∪⟪⟫⊆ B S x ⟩
  B ⟪ x ⟫ ∪ S ⟪ x ⟫
  ∎
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
subst-∪⟪⟫⊇ : {X : Set} {P B S : Pred[ X ]} (x : X) →
  B ∪ S ⊆ P → B ⟪ x ⟫ ∪ S ⟪ x ⟫ ⊆ P ⟪ x ⟫
subst-∪⟪⟫⊇ {X} {P} {B} {S} x B∪S⊆P = begin
  B ⟪ x ⟫ ∪ S ⟪ x ⟫
    ⊆⟨ distrib-∪⟪⟫⊇ B S x ⟩
  (B ∪ S) ⟪ x ⟫
    ⊆⟨ mono-⟪⟫ x B∪S⊆P ⟩
  P ⟪ x ⟫
  ∎
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
subst-∪≋⟪⟫ : {X : Set} {P B S : Pred[ X ]} (x : X) →
                P ≋ B ∪ S → P ⟪ x ⟫ ≋ B ⟪ x ⟫ ∪ S ⟪ x ⟫
subst-∪≋⟪⟫ {X} {P} {B} {S} x (P⊆B∪S , B∪S⊆P) =
  subst-∪⟪⟫⊆ x P⊆B∪S , subst-∪⟪⟫⊇ x B∪S⊆P

-----------------------------------------------------------------------------
