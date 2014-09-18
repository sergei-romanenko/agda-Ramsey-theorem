module ListPredicate where

open import Level public
  renaming (zero to lzero; suc to lsuc)

open import Data.Nat
  using (ℕ; zero; suc)
open import Data.List
  using (List; []; _∷_)
open import Data.Sum as Sum public
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; swap; curry; uncurry; <_,_>; _-,-_)
open import Data.Unit
  using (⊤; tt)
open import Data.Empty

open import Relation.Unary
  using(Pred; _∈_; _∪_; _∩_; _⟨×⟩_; _⟨→⟩_;  _⟨·⟩_)
  renaming (_⊆′_ to _⊆_)
open import Relation.Binary
  using (Setoid; Preorder)
import Relation.Binary.PreorderReasoning as Pre

open import Function
import Function.Related as Related

-----------------------------------------------------------------------------
-- Predicates and relations

-----------------------------------------------------------------------------
-- ⊆ is a preorder

⊆-refl : ∀ {ℓ} {X : Set ℓ} {a} {A : Pred X a} → A ⊆ A
⊆-refl x A = A

⊆-trans : ∀ {ℓ} {X : Set ℓ} {a b c}
            {A : Pred X a}{B : Pred X b}{C : Pred X c} →
  A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A⊆B B⊆C x = B⊆C x ∘ A⊆B x


-----------------------------------------------------------------------------
-- Predicate "equality"
-- (To be used as the "underlying equality" in the definition of ⊆-preorder.

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

-----------------------------------------------------------------------------
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
-- Monotonicity of ∪

mono-∪ : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B₁ B₂ : Pred X ℓ} →
                  A₁ ⊆ A₂ → B₁ ⊆ B₂ → A₁ ∪ B₁ ⊆ A₂ ∪ B₂
mono-∪ A₁⊆A₂ B₁⊆B₂ x =
  Sum.map (A₁⊆A₂ x) (B₁⊆B₂ x)

mono-∪ˡ : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B : Pred X ℓ} →
                  A₁ ⊆ A₂ → A₁ ∪ B ⊆ A₂ ∪ B
mono-∪ˡ A₁⊆A₂ = mono-∪ A₁⊆A₂ ⊆-refl

mono-∪ʳ : ∀ {ℓ} {X : Set ℓ} {A B₁ B₂ : Pred X ℓ} →
                  B₁ ⊆ B₂ → A ∪ B₁ ⊆ A ∪ B₂
mono-∪ʳ B₁⊆B₂ = mono-∪ ⊆-refl B₁⊆B₂

-----------------------------------------------------------------------------
-- Monotonicity of ∩

mono-∩ : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B₁ B₂ : Pred X ℓ} →
                  A₁ ⊆ A₂ → B₁ ⊆ B₂ → A₁ ∩ B₁ ⊆ A₂ ∩ B₂
mono-∩ A₁⊆A₂ B₁⊆B₂ x =
  Prod.map (A₁⊆A₂ x) (B₁⊆B₂ x)

mono-∩ˡ : ∀ {ℓ} {X : Set ℓ} {A₁ A₂ B : Pred X ℓ} →
                  A₁ ⊆ A₂ → A₁ ∩ B ⊆ A₂ ∩ B
mono-∩ˡ A₁⊆A₂ = mono-∩ A₁⊆A₂ ⊆-refl

mono-∩ʳ : ∀ {ℓ} {X : Set ℓ} {A B₁ B₂ : Pred X ℓ} →
                  B₁ ⊆ B₂ → A ∩ B₁ ⊆ A ∩ B₂
mono-∩ʳ B₁⊆B₂ = mono-∩ ⊆-refl B₁⊆B₂

-----------------------------------------------------------------------------
-- Some logical facts to be used later
-----------------------------------------------------------------------------

A∪A⊆A : ∀ {ℓ} {X : Set ℓ} {A : Pred X ℓ} →
  A ∪ A ⊆ A
A∪A⊆A x =
  [ id , id ]′

A⊆A∪B : ∀ {ℓ} {X : Set ℓ} {A B : Pred X ℓ} →
  A ⊆ A ∪ B
A⊆A∪B xs = inj₁

B∪A⊆A∪B : ∀ {ℓ} {X : Set ℓ} {A B : Pred X ℓ} →
  B ∪ A ⊆ A ∪ B
B∪A⊆A∪B xs =
  [ inj₂ , inj₁ ]′

A∪B∪C⊆[A∪B]∪C : ∀ {ℓ} {X : Set ℓ} {A B C : Pred X ℓ} →
  A ∪ (B ∪ C) ⊆ (A ∪ B) ∪ C
A∪B∪C⊆[A∪B]∪C xs =
  [ inj₁ ∘ inj₁ , Sum.map inj₂ id ]′

[A∪B]∪C⊆A∪B∪C : ∀ {ℓ} {X : Set ℓ} {A B C : Pred X ℓ} →
  (A ∪ B) ∪ C ⊆ A ∪ B ∪ C
[A∪B]∪C⊆A∪B∪C xs =
  [ Sum.map id inj₁ , inj₂ ∘ inj₂ ]′

[A∪C]∩[B∪D]⊆A∪B∪[C∩D] : ∀ {ℓ} {X : Set ℓ} {A B C D : Pred X ℓ} →
  (A ∪ C) ∩ (B ∪ D) ⊆ A ∪ B ∪ (C ∩ D)
[A∪C]∩[B∪D]⊆A∪B∪[C∩D] xs =
  uncurry [ flip (const inj₁) ,
            flip [ flip (const (inj₂ ∘ inj₁)) , flip (curry (inj₂ ∘ inj₂)) ]′ ]′

B∪A∪D∩C⊆A∪B∪C∩D : ∀ {ℓ} {X : Set ℓ} {A B C D : Pred X ℓ} →
  B ∪ A ∪ D ∩ C ⊆ A ∪ B ∪ (C ∩ D)
B∪A∪D∩C⊆A∪B∪C∩D xs =
  [ inj₂ ∘ inj₁ , Sum.map id (inj₂ ∘ < proj₂ , proj₁ >) ]′

A∩[B∪C]⊆A∩B∪A∩C : ∀ {ℓ} {X : Set ℓ} {A B C : Pred X ℓ} →
  A ∩ (B ∪ C) ⊆ A ∩ B ∪ A ∩ C
A∩[B∪C]⊆A∩B∪A∩C xs =
  uncurry (λ a → Sum.map (_,_ a) (_,_ a))

[A∪B]∩C⊆A∩C∪B∩C : ∀ {ℓ} {X : Set ℓ} {A B C : Pred X ℓ} →
  (A ∪ B) ∩ C ⊆ (A ∩ C) ∪ (B ∩ C)
[A∪B]∩C⊆A∩C∪B∩C xs =
  uncurry (λ c → Sum.map (flip _,_ c) (flip _,_ c)) ∘ swap

A∪C∪D∪B∪E⊆[A∪B]∪C∪D∪E : ∀ {ℓ} {X : Set ℓ} {A B C D E : Pred X ℓ} →
  A ∪ C ∪ D ∪ B ∪ E ⊆ (A ∪ B) ∪ C ∪ D ∪ E
A∪C∪D∪B∪E⊆[A∪B]∪C∪D∪E xs =
  [ inj₁ ∘ inj₁ ,
    [ inj₂ ∘ inj₁ , [ inj₂ ∘ inj₂ ∘ inj₁ , Sum.map inj₂ (inj₂ ∘ inj₂) ]′ ]′ ]′

-----------------------------------------------------------------------------
-- List predicates
-----------------------------------------------------------------------------

Pred[_] : ∀ {ℓ} (X : Set ℓ) → Set (lsuc ℓ)
Pred[ A ] = Pred (List A) _

-- The false list predicate
𝟘 : {X : Set} → Pred[ X ]
𝟘 = const ⊥


-- The true list predicate
𝟙 : {X : Set} → Pred[ X ]
𝟙 = const ⊤

-----------------------------------------------------------------------------
-- Replacement for 𝟙 ≋ A (see Coquand's note), 𝟙⊆ A is easier for
-- Agda to scrutinize.

𝟙⊆ : {X : Set} (A : Pred[ X ]) → Set
𝟙⊆ A = ∀ xs → A xs

-- 𝟙⊆ A is equivalent to 𝟙 ⊆ A
𝟙⊆⇒𝟙⊆A : {X : Set} {A : Pred[ X ]} →
  𝟙⊆ A → 𝟙 ⊆ A
𝟙⊆⇒𝟙⊆A 𝟙⊆-A = const ∘ 𝟙⊆-A

𝟙⊆A⇒𝟙⊆ : {X : Set} (A : Pred[ X ]) →
  𝟙 ⊆ A → 𝟙⊆ A
𝟙⊆A⇒𝟙⊆ A 𝟙⊆A = flip 𝟙⊆A tt

-- 𝟙⊆ A is equivalent to 𝟙 ≋ A
𝟙⊆⇒𝟙≋A : {X : Set} (A : Pred[ X ]) →
  𝟙⊆ A → 𝟙 ≋ A
𝟙⊆⇒𝟙≋A A 𝟙⊆-A =
  const ∘ 𝟙⊆-A , const ∘ (const tt)

𝟙≋A⇒𝟙⊆ : {X : Set} (A : Pred[ X ]) →
  𝟙 ≋ A → 𝟙⊆ A
𝟙≋A⇒𝟙⊆ A (𝟙⊆A , A⊆𝟙) =
  𝟙⊆A⇒𝟙⊆ A 𝟙⊆A

-----------------------------------------------------------------------------

mono-𝟙⊆ : {X : Set} {A B : Pred[ X ]} →
  A ⊆ B → 𝟙⊆ A → 𝟙⊆ B
mono-𝟙⊆ A⊆B 𝟙⊆-A =
  A⊆B ˢ 𝟙⊆-A

-----------------------------------------------------------------------------

A⊆𝟘∪A : {X : Set} {A : Pred[ X ]} →
  A ⊆ 𝟘 ∪ A
A⊆𝟘∪A xs = inj₂

𝟘∪A⊆A : {X : Set} {A : Pred[ X ]} →
  𝟘 ∪ A ⊆ A
𝟘∪A⊆A xs = [ ⊥-elim , id ]′

-----------------------------------------------------------------------------
-- Some list predicate operations to be used in the definition of almost full
-----------------------------------------------------------------------------

_·_ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P · x = λ xs → P (x ∷ xs)

-----------------------------------------------------------------------------

_⟪_⟫ : {X : Set} → Pred[ X ] → X → Pred[ X ]
P ⟪ x ⟫ = P ∪ P · x

-----------------------------------------------------------------------------
-- Some properties about _⟪_⟫ and _·_
-----------------------------------------------------------------------------
distrib-∪⟪⟫⊆ : {X : Set} (A B : Pred[ X ]) (x : X) →
                (A ∪ B) ⟪ x ⟫ ⊆ A ⟪ x ⟫ ∪ B ⟪ x ⟫
distrib-∪⟪⟫⊆ A B x xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
distrib-∪⟪⟫⊇ : {X : Set} {A B : Pred[ X ]} {x : X} →
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ⊆ (A ∪ B) ⟪ x ⟫
distrib-∪⟪⟫⊇ xs =
  [ Sum.map inj₁ inj₁ , Sum.map inj₂ inj₂ ]′

-----------------------------------------------------------------------------
mono-⟪x⟫ : {X : Set} {A : Pred[ X ]} {x : X} → 
               A ⊆ A ⟪ x ⟫
mono-⟪x⟫ xs = inj₁

-----------------------------------------------------------------------------
mono-⟪⟫ : {X : Set} {A B : Pred[ X ]} (x : X) → 
               A ⊆ B → A ⟪ x ⟫ ⊆ B ⟪ x ⟫
mono-⟪⟫ x h xs = Sum.map (h xs) (h (x ∷ xs))
