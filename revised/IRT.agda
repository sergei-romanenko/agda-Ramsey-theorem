module IRT where

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

A∪[B∪C]⊆[A∪B]∪C : ∀ {ℓ} {X : Set ℓ} {A B C : Pred X ℓ} →
  A ∪ (B ∪ C) ⊆ (A ∪ B) ∪ C
A∪[B∪C]⊆[A∪B]∪C xs =
  [ inj₁ ∘ inj₁ , Sum.map inj₂ id ]′

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
-- n-ary relations
-----------------------------------------------------------------------------
NRel : (n : ℕ) → Set → Set₁
NRel zero A = Set
NRel (suc n) A = A → NRel n A


-- conversion from n-ary relations to list n-prefix predicates

fromNRel : {X : Set} → (n : ℕ) → NRel n X → Pred[ X ]
fromNRel zero R xs = R
fromNRel (suc n) R [] = ⊥
fromNRel (suc n) R (x ∷ xs) = fromNRel n (R x) xs

-- intersection of n-ary relations

infixr 14 _⋀_

_⋀_ : {A : Set} → {n : ℕ} → (R S : NRel n A) → NRel n A
_⋀_ {A} {zero} R S = R × S
_⋀_ {A} {suc n} R S a = R a ⋀ S a 


-- ⋀ commutes with ∩

mono-⋀∩ : {X : Set} → (n : ℕ) → (R S : NRel n X) →
              fromNRel n R ∩ fromNRel n S ⊆ fromNRel n (R ⋀ S)
mono-⋀∩ zero R S xs (a , b) = a , b
mono-⋀∩ (suc n) R S [] (a , b) = b
mono-⋀∩ (suc n) R S (x ∷ xs) (a , b) = 
  mono-⋀∩ n (R x) (S x) xs (a , b)

-----------------------------------------------------------------------------
-- Ar a, for a : D, called "arity". Ar is a bar for the property of
-- being constant. For instance, a predicate A expressing that its
-- argument has some element of some given property, for instance
-- being equal to one, is not Ar. There is no point where A becomes
-- constant.
--
-- A note. In the original definition of `Ar`, `ar-now` looked as
--   ar-now   : (n : ∀ x → (A · x) ≋ A) → Ar A
-- But ⊆ is sufficient for the proofs...
-- (A · x) ≋ A means that additional x does not change the situation, while
-- (A · x) ⊆ A means that additional x does not improve the situation.

-----------------------------------------------------------------------------
data Ar {X : Set} (A : Pred[ X ]) : Set where
  ar-now   : (n : ∀ x → (A · x) ⊆ A) → Ar A
  ar-later : (l : ∀ x → Ar (A · x)) → Ar A


-- The list predicate derived from an n-ary relation is Ar,
-- since it becomes constant when all the n arguments have been provided.

fromNRel→Ar : {X : Set} → (n : ℕ) →
              (R : NRel n X) → Ar (fromNRel n R)
fromNRel→Ar zero R = ar-now (const (flip const))
fromNRel→Ar (suc n) R = ar-later (fromNRel→Ar n ∘ R)


-----------------------------------------------------------------------------
-- Almost full relations. Like a Well-Quasi ordering, without transitivity
-----------------------------------------------------------------------------
data AF {X : Set} (A : Pred[ X ]) : Set where
  af-now :   (n : 𝟙⊆ A) → AF A
  af-later : (l : (x : X) → AF (A ⟪ x ⟫)) → AF A

-----------------------------------------------------------------------------
-- Monotonicity of AF
--
-- As stated in Coquand's note:
-----------------------------------------------------------------------------
mono-AF : {X : Set}  → {A B : Pred[ X ]} → A ⊆ B → AF A → AF B
-----------------------------------------------------------------------------
mono-AF A⊆B (af-now 𝟙⊆A) =
  af-now (mono-𝟙⊆ A⊆B 𝟙⊆A)
mono-AF {X} {A} {B} A⊆B (af-later afA⟪⟫) =
  af-later (λ x → mono-AF
    (begin A ⟪ x ⟫ ⊆⟨ mono-⟪⟫ x A⊆B ⟩ B ⟪ x ⟫ ∎)
    (afA⟪⟫ x))
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
-- preparation for lemma-02
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
lemma-02₁ : {X : Set} (A B R S : Pred[ X ]) (x : X) →
             𝟙⊆ (A · x ∪ R · x) →
             R ∩ S · x ⊆ A · x ∪ (R · x ∩ S · x)

lemma-02₁ A B R S x Ax∪Rx = begin
  R ∩ S · x
    ⊆⟨ (λ xs → proj₂) ⟩
  S · x
    ⊆⟨ _,_ ∘ Ax∪Rx ⟩
  (A · x ∪ R · x) ∩ S · x
    ⊆⟨ [A∪B]∩C⊆A∩C∪B∩C ⟩
  (A · x ∩ S · x) ∪ (R · x ∩ S · x)
    ⊆⟨ (λ xs → [ inj₁ ∘ proj₁ , inj₂ ]′) ⟩
  A · x ∪ (R · x ∩ S · x)
  ∎
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
lemma-02₂ : {X : Set} (A B R S : Pred[ X ]) (x : X) →
             𝟙⊆ (A ∪ R) →
             A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫) ⊆ (A ∪ B ∪ (R ∩ S)) ⟪ x ⟫

lemma-02₂ A B R S x A∪R = begin
   A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫)
    ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ A∩[B∪C]⊆A∩B∪A∩C ⟩
  A ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (R ∩ S · x)
    ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ mono-∪ʳ $ lemma-02₁ A S R S x (A∪R ∘ _∷_ x) ⟩
  A ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (A · x ∪ (R · x ∩ S · x))
    ⊆⟨ (λ xs →
      [ inj₁ ∘ inj₁ ,
        [ inj₂ ∘ inj₁ ,
          [ inj₂ ∘ inj₂ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ∘ inj₂ ∘ inj₂ ]′ ]′ ]′ ]′) ⟩
  (A ∪ A · x) ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (R · x ∩ S · x)
    ⊆⟨ ⊆-refl ⟩
  A ⟪ x ⟫ ∪ (B ⟪ x ⟫ ∪ (R ∩ S) ⟪ x ⟫)
    ⊆⟨ mono-∪ʳ $ distrib-∪⟪⟫⊇ ⟩
  A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ⟪ x ⟫
    ⊆⟨ distrib-∪⟪⟫⊇  ⟩
  (A ∪ B ∪ (R ∩ S)) ⟪ x ⟫
  ∎
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02₀ : {X : Set} {P A B R S : Pred[ X ]} → P ⊆ B ∪ S →
            𝟙⊆ (A ∪ R) → AF P → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02₀ {X} {P} {A} {B} {R} {S} P⊆B∪S 𝟙⊆A∪R (af-now 𝟙⊆P) =
  af-now (flip helper tt)
  where
  open ⊆-Reasoning
  helper : 𝟙 ⊆ A ∪ B ∪ (R ∩ S)
  helper = begin
    𝟙
      ⊆⟨ 𝟙⊆⇒𝟙⊆A 𝟙⊆P ⟩
    P
      ⊆⟨ P⊆B∪S ⟩
    B ∪ S
      ⊆⟨ _,_ ∘ 𝟙⊆A∪R ⟩
    (A ∪ R) ∩ (B ∪ S)
      ⊆⟨ [A∪C]∩[B∪D]⊆A∪B∪[C∩D] ⟩
    A ∪ B ∪ (R ∩ S)
    ∎

lemma-02₀ {X} {P} {A} {B} {R} {S} P⊆B∪S A∪R (af-later afP⟪⟫) = 
  af-later (λ x → 
    mono-AF
      (A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫) ⊆ (A ∪ B ∪ (R ∩ S)) ⟪ x ⟫
        ∋ lemma-02₂ A B R S x A∪R)
      (lemma-02₀ (P ⟪ x ⟫ ⊆ B ⟪ x ⟫ ∪ S ⟪ x ⟫ ∋ subst-∪⟪⟫⊆ x P⊆B∪S)
                 A∪R (afP⟪⟫ x)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 : {X : Set} {A B R S : Pred[ X ]} →
           𝟙⊆ (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 =
  lemma-02₀ ⊆-refl
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym : {X : Set} {A B R S : Pred[ X ]} →
               𝟙⊆ (B ∪ S) → AF (A ∪ R) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym {X} {A} {B} {R} {S} B∪S afA∪R =
  mono-AF
    (begin
      B ∪ A ∪ (S ∩ R)
        ⊆⟨ B∪A∪D∩C⊆A∪B∪C∩D ⟩
      A ∪ B ∪ (R ∩ S) ∎)
    (lemma-02 B∪S afA∪R)
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
-- preparation for lemma-03
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
lemma-03⊆ : {X : Set} {P A B R S : Pred[ X ]} (x : X) → 
               (∀ x → R · x ⊆ R) → P ⊆ A ∪ R →
               A ⟪ x ⟫ ∪ B ∪ R ∩ S ⊆ (A ∪ B ∪ R ∩ S) ⟪ x ⟫

lemma-03⊆ {X} {P} {A} {B} {R} {S} x R·⊆R P⊆A∪R = begin
  A ⟪ x ⟫ ∪ B ∪ R ∩ S
    ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ mono-∩ˡ $ mono-⟪x⟫ R x ⟩
  A ⟪ x ⟫ ∪ B ∪ R ⟪ x ⟫ ∩ S
    ⊆⟨ mono-∪ʳ $ mono-∪ (mono-⟪x⟫ B x) R⟪⟫∩S⊆[R∩S]⟪⟫ ⟩
  A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S) ⟪ x ⟫
    ⊆⟨ mono-∪ʳ $ distrib-∪⟪⟫⊇ ⟩
  A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ⟪ x ⟫
    ⊆⟨ distrib-∪⟪⟫⊇ ⟩
  (A ∪ B ∪ R ∩ S) ⟪ x ⟫
  ∎
  where
  open ⊆-Reasoning

  R⟪⟫∩S⊆[R∩S]⟪⟫ = begin
    R ⟪ x ⟫ ∩ S
      ≋⟨⟩
    (R ∪ R · x) ∩ S
      ⊆⟨ [A∪B]∩C⊆A∩C∪B∩C ⟩
    (R ∩ S) ∪ (R · x ∩ S)
      ⊆⟨ mono-∪ʳ $ mono-∩ˡ (R·⊆R x) ⟩
    (R ∩ S) ∪ (R ∩ S)
      ⊆⟨ A∪A⊆A ⟩
    R ∩ S
      ⊆⟨ A⊆A∪B ⟩
    (R ∩ S) ∪ (R · x ∩ S · x)
      ≋⟨⟩
    (R ∩ S) ⟪ x ⟫
    ∎

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03₀ : {X : Set} {P A B R S : Pred[ X ]} →
            (∀ x → R · x ⊆ R) → P ⊆ A ∪ R → AF P → AF (B ∪ S) → 
            AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

lemma-03₀ {X} {P} {A} {B} {R} {S} R·⊆R P⊆A∪R (af-now 𝟙⊆P) afB∪S = 
  lemma-02 (mono-𝟙⊆ P⊆A∪R 𝟙⊆P) afB∪S

lemma-03₀ {X} {P} {A} {B} {R} {S} R·⊆R P⊆A∪R (af-later afP⟪⟫) afB∪S =
  af-later AF-[A∪B∪R∩S]⟪⟫
  where
  open ⊆-Reasoning

  R⟪⟫⊆R : ∀ x → R ⟪ x ⟫ ⊆ R
  R⟪⟫⊆R x = begin
    R ⟪ x ⟫ ≋⟨⟩ R ∪ R · x ⊆⟨ mono-∪ʳ $ R·⊆R x ⟩ R ∪ R ⊆⟨ A∪A⊆A ⟩ R ∎

  P⟪⟫⊆A⟪⟫∪R : ∀ x → P ⟪ x ⟫ ⊆ A ⟪ x ⟫ ∪ R
  P⟪⟫⊆A⟪⟫∪R x = begin
    P ⟪ x ⟫
      ⊆⟨ mono-⟪⟫ x P⊆A∪R ⟩
    (A ∪ R) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊆ A R x ⟩
    A ⟪ x ⟫ ∪ R ⟪ x ⟫
      ⊆⟨ mono-∪ʳ $ R⟪⟫⊆R x ⟩
    A ⟪ x ⟫ ∪ R
    ∎

  AF-A⟪⟫∪B∪R∩S : ∀ x → AF (A ⟪ x ⟫ ∪ B ∪ R ∩ S)
  AF-A⟪⟫∪B∪R∩S x = lemma-03₀ R·⊆R (P⟪⟫⊆A⟪⟫∪R x) (afP⟪⟫ x) afB∪S

  AF-[A∪B∪R∩S]⟪⟫ : ∀ x → AF ((A ∪ B ∪ R ∩ S) ⟪ x ⟫ )
  AF-[A∪B∪R∩S]⟪⟫ x =
    mono-AF
      (begin
        (A ⟪ x ⟫ ∪ B ∪ R ∩ S)
          ⊆⟨ lemma-03⊆ x R·⊆R P⊆A∪R ⟩
        (A ∪ B ∪ R ∩ S) ⟪ x ⟫ ∎)
      (AF-A⟪⟫∪B∪R∩S x)
  
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 : {X : Set} {A B R S : Pred[ X ]} →
           (∀ x → R · x ⊆ R) → AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 R·⊆R afA∪R =
  lemma-03₀ R·⊆R ⊆-refl afA∪R

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym : {X : Set} {A B R S : Pred[ X ]} →
               (∀ x → S · x ⊆ S) →
               AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym {X} {A} {B} {R} {S} Sx⊆S afA∪R afB∪S =
  mono-AF
    (begin
      B ∪ A ∪ (S ∩ R)
        ⊆⟨ B∪A∪D∩C⊆A∪B∪C∩D ⟩
      A ∪ B ∪ (R ∩ S) ∎)
    (lemma-03 Sx⊆S afB∪S afA∪R)
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
-- preparation for theorem-04
-----------------------------------------------------------------------------
lemma-04-1 :
  {X : Set} {A B R S : Pred[ X ]} (x : X) →
  (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S)) ∪ (R · x ∩ S · x) ⊆ (A ∪ B ∪ R ∩ S) ⟪ x ⟫

lemma-04-1 {X} {A} {B} {R} {S} x xs =
  [ [ Sum.map inj₁ inj₁ ,
      [ Sum.map (inj₂ ∘ inj₁) (inj₂ ∘ inj₁) , inj₁ ∘ inj₂ ∘ inj₂ ]′ ]′ ,
    inj₂ ∘ inj₂ ∘ inj₂ ]′

-----------------------------------------------------------------------------
lemma-04-2 : {X : Set} {A B R S : Pred[ X ]} (x : X) →
             (A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ (A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ R · x ∩ S · x
             ⊆
             (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ R · x ∩ S · x

lemma-04-2 {X} {A} {B} {R} {S} x xs =
  [ inj₁ ∘ [ inj₁ , inj₂ ∘ Sum.map inj₁ id ]′ , Sum.map (Sum.map inj₁ id) id ]′

-----------------------------------------------------------------------------
lemma-04-3 : {X : Set} {A B R S : Pred[ X ]} (x : X) →
             (A ⟪ x ⟫ ∪ R · x) ∪ B ∪ (R ∩ S) ⊆ (A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ R · x

lemma-04-3 {X} {A} {B} {R} {S} x xs =
  [ Sum.map inj₁ id , inj₁ ∘ inj₂ ]′

lemma-04-4 : {X : Set} {A B R S : Pred[ X ]} (x : X) →
             A ∪ (B ⟪ x ⟫ ∪ S · x) ∪ R ∩ S ⊆ (A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x

lemma-04-4 {X} {A} {B} {R} {S} x xs =
  [ inj₁ ∘ inj₁ , [ Sum.map (inj₂ ∘ inj₁) id , inj₁ ∘ inj₂ ∘ inj₂ ]′ ]′

lemma-04-5 : {X : Set} {P A R : Pred[ X ]} (x : X) →
             P ⊆ A ∪ R → P ⟪ x ⟫ ⊆ (A ⟪ x ⟫ ∪ R · x) ∪ R

lemma-04-5 {X} {P} {A} {R} x P⊆A∪R = begin
  P ⟪ x ⟫
    ⊆⟨ subst-∪⟪⟫⊆ x P⊆A∪R ⟩
  A ⟪ x ⟫ ∪ R ⟪ x ⟫
    ⊆⟨ mono-∪ʳ B∪A⊆A∪B ⟩
  A ⟪ x ⟫ ∪ (R · x ∪ R)
    ⊆⟨ A∪[B∪C]⊆[A∪B]∪C ⟩
  (A ⟪ x ⟫ ∪ R · x) ∪ R
  ∎
  where open ⊆-Reasoning

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04' : {X : Set} {A B R S P Q : Pred[ X ]} → 
              Ar R → Ar S → P ⊆ A ∪ R → Q ⊆ B ∪ S →
              AF P → AF Q → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04' (ar-now R·⊆R) ArS P⊆A∪R Q⊆B∪S AfP AfQ = 
    lemma-03 R·⊆R 
      (mono-AF P⊆A∪R AfP)
      (mono-AF Q⊆B∪S AfQ)

theorem-04' (ar-later arRx) (ar-now Sx⊆S)
  P⊆A∪R Q⊆B∪S AfP AfQ = 
    lemma-03-sym Sx⊆S
      (mono-AF P⊆A∪R AfP)
      (mono-AF Q⊆B∪S AfQ)

theorem-04' (ar-later arRx) (ar-later arSx) P⊆A∪R Q⊆B∪S (af-now 𝟙⊆P) AfQ = 
    lemma-02 (λ xs → P⊆A∪R xs (𝟙⊆P xs)) (mono-AF Q⊆B∪S AfQ)

theorem-04'
  (ar-later arRx) (ar-later arSx) P⊆A∪R Q⊆B∪S (af-later afPx) (af-now 𝟙⊆Q) =
    lemma-02-sym
      (λ xs → Q⊆B∪S xs (𝟙⊆Q xs))
      (mono-AF P⊆A∪R (af-later afPx))

theorem-04'
  (ar-later arRx) (ar-later arSx) P⊆A∪R Q⊆B∪S (af-later afPx) (af-later afQx) =
    af-later (λ x → 
      mono-AF 
        (lemma-04-1 x)
        (mono-AF
           (lemma-04-2 x)
           (theorem-04'
             -- Ar (R · x)
             (arRx x)
             -- Ar (S · x)
             (arSx x)
             ⊆-refl
             ⊆-refl
             -- Goal: AF ((A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ R · x)
             -- we use AF (A ⟪ x ⟫ ∪ R · x ∪ R) and AF (B ∪ S)
             (mono-AF 
               (lemma-04-3 {-A B R S-} x)
               -- AF ((A ⟪ x ⟫ ∪ R · x) ∪ B ∪ R ∩ S)
               (theorem-04'
                 (ar-later arRx) (ar-later arSx)
                 -- P ⟪ x ⟫ ⊆ (A ⟪ x ⟫ ∪ R · x) ∪ R
                 (lemma-04-5 x P⊆A∪R)
                 Q⊆B∪S
                 (afPx x)
                 (af-later afQx)))
             -- Goal: AF ((A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x)
             -- we use AF (B ⟪ x ⟫ ∪ S · x ∪ S) and AF (A ∪ R)
             (mono-AF
               (lemma-04-4 x)
               -- AF (A ∪ S · x ∪ B ⟪ x ⟫ ∪ R ∩ S)
               (theorem-04'
                 (ar-later arRx) (ar-later arSx)
                 P⊆A∪R
                 (lemma-04-5 x Q⊆B∪S)
                 (af-later afPx)
                 (afQx x))))))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 : {X : Set} (A B R S : Pred[ X ]) → 
             Ar R → Ar S → AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 A B R S x x' =
  theorem-04' x x' ⊆-refl ⊆-refl

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 : {X : Set} → (R S : Pred[ X ]) → 
               Ar R → Ar S → AF R → AF S → AF (R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 R S h1 h2 h3 h4 = 
  mono-AF
    (λ xs → [ ⊥-elim , [ ⊥-elim , id ]′ ]′)
    (theorem-04 𝟘 𝟘 R S
      h1 h2 
      (mono-AF (λ xs h → inj₂ h) h3)
      (mono-AF (λ xs h → inj₂ h) h4))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- The n-ary intuitionistic Ramsey Theorem
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n : {X : Set} → (n : ℕ) → (R S : NRel n X) →
        AF (fromNRel n R) → AF (fromNRel n S) → AF (fromNRel n (R ⋀ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n n R S h1 h2 = mono-AF (mono-⋀∩ n R S)
                            (corollary-05 (fromNRel n R) (fromNRel n S)
                              (fromNRel→Ar n R) (fromNRel→Ar n S)
                              h1
                              h2)


-----------------------------------------------------------------------------
-- Almost full is unavoidable
-----------------------------------------------------------------------------

-- An encoding of strictly increasing finite sequences of natural numbers
-- (Thierry Coquand's idea):

data StrictIncSeq : Set where
  SIε : StrictIncSeq
  SI+1 : StrictIncSeq → StrictIncSeq
  SI0+1 : StrictIncSeq → StrictIncSeq -- cons 0 ∘ map suc 

mapSI : {X : Set} → (ℕ → X) → StrictIncSeq → List X
mapSI f SIε = []
mapSI f (SI+1 s) = mapSI (λ n → f (suc n)) s
mapSI f (SI0+1 s) = (f 0) ∷ (mapSI (λ n → f (suc n)) s)

-- Any infinite sequence must have a finite subsequence satisfying P
-- s is a strictly increasing sequence of positions in α
Unavoidable : {X : Set} → (P : Pred[ X ]) → Set
Unavoidable {X} P =
  (α : ℕ → X) → ∃ (λ (s : StrictIncSeq) → P (mapSI α s))

-- If P is almost full, then P is unavoidable
AF-Unavoidable : {X : Set} → (P : Pred[ X ]) →
                 AF P  → Unavoidable P
AF-Unavoidable P (af-now h) f = SIε , h []
AF-Unavoidable P (af-later x→AfP⟪x⟫) f = 
  let rem0 : ∃ (λ s → (P ⟪ f zero ⟫) (mapSI (λ x → f (suc x)) s))
      rem0 = AF-Unavoidable (P ⟪ f 0 ⟫) (x→AfP⟪x⟫ (f 0)) (λ x → f (suc x))
      s0 : StrictIncSeq
      s0 = proj₁ rem0
      p : (P ⟪ f 0 ⟫) (mapSI (λ x → f (suc x)) s0)
      p = proj₂ rem0
  in (∃ λ s → P (mapSI f s)) ∋ [ _,_ (SI+1 s0) , _,_ (SI0+1 s0) ]′ p
