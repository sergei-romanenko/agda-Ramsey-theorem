
module ListPredicate where

open import Prelude

-----------------------------------------------------------------------------

-- Properties of list predicates A : Pred [ X ]

-----------------------------------------------------------------------------
-- Some (list) predicate operations

infixr 1010 _⨅_ _⨆_

_⨅_ : {A : Set} → Pred A → Pred A → Pred A
P ⨅ Q = λ a → P a ∧ Q a

_⨆_ : {A : Set} → Pred A → Pred A → Pred A
P ⨆ Q = λ a → P a ∨ Q a

-----------------------------------------------------------------------------
-- List predicate "subset"

infix 110 _⊆_

_⊆_ : {X : Set} → (A B : Pred [ X ]) → Set
A ⊆ B = ∀ xs → A xs → B xs


-----------------------------------------------------------------------------
-- List predicate equality

infix 110 _≡_ 

_≡_ : {X : Set} → Pred [ X ] → Pred [ X ] → Set
A ≡ B = A ⊆ B ∧ B ⊆ A

refl≡ : {X : Set} → (A : Pred [ X ]) → A ≡ A
refl≡ A = (λ x x' → x') , λ x x' → x'

symm≡ : {X : Set} → (A B : Pred [ X ]) →
        A ≡ B → B ≡ A
symm≡ A B (a , b) = b , a 

trans≡ : {X : Set} → (A B C : Pred [ X ]) →
         A ≡ B → B ≡ C → A ≡ C
trans≡ A B C (a , b) (a' , b') =
  (λ x x' → a' x (a x x')) , λ x x' → b x (b' x x') 


-----------------------------------------------------------------------------
-- Some special cases of substitutivity

left-disj-subst :  {X : Set} → (A A' B : Pred [ X ]) →
                   A ≡ A' → A ⨆ B ≡ A' ⨆ B
left-disj-subst A A' B (a , b) = 
  (λ xs h → ∨E {_}{_}{λ _ → (A' ⨆ B) xs} (λ a' → inl (a xs a')) inr h) ,
  λ xs h → ∨E {_}{_}{λ _ → (A ⨆ B) xs} (λ a' → inl (b xs a')) inr h

right-disj-subst :  {X : Set} → (A B B' : Pred [ X ]) →
                   B ≡ B' → A ⨆ B ≡ A ⨆ B'
right-disj-subst A A' B (a , b) = 
  (λ xs → ∨E inl (λ b' → inr (a xs b'))) ,
  (λ xs → ∨E inl (λ b' → inr (b xs b')))

-----------------------------------------------------------------------------

-- The false list predicate
₀ : {X : Set} → Pred [ X ]
₀ = λ xs → ⊥


-- The true list predicate
₁ : {X : Set} → Pred [ X ]
₁ = λ xs → ⊤

-----------------------------------------------------------------------------
-- Replacement for ₁ ≡ A (see Coquand's note), 'True A' is easier for
-- agda to scrutinize.

True : {X : Set} → Pred [ X ] → Set
True A = ∀ xs → A xs

-- True A is equivalent with ₁ ≡ A
True-1≡A : {X : Set} → (A : Pred [ X ]) →
            True A → (₁ ≡ A)
True-1≡A A h = (λ xs h' → h xs) , λ xs h → tt

1≡A-True : {X : Set} → (A : Pred [ X ]) →
            (₁ ≡ A) → True A
1≡A-True A (a , b) xs = a xs tt

-----------------------------------------------------------------------------
-- Some list predicate operations to be used in the definition of almost full
-----------------------------------------------------------------------------
infix 1020 _·_

_·_ : {X : Set} → Pred [ X ] → X → Pred [ X ]
P · x = λ xs → P (x :: xs)

-----------------------------------------------------------------------------
infix 1030 _⟪_⟫

_⟪_⟫ : {X : Set} → Pred [ X ] → X → Pred [ X ]
P ⟪ x ⟫ = P ⨆ P · x

-----------------------------------------------------------------------------
-- Some properties
-----------------------------------------------------------------------------
consDisj : {X : Set} → (A B : Pred [ X ]) → (x : X) →
           ((A ⨆ B) · x) ≡ (A · x ⨆ B · x)
consDisj A B x = refl≡ ((A ⨆ B) · x)

-- the following two are not used:
consConj : {X : Set} → (A B : Pred [ X ]) → (x : X) →
           ((A ⨅ B) · x) ≡ (A · x ⨅ B · x)
consConj A B x = refl≡ ((A ⨅ B) · x)

unitCons : {X : Set} → (x : X) → (₁ · x) ≡ ₁
unitCons x = refl≡ (₁ · x)

-----------------------------------------------------------------------------
-- substitutivity of _≡_ for _·_ and _⟪_⟫ 
-----------------------------------------------------------------------------
subst-·≡ : {X : Set} → (A B : Pred [ X ]) → (x : X) →
            A ≡ B → A · x ≡ B · x
subst-·≡ A B x = ∧E (λ a b → (λ xs → a (x :: xs)) , λ xs → b (x :: xs))

-----------------------------------------------------------------------------
subst-⟪⟫≡ : {X : Set} → (A B : Pred [ X ]) → (x : X) →
            A ≡ B → A ⟪ x ⟫ ≡ B ⟪ x ⟫
subst-⟪⟫≡ A B x (a , b) =
  (λ xs → ∨E (λ a' → inl (a xs a')) (λ b' → inr (a (x :: xs) b'))) , 
   λ xs → ∨E (λ a' → inl (b xs a')) (λ b' → inr (b (x :: xs) b'))

-----------------------------------------------------------------------------
-- Some properties about _⟪_⟫ and _·_
-----------------------------------------------------------------------------
distrib-⨆-⟪x⟫₁ : {X : Set} → (A B : Pred [ X ]) → (x : X) →
                (A ⨆ B) ⟪ x ⟫ ⊆ A ⟪ x ⟫ ⨆ B ⟪ x ⟫
distrib-⨆-⟪x⟫₁ A B x xs (inl (inl a)) = inl (inl a)
distrib-⨆-⟪x⟫₁ A B x xs (inl (inr b)) = inr (inl b)
distrib-⨆-⟪x⟫₁ A B x xs (inr (inl a)) = inl (inr a)
distrib-⨆-⟪x⟫₁ A B x xs (inr (inr b)) = inr (inr b)

-----------------------------------------------------------------------------
distrib-⨆-⟪x⟫₂ : {X : Set} → (A B : Pred [ X ]) → (x : X) →
    A ⟪ x ⟫ ⨆ B ⟪ x ⟫ ⊆ (A ⨆ B) ⟪ x ⟫
distrib-⨆-⟪x⟫₂ A B x xs (inl (inl a)) = inl (inl a)
distrib-⨆-⟪x⟫₂ A B x xs (inl (inr b)) = inr (inl b)
distrib-⨆-⟪x⟫₂ A B x xs (inr (inl a)) = inl (inr a)
distrib-⨆-⟪x⟫₂ A B x xs (inr (inr b)) = inr (inr b)

-----------------------------------------------------------------------------
distrib-⨆-⟪x⟫ : {X : Set} → (A B : Pred [ X ]) → (x : X) →
  (A ⨆ B) ⟪ x ⟫ ≡ A ⟪ x ⟫ ⨆ B ⟪ x ⟫
distrib-⨆-⟪x⟫ A B x = distrib-⨆-⟪x⟫₁ A B x , distrib-⨆-⟪x⟫₂ A B x

-----------------------------------------------------------------------------
-- this one is not used, but mentioned in Coquand's note:
distrib-⨅-cons : {X : Set} → (A B : Pred [ X ]) → (x : X) →
               (A ⨅ B) ⨆ A · x ⨅ B · x ≡ (A ⨅ B) ⟪ x ⟫
distrib-⨅-cons A B x = refl≡ ((A ⨅ B) ⨆ A · x ⨅ B · x)

-----------------------------------------------------------------------------
monotone-⟪x⟫ : {X : Set} → (A B : Pred [ X ]) → (x : X) → 
               A ⊆ B → A ⟪ x ⟫ ⊆ B ⟪ x ⟫
monotone-⟪x⟫ A B x h xs (inl h') = inl (h xs h')
monotone-⟪x⟫ A B x h xs (inr h') = inr (h (x :: xs) h')

-----------------------------------------------------------------------------
distrib-subst⨆≡⟪x⟫ : {X : Set} → (P B S : Pred [ X ]) → (x : X) →
                P ≡ B ⨆ S → P ⟪ x ⟫ ≡ B ⟪ x ⟫ ⨆ S ⟪ x ⟫
distrib-subst⨆≡⟪x⟫ P B S x (a , b) = 
  (λ xs h →
     distrib-⨆-⟪x⟫₁ B S x xs
       (monotone-⟪x⟫ P (B ⨆ S) x a xs h)) ,
     λ xs h →
         monotone-⟪x⟫ (B ⨆ S) P x b xs
         (distrib-⨆-⟪x⟫₂ B S x xs h)
-----------------------------------------------------------------------------
