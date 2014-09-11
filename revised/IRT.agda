
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
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; curry; uncurry; <_,_>; _-,-_)
open import Data.Unit
  using (⊤; tt)
open import Data.Empty
  using (⊥)

open import Relation.Unary
  using(Pred; _∈_; _∪_; _∩_)
  renaming (_⊆′_ to _⊆_)
open import Relation.Binary.PropositionalEquality

open import Function
import Function.Related as Related

open import ListPredicate

-----------------------------------------------------------------------------
-- Some logical facts
-----------------------------------------------------------------------------

-- commutativity of ⊎ and ×
commut-⊎ : {A B : Set} → A ⊎ B → B ⊎ A
commut-⊎ = [ inj₂ , inj₁ ]′

commut-× : {A B : Set} → A × B → B × A
commut-× = < proj₂ , proj₁ >

-- some associativity laws of ⊎
left-assoc-⊎ : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
left-assoc-⊎ = [ Sum.map id inj₁ , inj₂ ∘ inj₂ ]′

right-assoc-⊎ : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
right-assoc-⊎ = [ inj₁ ∘ inj₁ , Sum.map inj₂ id ]′

-- a few laws to be used later

A⊎C→B⊎D→A⊎B⊎C×D : {A B C D : Set} → A ⊎ C → B ⊎ D → A ⊎ B ⊎ (C × D)
A⊎C→B⊎D→A⊎B⊎C×D =
  [ flip (const inj₁) ,
    flip [ flip (const (inj₂ ∘ inj₁)) , curry (inj₂ ∘ inj₂ ∘ commut-×) ]′ ]′

B⊎A⊎D×C→A⊎B⊎C×D : {A B C D : Set} → B ⊎ A ⊎ D × C → A ⊎ B ⊎ C × D
B⊎A⊎D×C→A⊎B⊎C×D = [ inj₂ ∘ inj₁ , Sum.map id (inj₂ ∘ commut-×) ]′

⊥⊎⊥⊎A→A : {A : Set} → ⊥ ⊎ ⊥ ⊎ A → A
⊥⊎⊥⊎A→A (inj₁ ())
⊥⊎⊥⊎A→A (inj₂ (inj₁ ()))
⊥⊎⊥⊎A→A (inj₂ (inj₂ b)) = b

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

commut-⋀-∩₁ : {X : Set} → (n : ℕ) → (R S : NRel n X) →
              fromNRel n R ∩ fromNRel n S ⊆ fromNRel n (R ⋀ S)
commut-⋀-∩₁ zero R S xs (a , b) = a , b
commut-⋀-∩₁ (suc n) R S [] (a , b) = b
commut-⋀-∩₁ (suc n) R S (x ∷ xs) (a , b) = 
  commut-⋀-∩₁ n (R x) (S x) xs (a , b)

commut-⋀-∩₂ : {X : Set} → (n : ℕ) → (R S : NRel n X) →
              fromNRel n (R ⋀ S) ⊆ fromNRel n R ∩ fromNRel n S
commut-⋀-∩₂ zero R S xs h = h
commut-⋀-∩₂ (suc n) R S [] h = h , h
commut-⋀-∩₂ (suc n) R S (x ∷ xs) h =
  commut-⋀-∩₂ n (R x) (S x) xs h

commut-⋀-∩ : {X : Set} → (n : ℕ) → (R S : NRel n X) →
             fromNRel n R ∩ fromNRel n S ≋ fromNRel n (R ⋀ S)
commut-⋀-∩ n R S = commut-⋀-∩₁ n R S , commut-⋀-∩₂ n R S


-----------------------------------------------------------------------------
-- Ar a, for a : D, called "arity". Ar is a bar for the property of
-- being constant. For instance, a predicate A expressing that its
-- argument has some element of some given property, for instance
-- being equal to one, is not Ar. There is no point where A becomes
-- constant.
-----------------------------------------------------------------------------
data Ar {X : Set} (A : Pred[ X ]) : Set where
  ar-now   : (n : ∀ x → (A · x) ≋ A) → Ar A
  ar-later : (l : ∀ x → Ar (A · x)) → Ar A


-- The list predicate derived from an n-ary relation is Ar,
-- since it becomes constant when all the n arguments have been provided.

fromNRel→Ar : {X : Set} → (n : ℕ) →
              (R : NRel n X) → Ar (fromNRel n R)
fromNRel→Ar zero R = ar-now (const (flip const , flip const))
fromNRel→Ar (suc n) R = ar-later (fromNRel→Ar n ∘ R)


-----------------------------------------------------------------------------
-- Almost full relations. Like a Well-Quasi ordering, without transitivity
-----------------------------------------------------------------------------
data AF {X : Set} (A : Pred[ X ]) : Set where
  af-now :   (n : 𝟙≋ A) → AF A
  af-later : (l : (x : X) → AF (A ⟪ x ⟫)) → AF A


-- By P is monotone, we mean: (A → B) → P(A) → P(B)
-- So IRT.lemma-01 could be formulated as AF being monotone

monotone : ∀ {ℓ} {X : Set ℓ} → (Pred X ℓ → Set ℓ) → Set (lsuc ℓ)
monotone {ℓ} {X} P = {A B : Pred X ℓ} →
                        ((x : X) → A x → B x) → (P A → P B)

-----------------------------------------------------------------------------
-- Monotonicity of AF
--
-- As stated in Coquand's note:
-- mono-AF : {X : Set} → {A B : Pred[ X ]} → A ⊆ B → AF A → AF B
-----------------------------------------------------------------------------
mono-AF : {X : Set} → monotone (AF {X})
-----------------------------------------------------------------------------
mono-AF A⊆B (af-now p) =
  af-now (λ xs → A⊆B xs (p xs))
mono-AF A⊆B (af-later f) =
  af-later (λ x → mono-AF (mono-⟪⟫ x A⊆B) (f x))

-----------------------------------------------------------------------------
-- preparation for lemma-02
-----------------------------------------------------------------------------
lemma-02-1 : {X : Set} {A B R S : Pred[ X ]} → 
             𝟙≋ (A ∪ R) → 𝟙≋ (B ∪ S) → 𝟙≋ (A ∪ B ∪ (R ∩ S))
lemma-02-1 h1 h2 =
  λ xs → A⊎C→B⊎D→A⊎B⊎C×D (h1 xs) (h2 xs)

-- N.B. most of the proofs below who are written with
-- pattern-matching, have been auto-generated (with some manual
-- renaming) by Agda's "auto" facility, by Fredrik Lindblad
-----------------------------------------------------------------------------
lemma-02-2-1 : {X : Set} (A B R S : Pred[ X ]) (x : X) →
               R ∩ S · x ⊆ A · x ∪ (R · x ∩ S · x) →
               A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫) ⊆ (A ∪ B ∪ (R ∩ S))⟪ x ⟫

lemma-02-2-1 A B R S x h1 xs =
  [ inj₁ ∘ inj₁ ,
    [ Sum.map (inj₂ ∘ inj₁) (inj₂ ∘ inj₁) , uncurry (λ r →
              Sum.map (inj₂ ∘ inj₂ ∘ _,_ r) (Sum.map id inj₂ ∘ h1 xs ∘ _,_ r)) ]′ ]′

-----------------------------------------------------------------------------
lemma-02-2 : {X : Set} (A B R S : Pred[ X ]) (x : X) →
             𝟙≋ (A ∪ R) →
             A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫) ⊆ (A ∪ B ∪ (R ∩ S))⟪ x ⟫
lemma-02-2 A B R S x h1 xs h2 =
  lemma-02-2-1 A B R S x 
    (λ ys ab → Sum.map id (flip _,_ (proj₂ ab)) (h1 (x ∷ ys))) xs h2

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02' : {X : Set} → (P A B R S : Pred[ X ]) → P ⊆ B ∪ S →
            𝟙≋ (A ∪ R) → AF P → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02' P A B R S P⊆B∪S A∪R (af-now 𝟙≋P) =
  af-now (λ xs → lemma-02-1 (λ ys → A∪R xs)
                               (λ ys → 𝟙≋-⊆⇒𝟙≋ 𝟙≋P P⊆B∪S ys) xs)

lemma-02' P A B R S P⊆B∪S A∪R (af-later afPx) = 
  af-later (λ x → 
    mono-AF
      (lemma-02-2 A B R S x A∪R)
      (lemma-02' (P ⟪ x ⟫) A (B ⟪ x ⟫) R (S ⟪ x ⟫)
                 (subst-∪⟪⟫⊆ x P⊆B∪S) A∪R (afPx x)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 : {X : Set} (A B R S : Pred[ X ]) →
           𝟙≋ (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 A B R S =
  lemma-02' (B ∪ S) A B R S (λ xs h → h)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym : {X : Set} → (A B R S : Pred[ X ]) →
               𝟙≋ (B ∪ S) → AF (A ∪ R) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym A B R S h1 h2 =
  mono-AF (λ x → B⊎A⊎D×C→A⊎B⊎C×D) (lemma-02 B A S R h1 h2)

-----------------------------------------------------------------------------
-- preparation for lemma-03
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
lemma-03-1 : {X : Set} → (A B R S : Pred[ X ]) → (x : X) →
             R ⟪ x ⟫ ⊆ R → A ⟪ x ⟫ ∪ B ∪ R ⟪ x ⟫ ∩ S ⊆ (A ∪ B ∪ R ∩ S) ⟪ x ⟫
lemma-03-1 A B R S x r xs =
  [ Sum.map inj₁ inj₁ , inj₁ ∘ inj₂ ∘ Sum.map id (Prod.map (r xs) id) ]′

-----------------------------------------------------------------------------
lemma-03-2 : {X : Set} → (R : Pred[ X ]) → (x : X) →
             R · x ⊆ R → R ⟪ x ⟫ ⊆ R
lemma-03-2 R x r xs = [ id , r xs ]′

-----------------------------------------------------------------------------
lemma-03-3 : {X : Set} → (A B R' R S : Pred[ X ]) →
             R ⊆ R' → A ∪ B ∪ R ∩ S ⊆ A ∪ B ∪ R' ∩ S
lemma-03-3 A B R' R S r xs =
  Sum.map id (Sum.map id (Prod.map (r xs) id))

-----------------------------------------------------------------------------
lemma-03-4 : {X : Set} → (A B C D : Pred[ X ]) →
             A ⊆ B ∪ C → C ⊆ D → A ⊆ B ∪ D
lemma-03-4 A B C D A⊆B C⊆D =
  λ xs → Sum.map id (C⊆D xs) ∘  A⊆B xs

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03' : {X : Set} → (P A B R S : Pred[ X ]) →
            (∀ x → R · x ⊆ R) → AF P → P ⊆ A ∪ R → AF (B ∪ S) → 
            AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03' P A B R S Rx⊆R (af-now n) P⊆A∪R AF-B∪S = 
  lemma-02 A B R S
    (λ xs → 𝟙≋-⊆⇒𝟙≋ n P⊆A∪R xs)
    AF-B∪S

lemma-03' P A B R S Rx⊆R (af-later h) P⊆A∪R AF-B∪S = 
  af-later (λ x →
    mono-AF (lemma-03-1 A B R S x (lemma-03-2 R x (Rx⊆R x)))
            (mono-AF -- use R ⟪ x ⟫ ⊆ R, while R ⊆ R ⟪ x ⟫ is trivial
                     (lemma-03-3 (A ⟪ x ⟫) B (R ⟪ x ⟫) R S 
                       (mono-⟪x⟫ R x))
                     (lemma-03' (P ⟪ x ⟫) (A ⟪ x ⟫) B R S
                                Rx⊆R 
                                (h x)
                                 -- A⊆B∪C → C⊆D → A⊆B∪D
                                (lemma-03-4 (P ⟪ x ⟫) (A ⟪ x ⟫) (R ⟪ x ⟫) R
                                  (subst-∪⟪⟫⊆ x P⊆A∪R)
                                  (lemma-03-2 R x (Rx⊆R x)))
                                AF-B∪S)))
  

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 : {X : Set} → (A B R S : Pred[ X ]) →
           (∀ x → R · x ⊆ R) → AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 A B R S h1 h2 =
  lemma-03' (A ∪ R) A B R S h1 h2 ⊆-id

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym : {X : Set} → (A B R S : Pred[ X ]) →
               (∀ x → S · x ⊆ S) →
               AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym A B R S h1 h2 h3 =
  -- show  AF (B ∪ A ∪ S ∩ R)
  mono-AF (λ x → B⊎A⊎D×C→A⊎B⊎C×D) (lemma-03 B A S R h1 h3 h2)

-----------------------------------------------------------------------------
-- preparation for theorem-04
-----------------------------------------------------------------------------
lemma-04-1 :
  {X : Set} (A B R S : Pred[ X ]) (x : X) →
  (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S)) ∪ (R · x ∩ S · x) ⊆ (A ∪ B ∪ R ∩ S) ⟪ x ⟫
lemma-04-1 A B R S x xs =
  [ [ Sum.map inj₁ inj₁ ,
      [ Sum.map (inj₂ ∘ inj₁) (inj₂ ∘ inj₁) , inj₁ ∘ inj₂ ∘ inj₂ ]′ ]′ ,
    inj₂ ∘ inj₂ ∘ inj₂ ]′

-----------------------------------------------------------------------------
lemma-04-2 : {X : Set} (A B R S : Pred[ X ]) (x : X) →
             (A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ (A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ R · x ∩ S · x
             ⊆
             (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ R · x ∩ S · x
lemma-04-2 A B R S x xs =
  [ inj₁ ∘ [ inj₁ , inj₂ ∘ Sum.map inj₁ id ]′ , Sum.map (Sum.map inj₁ id) id ]′

-----------------------------------------------------------------------------
lemma-04-3 : {X : Set} → (A B R S : Pred[ X ]) → (x : X) →
             (A ⟪ x ⟫ ∪ R · x) ∪ B ∪ (R ∩ S) ⊆ (A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ R · x
lemma-04-3 A B R S x xs =
  [ Sum.map inj₁ id , inj₁ ∘ inj₂ ]′

lemma-04-4 : {X : Set} → (A B R S : Pred[ X ]) → (x : X) →
             A ∪ (B ⟪ x ⟫ ∪ S · x) ∪ R ∩ S ⊆ (A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x
lemma-04-4 A B R S x xs =
  [ inj₁ ∘ inj₁ , [ Sum.map (inj₂ ∘ inj₁) id , inj₁ ∘ inj₂ ∘ inj₂ ]′ ]′

lemma-04-5 : {X : Set} → (P A R : Pred[ X ]) → (x : X) →
             P ⊆ A ∪ R → P ⟪ x ⟫ ⊆ (A ⟪ x ⟫ ∪ R · x) ∪ R
lemma-04-5 P A R x P⊆A∪R xs =
  (P ⟪ x ⟫) xs
    ∼⟨ subst-∪⟪⟫⊆ x P⊆A∪R xs ⟩
  (A ⟪ x ⟫ ∪ R ⟪ x ⟫) xs
    ∼⟨ [ inj₁ ∘ inj₁ , [ inj₂ , inj₁ ∘ inj₂ ]′ ]′ ⟩
  ((A ⟪ x ⟫ ∪ R · x) ∪ R) xs
  ∎
  where
  open Related.EquationalReasoning

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04' : {X : Set} → (A B R S P Q : Pred[ X ]) → 
              Ar R → Ar S → P ⊆ A ∪ R → Q ⊆ B ∪ S →
              AF P → AF Q → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04'
  A B R S P Q (ar-now h) ArS P⊆A∪R Q⊆B∪S AfP AfQ = 
    lemma-03 A B R S (proj₁ ∘ h) 
      (mono-AF P⊆A∪R AfP)
      (mono-AF Q⊆B∪S AfQ)
theorem-04'
  A B R S P Q (ar-later h) (ar-now h')
  P⊆A∪R Q⊆B∪S AfP AfQ = 
    lemma-03-sym A B R S (proj₁ ∘ h')
      (mono-AF P⊆A∪R AfP)
      (mono-AF Q⊆B∪S AfQ)
theorem-04' A B R S P Q
  (ar-later h1) (ar-later h2)
  P⊆A∪R Q⊆B∪S (af-now h3) AfQ = 
    lemma-02 A B R S 
      (λ xs → P⊆A∪R xs (h3 xs)) (mono-AF Q⊆B∪S AfQ)
theorem-04' A B R S P Q
  (ar-later h1) (ar-later h2) P⊆A∪R Q⊆B∪S
  (af-later h3) (af-now h4) =
    lemma-02-sym A B R S
      (λ xs → Q⊆B∪S xs (h4 xs))
      (mono-AF P⊆A∪R (af-later h3))
theorem-04' A B R S P Q
  (ar-later h1) (ar-later h2) P⊆A∪R Q⊆B∪S (af-later h3) (af-later h4) =
    af-later (λ x → 
      mono-AF 
        (lemma-04-1 A B R S x)
        (mono-AF
           (lemma-04-2 A B R S x)
           (theorem-04' (A ⟪ x ⟫ ∪ B ∪ R ∩ S)
                        (A ∪ B ⟪ x ⟫ ∪ R ∩ S)
             (R · x) (S · x)
             ((A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ R · x)
             ((A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x)
             -- Ar (R · x)
             (h1 x)
             -- Ar (S · x)
             (h2 x)
             ⊆-id
             ⊆-id
             -- Goal: AF ((A ⟪ x ⟫ ∪ B ∪ R ∩ S) ∪ R · x)
             -- we use AF (A ⟪ x ⟫ ∪ R · x ∪ R) and AF (B ∪ S)
             (mono-AF 
               (lemma-04-3 A B R S x)
               -- AF ((A ⟪ x ⟫ ∪ R · x) ∪ B ∪ R ∩ S)
               (theorem-04' (A ⟪ x ⟫ ∪ R · x) B R S
                 (P ⟪ x ⟫) Q
                 (ar-later h1) (ar-later h2)
                 -- P ⟪ x ⟫ ≋ (A ⟪ x ⟫ ∪ R · x) ∪ R
                 (lemma-04-5 P A R x P⊆A∪R)
                 Q⊆B∪S
                 (h3 x)
                 (af-later h4)))
             -- Goal: AF ((A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x)
             -- we use AF (B ⟪ x ⟫ ∪ S · x ∪ S) and AF (A ∪ R)
             (mono-AF
               (lemma-04-4 A B R S x)
               -- AF (A ∪ S · x ∪ B ⟪ x ⟫ ∪ R ∩ S)
               (theorem-04' A (B ⟪ x ⟫ ∪ S · x) R S
                 P (Q ⟪ x ⟫)
                 (ar-later h1) (ar-later h2)
                 P⊆A∪R
                 (lemma-04-5 Q B S x Q⊆B∪S)
                 (af-later h3)
                 (h4 x))))))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 : {X : Set} → (A B R S : Pred[ X ]) → 
             Ar R → Ar S → AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 A B R S x x' =
  theorem-04' A B R S (A ∪ R) (B ∪ S) x x' ⊆-id ⊆-id

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 : {X : Set} → (R S : Pred[ X ]) → 
               Ar R → Ar S → AF R → AF S → AF (R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 R S h1 h2 h3 h4 = 
  mono-AF
    (λ xs → ⊥⊎⊥⊎A→A)
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
IRT_n n R S h1 h2 = mono-AF (commut-⋀-∩₁ n R S)
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
