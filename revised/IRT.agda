
module IRT where

open import Data.Sum as Sum
  using ()

open import Prelude

open import ListPredicate


-----------------------------------------------------------------------------
-- n-ary relations
-----------------------------------------------------------------------------
nRel : (n : ℕ) → Set → Set₁
nRel 0 A = Set
nRel (suc n) A = A → nRel n A


-- conversion from n-ary relations to list n-prefix predicates

fromNRel : {X : Set} → (n : ℕ) → nRel n X → Pred₀ [ X ]
fromNRel zero R xs = R
fromNRel (suc n) R [] = ⊥
fromNRel (suc n) R (x ∷ xs) = fromNRel n (R x) xs

-- intersection of n-ary relations

infixr 14 _∩_

_∩_ : {A : Set} → {n : ℕ} → (R S : nRel n A) → nRel n A
_∩_ {A} {zero} R S = R × S
_∩_ {A} {suc n} R S = λ a → (R a ∩ S a) 


-- ∩ commutes with ⨅

commut-∩-⨅₁ : {X : Set} → (n : ℕ) → (R S : nRel n X) →
              fromNRel n R ⨅ fromNRel n S ⊆ fromNRel n (R ∩ S)
commut-∩-⨅₁ zero R S xs (a , b) = a , b
commut-∩-⨅₁ (suc n) R S [] (a , b) = b
commut-∩-⨅₁ (suc n) R S (x ∷ xs) (a , b) = 
  commut-∩-⨅₁ n (R x) (S x) xs (a , b)

commut-∩-⨅₂ : {X : Set} → (n : ℕ) → (R S : nRel n X) →
              fromNRel n (R ∩ S) ⊆ fromNRel n R ⨅ fromNRel n S
commut-∩-⨅₂ zero R S xs h = h
commut-∩-⨅₂ (suc n) R S [] h = h , h
commut-∩-⨅₂ (suc n) R S (x ∷ xs) h =
  commut-∩-⨅₂ n (R x) (S x) xs h

commut-∩-⨅ : {X : Set} → (n : ℕ) → (R S : nRel n X) →
             fromNRel n R ⨅ fromNRel n S ≡ fromNRel n (R ∩ S)
commut-∩-⨅ n R S = (λ x → commut-∩-⨅₁ n R S x) , λ x → commut-∩-⨅₂ n R S x


-----------------------------------------------------------------------------
-- Ar(a), for a : D, called "arity". Ar is a bar for the property of
-- being constant. For instance, a predicate A expressing that its
-- argument has some element of some given property, for instance
-- being equal to one, is not Ar. There is no point where A becomes
-- constant.
-----------------------------------------------------------------------------
data Ar {X : Set} (A : Pred₀ [ X ]) : Set where
  leafAr : (∀ x → (A · x) ≡ A) → Ar A
  indAr : (∀ x → Ar (A · x)) → Ar A


-- The list predicate derived from an n-ary relation is Ar,
-- since it becomes constant when all the n arguments have been provided.

fromNRel→Ar : {X : Set} → (n : ℕ) →
              (R : nRel n X) → Ar(fromNRel n R)
fromNRel→Ar zero R = leafAr (λ x → (λ x' x0 → x0) , λ x' x0 → x0)
fromNRel→Ar (suc n) R = indAr (λ x' → fromNRel→Ar n (R x'))


-----------------------------------------------------------------------------
-- Almost full relations. Like a Well-Quasi ordering, without transitivity
-----------------------------------------------------------------------------
data AF {X : Set} (A : Pred₀ [ X ]) : Set where
  leafAF : True A → AF A
  indAF : ((x : X) → AF(A ⟪ x ⟫)) → AF A


-- By P is monotone, we mean: P(A) → (A → B) → P(B)
-- So IRT.lemma-01 could be formulated as AF being monotone

monotone : {X : Set} → (Pred₀ X → Set) → Set₁
monotone {X} P = (A B : Pred₀ X) →
                 ((x : X) → A x → B x) → (P A → P B)

-----------------------------------------------------------------------------
-- Monotonicity of AF
--
-- As stated in Coquand's note:
-- lemma-01 : {X : Set} → (A B : Pred₀ [ X ]) → A ⊆ B → AF A → AF B
-----------------------------------------------------------------------------
lemma-01 : {X : Set} → monotone (AF {X})
-----------------------------------------------------------------------------
lemma-01 A B hA⊆B (leafAF p) =
  leafAF (λ xs → hA⊆B xs (p xs))
lemma-01 A B hA⊆B (indAF f) = 
  indAF (λ x → lemma-01 (A ⟪ x ⟫) (B ⟪ x ⟫)
                        (monotone-⟪x⟫ A B x hA⊆B) (f x))

-----------------------------------------------------------------------------
-- preparation for lemma-02
-----------------------------------------------------------------------------
lemma-02-1-1 : {X : Set} → (A B R S : Pred₀ [ X ]) → 
               True (A ⨆ R) → B ⨆ S ⊆ A ⨆ B ⨆ (R ⨅ S)
lemma-02-1-1 A B R S h1 h2 h3 = A⊎C→B⊎D→A⊎B⊎C×D (h1 h2) h3

-----------------------------------------------------------------------------
lemma-02-1 : {X : Set} → (A B R S : Pred₀ [ X ]) → 
             True(A ⨆ R) → True(B ⨆ S) → True(A ⨆ B ⨆ (R ⨅ S))
lemma-02-1 A B R S h1 h2 = 
  λ xs →
       lemma-02-1-1 
         (λ ys → A xs) (λ ys → B xs) (λ ys → R xs) (λ ys → S xs)
         (λ xs' → h1 xs) xs (h2 xs)

-----------------------------------------------------------------------------
lemma-02-2-2 : {X : Set} → (A R S : Pred₀ [ X ]) → (x : X) →
               True(A · x ⨆ R · x) →
               R ⨅ S · x ⊆ A · x ⨆ (R · x ⨅ S · x)
lemma-02-2-2 A R S x h1 xs (a , b) = 
  Sum.map id (flip _,_ b) (h1 xs)

-- N.B. most of the proofs below who are written with
-- pattern-matching, have been auto-generated (with some manual
-- renaming) by Agda's "auto" facility, by Fredrik Lindblad
-----------------------------------------------------------------------------
lemma-02-2-1-1 :  {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
                  A · x ⨆ (R · x ⨅ S · x) ⊆ (A ⨆ B ⨆ (R ⨅ S))⟪ x ⟫
lemma-02-2-1-1 A B R S x xs (inj₁ a) = inj₂ (inj₁ a)
lemma-02-2-1-1 A B R S x xs (inj₂ b) = inj₂ (inj₂ (inj₂ b))

-----------------------------------------------------------------------------
lemma-02-2-1 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
               R ⨅ S · x ⊆ A · x ⨆ (R · x ⨅ S · x) →
               A ⨆ B ⟪ x ⟫ ⨆ (R ⨅ S ⟪ x ⟫) ⊆ (A ⨆ B ⨆ (R ⨅ S))⟪ x ⟫
lemma-02-2-1 A B R S x h1 xs (inj₁ a) = inj₁ (inj₁ a)
lemma-02-2-1 A B R S x h1 xs (inj₂ (inj₁ (inj₁ a))) = inj₁ (inj₂ (inj₁ a))
lemma-02-2-1 A B R S x h1 xs (inj₂ (inj₁ (inj₂ b))) = inj₂ (inj₂ (inj₁ b))
lemma-02-2-1 A B R S x h1 xs (inj₂ (inj₂ (a , inj₁ a'))) =
  inj₁ (inj₂ (inj₂ (a , a')))
lemma-02-2-1 A B R S x h1 xs (inj₂ (inj₂ (a , inj₂ b))) =
  lemma-02-2-1-1 A B R S x xs (h1 xs (a , b))

-----------------------------------------------------------------------------
lemma-02-2 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
             True(A ⨆ R) →
             A ⨆ B ⟪ x ⟫ ⨆ (R ⨅ S ⟪ x ⟫) ⊆ (A ⨆ B ⨆ (R ⨅ S))⟪ x ⟫
lemma-02-2 A B R S x h1 xs h2 =
  lemma-02-2-1 A B R S x 
    (lemma-02-2-2 A R S x (λ xs' → h1 (x ∷ xs'))) xs h2


-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02' : {X : Set} → (P A B R S : Pred₀ [ X ]) →
            True(A ⨆ R) → AF P → P ≡ B ⨆ S → AF(A ⨆ B ⨆ (R ⨅ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02' P A B R S A⨆R (leafAF h) P≡B⨆S = 
  leafAF (λ xs → 
    lemma-02-1
      (λ ys → A xs) (λ ys → B xs) (λ ys → R xs) (λ ys → S xs)
      (λ ys → A⨆R xs)
      (λ ys → uncurry (λ a b → a xs (h xs)) P≡B⨆S)
      xs)

lemma-02' P A B R S A⨆R (indAF afPx) P≡B⨆S = 
  indAF (λ x → 
    lemma-01
      (A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S ⟪ x ⟫) (((A ⨆ B ⨆ R ⨅ S) ⟪ x ⟫)) 
      (lemma-02-2 A B R S x A⨆R)
      (lemma-02' (P ⟪ x ⟫) A  (B ⟪ x ⟫) R (S ⟪ x ⟫)
                 A⨆R 
                 (afPx x)
                 (distrib-subst⨆≡⟪x⟫ P B S x P≡B⨆S)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 : {X : Set} → (A B R S : Pred₀ [ X ]) →
           True(A ⨆ R) → AF(B ⨆ S) → AF(A ⨆ B ⨆ (R ⨅ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02 = λ A B R S h1 h2 →
               lemma-02' (B ⨆ S) A B R S h1 h2
               (refl≡ (B ⨆ S))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym : {X : Set} → (A B R S : Pred₀ [ X ]) →
               True(B ⨆ S) → AF(A ⨆ R) → AF(A ⨆ B ⨆ (R ⨅ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02-sym A B R S h1 h2 =
  lemma-01 (B ⨆ A ⨆ S ⨅ R) (A ⨆ B ⨆ R ⨅ S)
    (λ x → B⊎A⊎D×C→A⊎B⊎C×D)
    (lemma-02 B A S R h1 h2)

-----------------------------------------------------------------------------
-- preparation for lemma-03
-----------------------------------------------------------------------------
lemma-03-1 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
             R ⟪ x ⟫ ≡ R → A ⟪ x ⟫ ⨆ B ⨆ R ⟪ x ⟫ ⨅ S ⊆ (A ⨆ B ⨆ R ⨅ S) ⟪ x ⟫
lemma-03-1 A B R S x (a , b) xs (inj₁ (inj₁ a')) = inj₁ (inj₁ a')
lemma-03-1 A B R S x (a , b) xs (inj₁ (inj₂ b')) = inj₂ (inj₁ b')
lemma-03-1 A B R S x (a , b) xs (inj₂ (inj₁ a')) = inj₁ (inj₂ (inj₁ a'))
lemma-03-1 A B R S x (a , b) xs (inj₂ (inj₂ (a' , b'))) =
  inj₁ (inj₂ (inj₂ (a xs a' , b')))

-----------------------------------------------------------------------------
lemma-03-2 : {X : Set} → (R : Pred₀ [ X ]) → (x : X) →
             R · x ≡ R → R ⟪ x ⟫ ≡ R
lemma-03-2 R x (a , b) =
  (λ xs → a xs ∘ [ b xs , id ]′) , (λ xs → inj₁)

lemma-03-3 : {X : Set} → (A B R' R S : Pred₀ [ X ]) → 
             R' ≡ R → A ⨆ B ⨆ R ⨅ S ⊆ A ⨆ B ⨆ R' ⨅ S
lemma-03-3 A B R' R S (h1 , h2) xs (inj₁ a) = inj₁ a
lemma-03-3 A B R' R S (h1 , h2) xs (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
lemma-03-3 A B R' R S (h1 , h2) xs (inj₂ (inj₂ (a , b))) =
  inj₂ (inj₂ (h2 xs a , b))

-----------------------------------------------------------------------------
lemma-03-4 : {X : Set} → (A B C D : Pred₀ [ X ]) →
             A ≡ B ⨆ C → C ≡ D → A ≡ B ⨆ D
lemma-03-4 A B C D (a , b) (a' , b') =
  (λ xs → Sum.map id (a' xs) ∘ a xs) , (λ xs → b xs ∘ Sum.map id (b' xs))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03' : {X : Set} → (P A B R S : Pred₀ [ X ]) →
            (∀ x → R · x ≡ R) → AF(P) → P ≡ A ⨆ R → AF(B ⨆ S) → 
            AF(A ⨆ B ⨆ R ⨅ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03' P A B R S Rx≡R (leafAF h) h' AF-B⨆S = 
  lemma-02 A B R S
    (λ xs → proj₂ ((h xs) , uncurry (λ a b → a xs (h xs)) h'))
    AF-B⨆S

lemma-03' P A B R S Rx≡R (indAF h) P≡A⨆R AF-B⨆S = 
  indAF (λ x →
    lemma-01 (A ⟪ x ⟫ ⨆ B ⨆ R ⟪ x ⟫ ⨅ S) 
             (((A ⨆ B ⨆ R ⨅ S) ⟪ x ⟫)) 
             (lemma-03-1 A B R S x (lemma-03-2 R x (Rx≡R x)))
             (lemma-01 (A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) (A ⟪ x ⟫ ⨆ B ⨆ R ⟪ x ⟫ ⨅ S)
                       -- use R ⟪ x ⟫ ≡ R
                       (lemma-03-3 (A ⟪ x ⟫) B (R ⟪ x ⟫) R S 
                         (lemma-03-2 R x (Rx≡R x)))
                       (lemma-03' (P ⟪ x ⟫) (A ⟪ x ⟫) B R S
                                 Rx≡R 
                                 (h x)
                                 -- A≡B⨆C → C≡D → A≡B⨆D
                                 (lemma-03-4 (P ⟪ x ⟫) (A ⟪ x ⟫) (R ⟪ x ⟫) R
                                   (distrib-subst⨆≡⟪x⟫ P A R x P≡A⨆R) 
                                   (lemma-03-2 R x (Rx≡R x)))
                                 AF-B⨆S)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 : {X : Set} → (A B R S : Pred₀ [ X ]) →
           (∀ x → R · x ≡ R) → AF(A ⨆ R) → AF(B ⨆ S) → AF(A ⨆ B ⨆ R ⨅ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03 = λ A B R S h1 h2 →
                lemma-03' (A ⨆ R) A B R S h1 h2
                (refl≡ (A ⨆ R))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym : {X : Set} → (A B R S : Pred₀ [ X ]) →
               (∀ x → S · x ≡ S) → AF(A ⨆ R) → AF(B ⨆ S) → AF(A ⨆ B ⨆ R ⨅ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-03-sym A B R S h1 h2 h3 =
  -- show  AF(B ⨆ A ⨆ S ⨅ R)
  lemma-01 (B ⨆ A ⨆ S ⨅ R) (A ⨆ B ⨆ R ⨅ S)
    (λ x → B⊎A⊎D×C→A⊎B⊎C×D)
    (lemma-03 B A S R h1 h3 h2)

-----------------------------------------------------------------------------
-- preparation for theorem-04
-----------------------------------------------------------------------------
lemma-04-1 :
  {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
  (A ⟪ x ⟫ ⨆ B ⟪ x ⟫ ⨆ (R ⨅ S)) ⨆ (R · x ⨅ S · x) ⊆ (A ⨆ B ⨆ R ⨅ S) ⟪ x ⟫
lemma-04-1 A B R S x xs (inj₁ (inj₁ (inj₁ a))) = inj₁ (inj₁ a)
lemma-04-1 A B R S x xs (inj₁ (inj₁ (inj₂ b))) = inj₂ (inj₁ b)
lemma-04-1 A B R S x xs (inj₁ (inj₂ (inj₁ (inj₁ a)))) = inj₁ (inj₂ (inj₁ a))
lemma-04-1 A B R S x xs (inj₁ (inj₂ (inj₁ (inj₂ b)))) = inj₂ (inj₂ (inj₁ b))
lemma-04-1 A B R S x xs (inj₁ (inj₂ (inj₂ b))) = inj₁ (inj₂ (inj₂ b))
lemma-04-1 A B R S x xs (inj₂ b) = inj₂ (inj₂ (inj₂ b))

-----------------------------------------------------------------------------
lemma-04-2 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
             (A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ (A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ R · x ⨅ S · x
             ⊆
             (A ⟪ x ⟫ ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ R · x ⨅ S · x
lemma-04-2 A B R S x xs (inj₁ (inj₁ a)) = inj₁ (inj₁ a)
lemma-04-2 A B R S x xs (inj₁ (inj₂ (inj₁ a))) = inj₁ (inj₂ (inj₁ (inj₁ a)))
lemma-04-2 A B R S x xs (inj₁ (inj₂ (inj₂ b))) = inj₁ (inj₂ (inj₂ b))
lemma-04-2 A B R S x xs (inj₂ (inj₁ (inj₁ a))) = inj₁ (inj₁ (inj₁ a))
lemma-04-2 A B R S x xs (inj₂ (inj₁ (inj₂ b))) = inj₁ (inj₂ b)
lemma-04-2 A B R S x xs (inj₂ (inj₂ b)) = inj₂ b

-----------------------------------------------------------------------------
lemma-04-3 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
             (A ⟪ x ⟫ ⨆ R · x) ⨆ B ⨆ (R ⨅ S) ⊆ (A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ R · x
lemma-04-3 A B R S x xs (inj₁ (inj₁ a)) = inj₁ (inj₁ a)
lemma-04-3 A B R S x xs (inj₁ (inj₂ b)) = inj₂ b
lemma-04-3 A B R S x xs (inj₂ b) = inj₁ (inj₂ b)

lemma-04-4 : {X : Set} → (A B R S : Pred₀ [ X ]) → (x : X) →
             A ⨆ (B ⟪ x ⟫ ⨆ S · x) ⨆ R ⨅ S ⊆ (A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ S · x
lemma-04-4 A B R S x xs (inj₁ a) = inj₁ (inj₁ a)
lemma-04-4 A B R S x xs (inj₂ (inj₁ (inj₁ a))) = inj₁ (inj₂ (inj₁ a))
lemma-04-4 A B R S x xs (inj₂ (inj₁ (inj₂ b))) = inj₂ b
lemma-04-4 A B R S x xs (inj₂ (inj₂ b)) = inj₁ (inj₂ (inj₂ b))

lemma-04-5 : {X : Set} → (P A R : Pred₀ [ X ]) → (x : X) →
             P ≡ A ⨆ R → P ⟪ x ⟫ ≡ (A ⟪ x ⟫ ⨆ R · x) ⨆ R
lemma-04-5 P A R x P≡A⨆R = 
   (trans≡ (P ⟪ x ⟫) (A ⟪ x ⟫ ⨆ R ⟪ x ⟫) ((A ⟪ x ⟫ ⨆ R · x) ⨆ R)
                      (distrib-subst⨆≡⟪x⟫ P A R x P≡A⨆R)
                      (trans≡ (A ⟪ x ⟫ ⨆ R ⟪ x ⟫)
                               (A ⟪ x ⟫ ⨆ (R · x ⨆ R))
                               ((A ⟪ x ⟫ ⨆ R · x) ⨆ R)
                        (right-disj-subst (A ⟪ x ⟫)
                           (R ⟪ x ⟫) (R · x ⨆ R)
                           ((λ _ → commut-⊎) , λ _ → commut-⊎))
                        ((λ _ → right-assoc-⊎) , λ _ → left-assoc-⊎)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04' : {X : Set} → (A B R S P Q : Pred₀ [ X ]) → 
              Ar R → Ar S → P ≡ A ⨆ R → Q ≡ B ⨆ S →
              AF P → AF Q → AF(A ⨆ B ⨆ (R ⨅ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04'
  A B R S P Q (leafAr h) ArS (P⊆A⨆R , A⨆R⊆P) (Q⊆B⨆S , B⨆S⊆Q) AfP AfQ = 
    lemma-03 A B R S h 
      (lemma-01 P (A ⨆ R) P⊆A⨆R AfP)
      (lemma-01 Q (B ⨆ S) Q⊆B⨆S AfQ)
theorem-04'
  A B R S P Q (indAr h) (leafAr h')
  (P⊆A⨆R , A⨆R⊆P) (Q⊆B⨆S , B⨆S⊆Q) AfP AfQ = 
    lemma-03-sym A B R S h'
      (lemma-01 P (A ⨆ R) P⊆A⨆R AfP)
      (lemma-01 Q (B ⨆ S) Q⊆B⨆S AfQ)
theorem-04' A B R S P Q
  (indAr h1) (indAr h2) (P⊆A⨆R , A⨆R⊆P) (Q⊆B⨆S , B⨆S⊆Q) (leafAF h3) AfQ = 
    lemma-02 A B R S 
      (λ xs → P⊆A⨆R xs (h3 xs)) (lemma-01 Q (B ⨆ S) Q⊆B⨆S AfQ)
theorem-04' A B R S P Q
  (indAr h1) (indAr h2) (P⊆A⨆R , A⨆R⊆P) (Q⊆B⨆S , B⨆S⊆Q)
  (indAF h3) (leafAF h4) =
    lemma-02-sym A B R S
      (λ xs → Q⊆B⨆S xs (h4 xs))
      (lemma-01 P (A ⨆ R) P⊆A⨆R (indAF h3))
theorem-04' A B R S P Q
  (indAr h1) (indAr h2) P≡A⨆R Q≡B⨆S (indAF h3) (indAF h4) =
    indAF (λ x → 
      lemma-01 
        ((A ⟪ x ⟫ ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ (R · x ⨅ S · x))
          ((A ⨆ B ⨆ R ⨅ S) ⟪ x ⟫)
        (lemma-04-1 A B R S x)
        (lemma-01
           ((A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆
            (A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ R · x ⨅ S · x)
           ((A ⟪ x ⟫ ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ R · x ⨅ S · x)
           (lemma-04-2 A B R S x)
           (theorem-04' (A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S)
                        (A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S)
             (R · x) (S · x)
             ((A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ R · x)
             ((A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ S · x)
             -- Ar(R · x)
             (h1 x)
             -- Ar(S · x)
             (h2 x)
             (refl≡ ((A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ R · x))
             (refl≡ ((A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ S · x))
             -- Goal: AF ((A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ R · x)
             -- we use AF(A ⟪ x ⟫ ⨆ R · x ⨆ R) and AF(B ⨆ S)
             (lemma-01 
               ((A ⟪ x ⟫ ⨆ R · x) ⨆ B ⨆ (R ⨅ S))
               ((A ⟪ x ⟫ ⨆ B ⨆ R ⨅ S) ⨆ R · x)
               (lemma-04-3 A B R S x)
               -- AF ((A ⟪ x ⟫ ⨆ R · x) ⨆ B ⨆ R ⨅ S)
               (theorem-04' (A ⟪ x ⟫ ⨆ R · x) B R S
                 (P ⟪ x ⟫) Q
                 (indAr h1) (indAr h2)
                 -- P ⟪ x ⟫ ≡ (A ⟪ x ⟫ ⨆ R · x) ⨆ R
                 (lemma-04-5 P A R x P≡A⨆R)
                 Q≡B⨆S
                 (h3 x)
                 (indAF h4)))
             -- Goal: AF ((A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ S · x)
             -- we use AF(B ⟪ x ⟫ ⨆ S · x ⨆ S) and AF(A ⨆ R)
             (lemma-01
               (A ⨆ (B ⟪ x ⟫ ⨆ S · x) ⨆ R ⨅ S)
               ((A ⨆ B ⟪ x ⟫ ⨆ R ⨅ S) ⨆ S · x)
               (lemma-04-4 A B R S x)
               -- AF (A ⨆ S · x ⨆ B ⟪ x ⟫ ⨆ R ⨅ S)
               (theorem-04' A (B ⟪ x ⟫ ⨆ S · x) R S
                 P (Q ⟪ x ⟫)
                 (indAr h1) (indAr h2)
                 P≡A⨆R
                 (lemma-04-5 Q B S x Q≡B⨆S)
                 (indAF h3)
                 (h4 x))))))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 : {X : Set} → (A B R S : Pred₀ [ X ]) → 
             Ar R → Ar S → AF(A ⨆ R) → AF(B ⨆ S) → AF(A ⨆ B ⨆ (R ⨅ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 = λ A B R S x x' →
                 theorem-04' A B R S (A ⨆ R) (B ⨆ S) x x'
                 (refl≡ (A ⨆ R)) (refl≡ (B ⨆ S))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 : {X : Set} → (R S : Pred₀ [ X ]) → 
               Ar R → Ar S → AF R → AF S → AF(R ⨅ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 R S h1 h2 h3 h4 = 
  lemma-01 (₀ ⨆ ₀ ⨆ R ⨅ S) (R ⨅ S)
    (λ xs → ⊥⊎⊥⊎A→A)
    (theorem-04 ₀ ₀ R S
      h1 h2 
      (lemma-01 R (₀ ⨆ R) (λ xs h → inj₂ h) h3)
      (lemma-01 S (₀ ⨆ S) (λ xs h → inj₂ h) h4))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- The n-ary intuitionistic Ramsey Theorem
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n : {X : Set} → (n : ℕ) → (R S : nRel n X) →
        AF(fromNRel n R) → AF(fromNRel n S) → AF(fromNRel n (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n n R S h1 h2 = lemma-01 (fromNRel n R ⨅ fromNRel n S)
                             (fromNRel n (R ∩ S))
                             (commut-∩-⨅₁ n R S)
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

mapSI : {X : Set} → (ℕ → X) → StrictIncSeq → [ X ]
mapSI f SIε = []
mapSI f (SI+1 s) = mapSI (λ n → f (suc n)) s
mapSI f (SI0+1 s) = (f 0) ∷ (mapSI (λ n → f (suc n)) s)

-- Any infinite sequence must have a finite subsequence satisfying P
-- s is a strictly increasing sequence of positions in α
Unavoidable : {X : Set} → (P : Pred₀ [ X ]) → Set
Unavoidable {X} P =
  (α : ℕ → X) → ∃ (λ (s : StrictIncSeq) → P (mapSI α s))

-- If P is almost full, then P is unavoidable
AF-Unavoidable : {X : Set} → (P : Pred₀ [ X ]) →
                 AF P  → Unavoidable P
AF-Unavoidable P (leafAF h) f = SIε , h []
AF-Unavoidable P (indAF x→AfP⟪x⟫) f = 
  let rem0 : ∃ (λ s → (P ⟪ f zero ⟫) (mapSI (λ x → f (suc x)) s))
      rem0 = AF-Unavoidable (P ⟪ f 0 ⟫) (x→AfP⟪x⟫ (f 0)) (λ x → f (suc x))
      s0 : StrictIncSeq
      s0 = proj₁ rem0
      p : (P ⟪ f 0 ⟫) (mapSI (λ x → f (suc x)) s0)
      p = proj₂ rem0
  in (∃ λ s → P (mapSI f s)) ∋ [ _,_ (SI+1 s0) , _,_ (SI0+1 s0) ]′ p
