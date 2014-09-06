
module Prelude where

open import Level public
  renaming (zero to lzero; suc to lsuc)

-- Functions

open import Function public

-- Predicates and relations

open import Relation.Unary public
  using (Pred)

Pred₀ : (A : Set) → Set₁
Pred₀ A = Pred A lzero

open import Relation.Binary public
  using (Rel)

Rel₀ : (A : Set) → Set₁
Rel₀ A = Rel A lzero

-- Absurdity

open import Data.Empty public
  using (⊥; ⊥-elim)

open import Relation.Nullary public
  using (¬_)

-- Triviality

open import Data.Unit public
  using (⊤; tt)

-- Conjunction and disjunction & existential quantification

open import Data.Sum as Sum public
  using (_⊎_; inj₁; inj₂; [_,_]′)

open import Data.Product as Prod public
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; curry; uncurry)


-----------------------------------------------------------------------------
-- Some logical facts to be used in IRT.agda
-----------------------------------------------------------------------------

-- commutativity of ⊎ and ×
commut-⊎ : {A B : Set} → A ⊎ B → B ⊎ A
commut-⊎ (inj₁ a) = inj₂ a
commut-⊎ (inj₂ b) = inj₁ b

commut-× : {A B : Set} → A × B → B × A
commut-× (a , b) = b , a

-- some associativity laws of ⊎
left-assoc-⊎ : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
left-assoc-⊎ (inj₁ (inj₁ a)) = inj₁ a
left-assoc-⊎ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
left-assoc-⊎ (inj₂ b) = inj₂ (inj₂ b)

right-assoc-⊎ : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
right-assoc-⊎ (inj₁ a) = inj₁ (inj₁ a)
right-assoc-⊎ (inj₂ (inj₁ a)) = inj₁ (inj₂ a)
right-assoc-⊎ (inj₂ (inj₂ b)) = inj₂ b

-- a few laws to be used later

A⊎C→B⊎D→A⊎B⊎C×D : {A B C D : Set} → A ⊎ C → B ⊎ D → A ⊎ B ⊎ (C × D)
A⊎C→B⊎D→A⊎B⊎C×D (inj₁ a) h2 = inj₁ a
A⊎C→B⊎D→A⊎B⊎C×D (inj₂ b) (inj₁ a) = inj₂ (inj₁ a)
A⊎C→B⊎D→A⊎B⊎C×D (inj₂ b) (inj₂ b') = inj₂ (inj₂ (b , b'))

B⊎A⊎D×C→A⊎B⊎C×D : {A B C D : Set} → B ⊎ A ⊎ D × C → A ⊎ B ⊎ C × D
B⊎A⊎D×C→A⊎B⊎C×D (inj₁ a) = inj₂ (inj₁ a)
B⊎A⊎D×C→A⊎B⊎C×D (inj₂ (inj₁ a)) = inj₁ a
B⊎A⊎D×C→A⊎B⊎C×D (inj₂ (inj₂ (a , b))) = inj₂ (inj₂ (b , a))

⊥⊎⊥⊎A→A : {A : Set} → ⊥ ⊎ ⊥ ⊎ A → A
⊥⊎⊥⊎A→A (inj₁ ())
⊥⊎⊥⊎A→A (inj₂ (inj₁ ()))
⊥⊎⊥⊎A→A (inj₂ (inj₂ b)) = b

-- Booleans

open import Data.Bool public
  using (Bool; true; false)

-- Natural numbers

open import Data.Nat public
  using (ℕ; zero; suc)

-- Lists

open import Data.List public
  using ([]; _∷_) renaming (List to [_])
