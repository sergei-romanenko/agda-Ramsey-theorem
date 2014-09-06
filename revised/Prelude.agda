
module Prelude where

-- Predicates and relations

Pred : (A : Set) → Set₁
Pred A = A → Set

Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- Absurdity

data ⊥ : Set where

⊥E : {A : Set} → ⊥ → A
⊥E ()


¬_ : Set → Set
¬ A = A → ⊥

-- Triviality

data ⊤ : Set where
  tt : ⊤

-- Conjunction and disjunction

infixr 14 _∧_ _∨_

data _∨_ (A : Set) (B : Set) : Set where
  inl : (a : A) → A ∨ B
  inr : (b : B) → A ∨ B

∨E : {A B : Set} → {C : A ∨ B → Set}
   → ((a : A) → C (inl a))  
   → ((b : B) → C (inr b))
   → (p : A ∨ B)
   → C p
∨E ac bc (inl a) = ac a
∨E ac bc (inr b) = bc b



data  _∧_ (A : Set) (B : Set) : Set where
  _,_ : (a : A) → (b : B) → A ∧ B

∧E : {A B : Set} → {C : A ∧ B → Set}
   → ((a : A) → (b : B) → C (a , b))
   → (p : A ∧ B)
   → C p
∧E f (a , b) = f a b


fst : {A B : Set} → A ∧ B → A
fst {A} {B} p = ∧E {A} {B} {λ p' → A} (λ x x' → x) p

snd : {A B : Set} → A ∧ B → B
snd {A} {B} p = ∧E {A} {B} {λ p' → B} (λ a b → b) p


-- equivalence
infix 10 _↔_

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

-----------------------------------------------------------------------------
-- existential quantification
-----------------------------------------------------------------------------
data Σ {A : Set} (F : A → Set) : Set where
     Σ-intro : (x : A) → F x → Σ {A} F

Σ-witness : {A : Set} {F : A → Set} → 
            Σ {A} F → A
Σ-witness (Σ-intro a fa) = a

Σ-elim : {A : Set} {F : A → Set} → 
         (p : Σ {A} F) → F (Σ-witness p)
Σ-elim (Σ-intro a fa) = fa


data Σ₁ {A : Set₁} (F : A → Set) : Set₁ where
  Σ₁-intro : (x : A) → F x → Σ₁ {A} F

-----------------------------------------------------------------------------
-- Some logical facts to be used in IRT.agda
-----------------------------------------------------------------------------

-- commutativity of ∨ and ∧
commut-∨ : {A B : Set} → A ∨ B → B ∨ A
commut-∨ (inl a) = inr a
commut-∨ (inr b) = inl b

commut-∧ : {A B : Set} → A ∧ B → B ∧ A
commut-∧ (a , b) = b , a

-- some associativity laws of ∨
left-assoc-∨ : {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
left-assoc-∨ (inl (inl a)) = inl a
left-assoc-∨ (inl (inr b)) = inr (inl b)
left-assoc-∨ (inr b) = inr (inr b)

right-assoc-∨ : {A B C : Set} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
right-assoc-∨ (inl a) = inl (inl a)
right-assoc-∨ (inr (inl a)) = inl (inr a)
right-assoc-∨ (inr (inr b)) = inr b

-- a few laws to be used later

A∨C→B∨D→A∨B∨C∧D : {A B C D : Set} → A ∨ C → B ∨ D → A ∨ B ∨ (C ∧ D)
A∨C→B∨D→A∨B∨C∧D (inl a) h2 = inl a
A∨C→B∨D→A∨B∨C∧D (inr b) (inl a) = inr (inl a)
A∨C→B∨D→A∨B∨C∧D (inr b) (inr b') = inr (inr (b , b'))

B∨A∨D∧C→A∨B∨C∧D : {A B C D : Set} → B ∨ A ∨ D ∧ C → A ∨ B ∨ C ∧ D
B∨A∨D∧C→A∨B∨C∧D (inl a) = inr (inl a)
B∨A∨D∧C→A∨B∨C∧D (inr (inl a)) = inl a
B∨A∨D∧C→A∨B∨C∧D (inr (inr (a , b))) = inr (inr (b , a))

⊥∨⊥∨A→A : {A : Set} → ⊥ ∨ ⊥ ∨ A → A
⊥∨⊥∨A→A (inl ())
⊥∨⊥∨A→A (inr (inl ()))
⊥∨⊥∨A→A (inr (inr b)) = b

-- Booleans

data Bool : Set where
  true : Bool
  false : Bool

T : Bool → Set
T true = ⊤
T false = ⊥

boolRec : {P : Bool → Set} →
          P true →
          P false →
          (b : Bool) →
          P b
boolRec h1 h2 true = h1
boolRec h1 h2 false = h2

-- Natural numbers

data ℕ : Set where 
     O : ℕ              
     succ : ℕ → ℕ       

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC succ #-}


natrec : 
  {P : Pred ℕ} → 
  P 0 → ((n : ℕ) → P n → P (succ n)) →
  (m : ℕ) → P m 
natrec p0 pS O = p0
natrec p0 pS (succ m) = pS m (natrec p0 pS m)

_<_ : Rel ℕ
O < O = ⊥
O < succ n = ⊤
succ n < O = ⊥
succ m < succ n = m < n

_≤_ : Rel ℕ
O ≤ n = ⊤
succ n ≤ O = ⊥
succ m ≤ succ n = m ≤ n

_+_ : ℕ → ℕ → ℕ
m + O = m
m + succ n = succ (m + n)


-- Lists

infixr 6 _::_

data [_] (X : Set) : Set where
  [] : [ X ]
  _::_ : X → [ X ] → [ X ]

{-# BUILTIN LIST [_] #-}
{-# BUILTIN NIL  []  #-}
{-# BUILTIN CONS _::_ #-}

listrec : {X : Set} → {P : [ X ] → Set} → 
          P [] →
          ((x : X) → (xs : [ X ]) → P xs → P (x :: xs)) →
          (xs : [ X ]) →
          P xs
listrec base ind [] = base
listrec base ind (xs :: xs') = ind xs xs' (listrec base ind xs')

