module IRT where

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Data.Nat
  using (ℕ; zero; suc)
open import Data.List
  using (List; []; _∷_)
open import Data.Sum as Sum
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

open import ListPredicate

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
-- lemma-02
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02₀ : {X : Set} {P A B R S : Pred[ X ]} → P ⊆ B ∪ S →
            𝟙⊆ (A ∪ R) → AF P → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
lemma-02₀ {X} {P} {A} {B} {R} {S} P⊆B∪S 𝟙⊆A∪R (af-now 𝟙⊆P) =
  af-now (flip 𝟙⊆A∪B∪[R∩S] tt)
  where
  open ⊆-Reasoning

  𝟙⊆A∪B∪[R∩S] = begin
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

lemma-02₀ {X} {P} {A} {B} {R} {S} P⊆B∪S 𝟙⊆A∪R (af-later afP⟪⟫) = 
  af-later (λ x → 
    mono-AF
      (A∪B⟪⟫∪[R∩S⟪⟫]⊆[A∪B∪[R∩S]]⟪⟫ x)
      (lemma-02₀ (P⟪⟫⊆B⟪⟫∪S⟪⟫ x) 𝟙⊆A∪R (afP⟪⟫ x)))
  where
  open ⊆-Reasoning

  R∩S·⊆A·∪R·∩S· = λ x → begin
    R ∩ S · x
      ⊆⟨ (λ xs → proj₂) ⟩
    S · x
      ⊆⟨ _,_ ∘ 𝟙⊆A∪R ∘ _∷_ x ⟩
    (A · x ∪ R · x) ∩ S · x
      ⊆⟨ [A∪B]∩C⊆A∩C∪B∩C ⟩
    (A · x ∩ S · x) ∪ (R · x ∩ S · x)
      ⊆⟨ (λ xs → [ inj₁ ∘ proj₁ , inj₂ ]′) ⟩
    A · x ∪ (R · x ∩ S · x)
    ∎

  A∪B⟪⟫∪[R∩S⟪⟫]⊆[A∪B∪[R∩S]]⟪⟫ = λ x → begin
    A ∪ B ⟪ x ⟫ ∪ (R ∩ S ⟪ x ⟫)
      ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ A∩[B∪C]⊆A∩B∪A∩C ⟩
    A ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (R ∩ S · x)
      ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ mono-∪ʳ $ R∩S·⊆A·∪R·∩S· x ⟩
    A ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (A · x ∪ (R · x ∩ S · x))
      ⊆⟨ A∪C∪D∪B∪E⊆[A∪B]∪C∪D∪E ⟩
    (A ∪ A · x) ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (R · x ∩ S · x)
      ≋⟨⟩
    A ⟪ x ⟫ ∪ (B ⟪ x ⟫ ∪ (R ∩ S) ⟪ x ⟫)
      ⊆⟨ mono-∪ʳ $ distrib-∪⟪⟫⊇ ⟩
    A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊇  ⟩
    (A ∪ B ∪ (R ∩ S)) ⟪ x ⟫
    ∎

  P⟪⟫⊆B⟪⟫∪S⟪⟫ = λ x → begin
    P ⟪ x ⟫
      ⊆⟨ mono-⟪⟫ x P⊆B∪S ⟩
    (B ∪ S) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊆ B S x ⟩
    B ⟪ x ⟫ ∪ S ⟪ x ⟫
    ∎

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

  R⟪⟫∩S⊆[R∩S]⟪⟫ : ∀ x → R ⟪ x ⟫ ∩ S ⊆ (R ∩ S) ⟪ x ⟫

  R⟪⟫∩S⊆[R∩S]⟪⟫ = λ x → begin
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

  A⟪⟫∪B∪R∩S⊆[A∪B∪R∩S]⟪⟫ : ∀ x → A ⟪ x ⟫ ∪ B ∪ R ∩ S ⊆ (A ∪ B ∪ R ∩ S) ⟪ x ⟫
  A⟪⟫∪B∪R∩S⊆[A∪B∪R∩S]⟪⟫ = λ x → begin
    A ⟪ x ⟫ ∪ B ∪ R ∩ S
      ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ mono-∩ˡ $ mono-⟪x⟫ ⟩
    A ⟪ x ⟫ ∪ B ∪ R ⟪ x ⟫ ∩ S
      ⊆⟨ mono-∪ʳ $ mono-∪ mono-⟪x⟫ (R⟪⟫∩S⊆[R∩S]⟪⟫ x) ⟩
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S) ⟪ x ⟫
      ⊆⟨ mono-∪ʳ $ distrib-∪⟪⟫⊇ ⟩
    A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊇ ⟩
    (A ∪ B ∪ R ∩ S) ⟪ x ⟫
    ∎

  AF-A⟪⟫∪B∪R∩S : ∀ x → AF (A ⟪ x ⟫ ∪ B ∪ R ∩ S)
  AF-A⟪⟫∪B∪R∩S x =
    lemma-03₀ R·⊆R
      (begin P ⟪ x ⟫ ⊆⟨ P⟪⟫⊆A⟪⟫∪R x ⟩ A ⟪ x ⟫ ∪ R ∎)
      (afP⟪⟫ x) afB∪S

  AF-[A∪B∪R∩S]⟪⟫ : ∀ x → AF ((A ∪ B ∪ R ∩ S) ⟪ x ⟫ )
  AF-[A∪B∪R∩S]⟪⟫ x =
    mono-AF
      (begin
        (A ⟪ x ⟫ ∪ B ∪ R ∩ S)
          ⊆⟨ A⟪⟫∪B∪R∩S⊆[A∪B∪R∩S]⟪⟫ x ⟩
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
-----------------------------------------------------------------------------
theorem-04₀ : {X : Set} {A B R S P Q : Pred[ X ]} → 
              Ar R → Ar S → P ⊆ A ∪ R → Q ⊆ B ∪ S →
              AF P → AF Q → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04₀ (ar-now R·⊆R) arS P⊆A∪R Q⊆B∪S afP afQ = 
    lemma-03 R·⊆R 
      (mono-AF P⊆A∪R afP)
      (mono-AF Q⊆B∪S afQ)

theorem-04₀ (ar-later arR·) (ar-now S·⊆S)
  P⊆A∪R Q⊆B∪S afP afQ = 
    lemma-03-sym S·⊆S
      (mono-AF P⊆A∪R afP)
      (mono-AF Q⊆B∪S afQ)

theorem-04₀ (ar-later arR·) (ar-later arS·) P⊆A∪R Q⊆B∪S (af-now 𝟙⊆P) afQ = 
    lemma-02 (mono-𝟙⊆ P⊆A∪R 𝟙⊆P) (mono-AF Q⊆B∪S afQ)

theorem-04₀
  (ar-later arR·) (ar-later arS·) P⊆A∪R Q⊆B∪S (af-later afP·) (af-now 𝟙⊆Q) =
    lemma-02-sym
      (λ xs → Q⊆B∪S xs (𝟙⊆Q xs))
      (mono-AF P⊆A∪R (af-later afP·))

theorem-04₀ {X} {A} {B} {R} {S} {P} {Q}
  (ar-later arR·) (ar-later arS·) P⊆A∪R Q⊆B∪S (af-later afP·) (af-later afQ·) =
    af-later (λ x →
      AF ((A ∪ B ∪ (R ∩ S)) ∪ A · x ∪ B · x ∪ (R · x ∩ S · x))
      ∋
      mono-AF 
        (zip-A⟪⟫B⟪⟫RS x)
        (mono-AF
           (zip-ABCD (R ∩ S) (R · x ∩ S · x) x)
           (AF ((A ⟪ x ⟫ ∪ B ∪ (R ∩ S)) ∪ (A ∪ B ⟪ x ⟫ ∪ (R ∩ S)) ∪
                   (R · x ∩ S · x))
           ∋ 
           theorem-04₀ (arR· x) (arS· x) ⊆-refl ⊆-refl
             (AF ((A ⟪ x ⟫ ∪ B ∪ (R ∩ S)) ∪ R · x) ∋
             mono-AF 
               (move-A⟪⟫BRS x)
               (AF ((A ⟪ x ⟫ ∪ R · x) ∪ B ∪ (R ∩ S))
                 ∋ theorem-04₀ (ar-later arR·) (ar-later arS·)
                               (use-⊆∪ x P⊆A∪R) Q⊆B∪S
                               (afP· x) (af-later afQ·)))
             (AF ((A ∪ B ⟪ x ⟫ ∪ (R ∩ S)) ∪ S · x) ∋
             mono-AF
               (move-AB⟪⟫RS x)
               (AF (A ∪ (B ⟪ x ⟫ ∪ S · x) ∪ (R ∩ S))
                 ∋ theorem-04₀ (ar-later arR·) (ar-later arS·)
                               P⊆A∪R (use-⊆∪ x Q⊆B∪S)
                               (af-later afP·) (afQ· x))))))
  where
  open ⊆-Reasoning

  zip-A⟪⟫B⟪⟫RS = λ x → begin
    (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S)) ∪ (R · x ∩ S · x)
      ⊆⟨ [A∪B]∪C⊆A∪B∪C ⟩
    A ⟪ x ⟫ ∪ (B ⟪ x ⟫ ∪ (R ∩ S)) ∪ (R · x ∩ S · x)
      ⊆⟨ mono-∪ʳ $ [A∪B]∪C⊆A∪B∪C ⟩
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S) ∪ (R · x ∩ S · x)
      ≋⟨⟩
    A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ (R ∩ S) ⟪ x ⟫
      ⊆⟨ mono-∪ʳ $ distrib-∪⟪⟫⊇ ⟩
    A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊇ ⟩
    (A ∪ B ∪ R ∩ S) ⟪ x ⟫
    ∎

  zip-ABCD = λ C D x → begin
    (A ⟪ x ⟫ ∪ B ∪ C) ∪ (A ∪ B ⟪ x ⟫ ∪ C) ∪ D
      ⊆⟨ A∪B∪C⊆[A∪B]∪C ⟩
    ((A ⟪ x ⟫ ∪ B ∪ C) ∪ (A ∪ B ⟪ x ⟫ ∪ C)) ∪ D
      ⊆⟨ mono-∪ˡ $ mono-∪ (mono-∪ʳ $ mono-∪ˡ $ mono-⟪x⟫) (mono-∪ˡ $ mono-⟪x⟫) ⟩
    ((A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ C) ∪ (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ C)) ∪ D
      ⊆⟨ mono-∪ˡ $ A∪A⊆A ⟩
    (A ⟪ x ⟫ ∪ B ⟪ x ⟫ ∪ C) ∪ D
    ∎

  move-A⟪⟫BRS = λ x → begin
    (A ⟪ x ⟫ ∪ R · x) ∪ B ∪ (R ∩ S)
      ⊆⟨ [A∪B]∪C⊆A∪B∪C ⟩
    A ⟪ x ⟫ ∪ R · x ∪ (B ∪ (R ∩ S))
      ⊆⟨ mono-∪ʳ $ B∪A⊆A∪B ⟩
    A ⟪ x ⟫ ∪ (B ∪ (R ∩ S)) ∪ R · x
      ⊆⟨ A∪B∪C⊆[A∪B]∪C ⟩
    (A ⟪ x ⟫ ∪ B ∪ (R ∩ S)) ∪ R · x
    ∎

  move-AB⟪⟫RS = λ x → begin
    A ∪ (B ⟪ x ⟫ ∪ S · x) ∪ R ∩ S
      ⊆⟨ mono-∪ʳ $ [A∪B]∪C⊆A∪B∪C ⟩
    A ∪ B ⟪ x ⟫ ∪ S · x ∪ R ∩ S
      ⊆⟨ mono-∪ʳ $ mono-∪ʳ $ B∪A⊆A∪B ⟩
    A ∪ B ⟪ x ⟫ ∪ R ∩ S ∪ S · x
      ⊆⟨ mono-∪ʳ $ A∪B∪C⊆[A∪B]∪C ⟩
    A ∪ (B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x
      ⊆⟨ A∪B∪C⊆[A∪B]∪C ⟩
    (A ∪ B ⟪ x ⟫ ∪ R ∩ S) ∪ S · x
    ∎

  use-⊆∪ = λ {P} {A} {R} x P⊆A∪R → begin
    P ⟪ x ⟫
      ⊆⟨ mono-⟪⟫ x P⊆A∪R ⟩
    (A ∪ R) ⟪ x ⟫
      ⊆⟨ distrib-∪⟪⟫⊆ A R x ⟩
    A ⟪ x ⟫ ∪ R ⟪ x ⟫
      ⊆⟨ mono-∪ʳ B∪A⊆A∪B ⟩
    A ⟪ x ⟫ ∪ (R · x ∪ R)
      ⊆⟨ A∪B∪C⊆[A∪B]∪C ⟩
    (A ⟪ x ⟫ ∪ R · x) ∪ R
    ∎

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 : {X : Set} (A B R S : Pred[ X ]) → 
             Ar R → Ar S → AF (A ∪ R) → AF (B ∪ S) → AF (A ∪ B ∪ (R ∩ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
theorem-04 A B R S arR arS =
  theorem-04₀ arR arS ⊆-refl ⊆-refl

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 : {X : Set} → (R S : Pred[ X ]) → 
               Ar R → Ar S → AF R → AF S → AF (R ∩ S)
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
corollary-05 R S arR arS afR afS =
  mono-AF
    (begin 𝟘 ∪ 𝟘 ∪ (R ∩ S) ⊆⟨ 𝟘∪A⊆A ⟩ 𝟘 ∪ (R ∩ S) ⊆⟨ 𝟘∪A⊆A ⟩ R ∩ S ∎)
    (theorem-04 𝟘 𝟘 R S
      arR arS
      (mono-AF (R ⊆ 𝟘 ∪ R ∋ A⊆𝟘∪A) afR)
      (mono-AF (S ⊆ 𝟘 ∪ S ∋ A⊆𝟘∪A)  afS))
  where open ⊆-Reasoning


-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- n-ary relations
-----------------------------------------------------------------------------
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

-- The list predicate derived from an n-ary relation is Ar,
-- since it becomes constant when all the n arguments have been provided.

fromNRel→Ar : {X : Set} → (n : ℕ) →
              (R : NRel n X) → Ar (fromNRel n R)
fromNRel→Ar zero R = ar-now (const (flip const))
fromNRel→Ar (suc n) R = ar-later (fromNRel→Ar n ∘ R)

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- The n-ary intuitionistic Ramsey Theorem
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n : {X : Set} (n : ℕ) (R S : NRel n X) →
        AF (fromNRel n R) → AF (fromNRel n S) → AF (fromNRel n (R ⋀ S))
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
IRT_n n R S afR afS =
  mono-AF (mono-⋀∩ n R S)
          (corollary-05 (fromNRel n R) (fromNRel n S)
          (fromNRel→Ar n R) (fromNRel→Ar n S)
          afR afS)


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
AF-Unavoidable P (af-later x→afP⟪x⟫) f = 
  let rem0 : ∃ (λ s → (P ⟪ f zero ⟫) (mapSI (λ x → f (suc x)) s))
      rem0 = AF-Unavoidable (P ⟪ f 0 ⟫) (x→afP⟪x⟫ (f 0)) (λ x → f (suc x))
      s0 : StrictIncSeq
      s0 = proj₁ rem0
      p : (P ⟪ f 0 ⟫) (mapSI (λ x → f (suc x)) s0)
      p = proj₂ rem0
  in (∃ λ s → P (mapSI f s)) ∋ [ _,_ (SI+1 s0) , _,_ (SI0+1 s0) ]′ p
