module plfa.part1.Negation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (suc-injective; ≤-pred)
open import Data.Nat using (ℕ; zero; _+_; _*_; _≤_; suc; s≤s; z≤n; _<_)
open import Data.Product -- using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_)

open import plfa.part1.Isomorphism using (_≃_; extensionality)

<-irreflexive : ∀ n → ¬ (n < n)
<-irreflexive (suc m) (s≤s m≤m) = <-irreflexive m m≤m

trichotomy : Trichotomous (_≡_) (_<_)
trichotomy zero    zero    = tri≈ (λ()) refl (λ())
trichotomy zero    (suc n) = tri< (s≤s (z≤n {n})) (λ()) (λ())
trichotomy (suc n) zero    = tri> (λ()) (λ()) (s≤s (z≤n {n}))
trichotomy (suc n) (suc m) with trichotomy n m
... | tri< n<m n≉m n≯m = tri< (s≤s n<m)      (n≉m ∘ suc-injective) (n≯m ∘ ≤-pred)
... | tri≈ n≮m n≈m n≯m = tri≈ (n≮m ∘ ≤-pred) (cong suc n≈m)        (n≯m ∘ ≤-pred)
... | tri> n≮m n≉m n>m = tri> (n≮m ∘ ≤-pred) (n≉m ∘ suc-injective) (s≤s n>m)

⊎-dual-× : ∀ {A B} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : ∀ {A B} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
    to ¬a⊎b = (¬a⊎b ∘ inj₁) , (¬a⊎b ∘ inj₂)

    from : ∀ {A B} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
    from (¬a , ¬b) = [ ¬a , ¬b ]

    from∘to : ∀ {A B : Set} → (¬a⊎b : (¬ (A ⊎ B))) → from {A} {B} (to {A} {B} ¬a⊎b) ≡ ¬a⊎b
    from∘to ¬a⊎b = extensionality (λ a⊎b → ⊥-elim {_} {from (to ¬a⊎b) a⊎b ≡ ¬a⊎b a⊎b} (¬a⊎b a⊎b))

    to∘from : ∀ {A B} → (¬a×¬b : (¬ A) × (¬ B)) → to (from ¬a×¬b) ≡ ¬a×¬b
    to∘from {A} {B} (¬a , ¬b) = refl

---

_ : ℕ → ℕ → ℕ
_ = λ{x → λ{y → x + y}}

-- g : ℕ
-- g = (λ{(a : ℕ , b : ℕ) → a + b}) (1 , 2)

f : ℕ → ℕ → ℕ
f a b = a + b

g : ℕ → ℕ → ℕ
g c d = c + d

_ : ((ℕ → ⊥) ≡ (ℕ → ⊥) × f ≡ g)
_ = refl , refl

test : ∀ {A : Set} → (f : (A → ⊥)) → (g : (A → ⊥)) → f ≡ g
test f g = extensionality (λ a → ⊥-elim {_} {f a ≡ g a} (f a))
