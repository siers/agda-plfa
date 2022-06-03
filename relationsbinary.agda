module relationsbinary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (_∘_; _∋_)
open import Data.String.Base using (String; _++_)
open import Data.List using (List; _∷_; []; intersperse; foldl)
open import Data.Nat using (ℕ; zero; _+_; _*_; _≤_; suc; s≤s; z≤n; ≢-nonZero; _<_)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; m≤n*m; ≤-trans; ≤-step)
open import Data.Nat.Show using (show)
open import Data.Empty using (⊥)

open import IO using (run; putStrLn)
open import Level using (0ℓ)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

binToStr : Bin → String
binToStr ⟨⟩ = ""
binToStr (b O) = binToStr b ++ "0"
binToStr (b I) = binToStr b ++ "1"

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

data One : Bin → Set where
  ⟨I⟩ : One (⟨⟩ I)
  _O : ∀ {b : Bin} → One b → One (b O)
  _I : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
  ⟨O⟩ : Can (⟨⟩ O)
  C : ∀ {b : Bin} → One b → Can b

-- for some reason these absurd patterns must be named to work properly.
-- courtesy of ncf from irc.libera.net/#agda's ncf
can't : Can ⟨⟩ → ⊥
can't (C ())

_ : Can (⟨⟩ O)
_ = ⟨O⟩

can't2 : Can (⟨⟩ O O) → ⊥
can't2 (C (() O O))

can't3 : Can (⟨⟩ O I) → ⊥
can't3 (C (() O I))

_ : Can (⟨⟩ I)
_ = C (⟨I⟩)

_ : Can (⟨⟩ I O)
_ = C (⟨I⟩ O)

_ : Can (⟨⟩ I I)
_ = C (⟨I⟩ I)

_ : Can (⟨⟩ I O O)
_ = C (⟨I⟩ O O)

inc-can-long : ∀ {b : Bin} → Can b → Can (inc b)
inc-can-long {⟨⟩} (C ())
inc-can-long {⟨⟩ O} ⟨0⟩ = C ⟨I⟩
inc-can-long {⟨⟩ I} (C ⟨I⟩) = C (⟨I⟩ O)
inc-can-long (C (o O)) = C (o I)
inc-can-long {b} (C (o I)) = can-suffix-O (inc-can-long (C o))
  where
    can-suffix-O : ∀ {b : Bin} → Can (inc b) → Can ((inc b) O)
    can-suffix-O {⟨⟩ I} (C o) = C (o O)
    can-suffix-O {b} (C o) = C (o O)

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one ⟨I⟩ = (⟨I⟩ O)
inc-one (o O) = (o I)
inc-one (o I) = (inc-one o) O

inc-can-short : ∀ {b : Bin} → Can b → Can (inc b)
inc-can-short {⟨⟩ O} ⟨0⟩ = C ⟨I⟩
inc-can-short {b} (C o) = C (inc-one o)

to : ∀ (n : ℕ) → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

to-can : ∀ (n : ℕ) → Can (to n)
to-can zero = ⟨O⟩
to-can (suc n) = inc-can-short (to-can n)

from : ∀ (b : Bin) → ℕ
from ⟨⟩ = zero
from (b O) = 2 * (from b)
from (b I) = 1 + 2 * (from b)

fromCan : ∀ {b : Bin} → Can b → Bin
fromCan {b} _ = b

_ : to (2 * (from (⟨⟩ I))) ≡ ⟨⟩ I O
_ = refl

-- "2 * n = n + n" should not have been baked into this proof, but shoehorned it in anyway
-- to-×2 : ∀ (n : ℕ) → 1 ≤ n → to (n + n) ≡ Bin ∋ ((to n) O)
to-×2 : ∀ (n : ℕ) → 1 ≤ n → to (2 * n) ≡ (Bin ∋ ((to n) O))
to-×2 1 1≤1 = refl
to-×2 (suc n@(suc m)) 1≤sucn =
  begin
  to (2 * (suc n)) ≡⟨ cong to (×2 (suc n)) ⟩
  to ((suc n) + (suc n)) ≡⟨ cong to (+-suc (suc n) n) ⟩
  inc (inc (to (n + n))) ≡⟨ cong (inc ∘ inc) (trans (cong to (sym (×2 n))) (to-×2 n (s≤s (z≤n {m})))) ⟩
  inc (inc ((to n) O)) ≡⟨⟩
  ((to (suc n)) O)
  ∎
  where
    -- should this really be this difficult? also, it's code golfed
    ×2 : ∀ (n : ℕ) → 2 * n ≡ n + n
    ×2 n = trans (sym (+-assoc n n zero)) (+-comm (n + n) zero)

one≤from : ∀ {b} → One b → 1 ≤ from b
one≤from {⟨⟩ I} ⟨I⟩ = s≤s z≤n
one≤from {b O} (o O) = ≤-trans (one≤from o) (m≤n*m (from b) (s≤s (z≤n {1})))
one≤from {b I} (o I) = ≤-step (≤-trans (one≤from o) (m≤n*m (from b) (s≤s (z≤n {1}))))

≡-to-from-bO : ∀ {b} → Can (b O) → to (from b) ≡ b → to (from (b O)) ≡ b O
≡-to-from-bO {b} (C (o O)) step = begin
  to (from (b O)) ≡⟨⟩
  to (2 * (from b)) ≡⟨ to-×2 (from b) (one≤from o) ⟩
  (to (from b)) O ≡⟨ cong (_O) step ⟩
  b O
  ∎

≡-to-from : ∀ {b} → Can b → to (from b) ≡ b
≡-to-from (⟨O⟩) = refl
≡-to-from (C ⟨I⟩) = refl
≡-to-from {b O} c@(C (o O)) = ≡-to-from-bO c (≡-to-from (C o))
≡-to-from {b I} (C (o I)) = begin
  to (from (b I)) ≡⟨⟩
  inc (to (2 * (from b))) ≡⟨⟩
  inc (to (from (b O))) ≡⟨ cong inc (≡-to-from-bO (C (o O)) (≡-to-from (C o))) ⟩
  inc (b O) ≡⟨⟩
  b I
  ∎

outputs : List String
outputs =
  (". + 1 = " ++ ((binToStr ∘ inc) ⟨⟩)) ∷
  ("0 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ O))) ∷
  ("1 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I))) ∷
  ("5 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I O I))) ∷
  ("7 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I I I))) ∷
  ("from (inc (Can (to 7))) = " ++ ((show ∘ from ∘ fromCan ∘ inc-can-short) (to-can 7))) ∷
  ("(show ∘ from ∘ to) 1000 = " ++ ((show ∘ from ∘ to) 1000)) ∷
  []

main = run {0ℓ} ((putStrLn ∘ foldl (_++_) "" ∘ intersperse "\n") outputs)
