module plfa.part1.Relationsbinary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product
open import Function using (_∘_; _∋_)
open import Data.String.Base using (String; _++_)
open import Data.List using (List; _∷_; []; intersperse; foldl)
open import Data.Nat using (ℕ; zero; _+_; _*_; _≤_; suc; s≤s; z≤n; ≢-nonZero; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc; +-comm; m≤n*m; ≤-trans; ≤-step; *-distribˡ-+)
open import Data.Nat.Show using (show)
open import Data.Empty using (⊥)
-- open import Function.Inverse using ()

-- open import IO using (run; putStrLn)
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

can-to-bin : ∀ {b} → Can b → Bin
can-to-bin {b} _ = b

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

-- Some of this would probably be simpler, if I would exploit the fact that
-- binary strings "…DCBA" are equivalent to "… + D * 2^3 + C * 2^2 + B * 2^1 + A * 2^0 : ℕ",
-- but it might be overkill and I don't think that was the intented way of solving this exercise.

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

inc-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-can {⟨⟩ O} ⟨0⟩ = C ⟨I⟩
inc-can {b} (C o) = C (inc-one o)

to : ∀ (n : ℕ) → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

to-can : ∀ (n : ℕ) → Can (to n)
to-can zero = ⟨O⟩
to-can (suc n) = inc-can (to-can n)

from : ∀ (b : Bin) → ℕ
from ⟨⟩ = zero
from (b O) = 2 * (from b)
from (b I) = 1 + 2 * (from b)

from-can : ∀ {b : Bin} → Can b → ℕ
from-can {b} _ = from b

inc-suc-comm : ∀ {b} (c : Can b) → from-can (inc-can c) ≡ suc (from-can c)
inc-suc-comm {⟨⟩} (C ())
inc-suc-comm {⟨⟩ O} ⟨0⟩ = refl
inc-suc-comm {⟨⟩ I} (C ⟨I⟩) = refl
inc-suc-comm {b O} (C (o O)) = refl
inc-suc-comm {b I} (C (o I)) = begin
  from-can (inc-can (C (o I))) ≡⟨⟩
  from-can (C ((inc-one o) O)) ≡⟨⟩
  2 * from-can (C (inc-one o)) ≡⟨⟩
  2 * from-can (inc-can (C o)) ≡⟨ cong (2 *_) (inc-suc-comm (C o)) ⟩
  2 * (suc (from-can (C o))) ≡⟨⟩
  2 * (1 + (from-can (C o))) ≡⟨ cong (2 *_) (+-comm 1 (from-can (C o))) ⟩
  2 * ((from-can (C o)) + 1) ≡⟨ *-distribˡ-+ 2 (from-can (C o)) 1 ⟩
  2 * from-can (C o) + 2 ≡⟨⟩
  from-can (C (o O)) + 2 ≡⟨ +-comm (from-can (C (o O))) 2 ⟩
  2 + from-can (C (o O)) ≡⟨⟩
  1 + 1 + from-can (C (o O)) ≡⟨⟩
  1 + from-can (C (o I)) ≡⟨⟩
  suc (from-can (C (o I))) ∎

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
  ((to (suc n)) O) ∎
  where
    ×2 : ∀ (n : ℕ) → 2 * n ≡ n + n
    ×2 n = cong (n +_) (+-identityʳ n)
    -- should this really be this difficult? also, it's code golfed
    -- ×2 n = trans (sym (+-assoc n n zero)) (+-comm (n + n) zero)

one≤from : ∀ {b} → One b → 1 ≤ from b
one≤from {⟨⟩ I} ⟨I⟩ = s≤s z≤n
one≤from {b O} (o O) = ≤-trans (one≤from o) (m≤n*m (from b) (s≤s (z≤n {1})))
one≤from {b I} (o I) = ≤-step (≤-trans (one≤from o) (m≤n*m (from b) (s≤s (z≤n {1}))))

≡-to-from-bO : ∀ {b} → Can (b O) → to (from b) ≡ b → to (from (b O)) ≡ b O
≡-to-from-bO {b} (C (o O)) step = begin
  to (from (b O)) ≡⟨⟩
  to (2 * (from b)) ≡⟨ to-×2 (from b) (one≤from o) ⟩
  (to (from b)) O ≡⟨ cong (_O) step ⟩
  b O ∎

≡-to-from : ∀ {b} → Can b → to (from b) ≡ b
≡-to-from (⟨O⟩) = refl
≡-to-from (C ⟨I⟩) = refl
≡-to-from {b O} c@(C (o O)) = ≡-to-from-bO c (≡-to-from (C o))
≡-to-from {b I} (C (o I)) = begin
  to (from (b I)) ≡⟨⟩
  inc (to (2 * (from b))) ≡⟨⟩
  inc (to (from (b O))) ≡⟨ cong inc (≡-to-from-bO (C (o O)) (≡-to-from (C o))) ⟩
  inc (b O) ≡⟨⟩
  b I ∎

≡-to-from-sigma : ∀ (p : Σ Bin Can) → to (from (proj₁ p)) ≡ (proj₁ p)
≡-to-from-sigma (_ , ⟨O⟩) = refl
≡-to-from-sigma (_ , (C ⟨I⟩)) = refl
≡-to-from-sigma (b O , c@(C (o O))) = ≡-to-from-bO c (≡-to-from-sigma (b , C o))
≡-to-from-sigma (b I , (C (o I))) = begin
  to (from (b I)) ≡⟨⟩
  inc (to (2 * (from b))) ≡⟨⟩
  inc (to (from (b O))) ≡⟨ cong inc (≡-to-from-bO (C (o O)) (≡-to-from-sigma (b , C o))) ⟩
  inc (b O) ≡⟨⟩
  b I ∎

≡-from-to-can : ∀ {n} → from-can (to-can n) ≡ n
≡-from-to-can {zero} = refl
≡-from-to-can {suc n} = begin
  from-can (to-can (suc n)) ≡⟨⟩
  from-can (inc-can (to-can n)) ≡⟨ inc-suc-comm (to-can n) ⟩
  suc (from-can (to-can n)) ≡⟨ cong suc (≡-from-to-can {n}) ⟩
  suc n ∎

≡One : ∀ {b : Bin} (ob ob′ : One b) → ob ≡ ob′
≡One ⟨I⟩ ⟨I⟩ = refl
≡One (o O) (o′ O) = cong (_O) (≡One o o′)
≡One (o I) (o′ I) = cong (_I) (≡One o o′)

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can {⟨⟩ O} ⟨O⟩ ⟨O⟩ = refl
≡Can {⟨⟩ O} (⟨O⟩) (C (() O))
≡Can {⟨⟩ O} (C (() O)) (⟨O⟩)
≡Can (C o) (C o′) = cong C (≡One o o′)

proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ {b , c} {b′ , c′} refl = cong (b ,_) (≡Can c c′)

-- ≡-to-from-can : ∀ {b} → (c : Can b) → to-can (from-can c) ≡ c -- this won't type check 😭
-- ≡-to-from-can : ∀ (cb : Σ Bin Can) → to-can (from-can (proj₂ cb)) ≡ (Can ∋ (proj₂ cb))
-- ≡-to-from-can = ?
-- ≡-to-from-can (b , c) = begin
--   to-can (from-can c) ≡⟨⟩
--   to-can (from b) ≡⟨⟩
--   to-can (from b) ≡⟨ proj₁≡→Can≡ (≡-to-from c) ⟩
--   c
--   ∎

outputs : List String
outputs =
  (". + 1 = " ++ ((binToStr ∘ inc) ⟨⟩)) ∷
  ("0 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ O))) ∷
  ("1 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I))) ∷
  ("5 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I O I))) ∷
  ("7 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I I I))) ∷
  ("from (inc (Can (to 7))) = " ++ ((show ∘ from ∘ can-to-bin ∘ inc-can) (to-can 7))) ∷
  ("(show ∘ from ∘ to) 1000 = " ++ ((show ∘ from ∘ to) 1000)) ∷
  []

-- main = run {0ℓ} ((putStrLn ∘ foldl (_++_) "" ∘ intersperse "\n") outputs)
