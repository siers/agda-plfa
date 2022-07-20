module plfa.part1.Peano where

-- https://plfa.github.io/Induction/

open import IO
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-comm; *-suc)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p = begin
  m + (n + p) ≡⟨ sym (+-assoc m n p) ⟩
  (m + n) + p ≡⟨ cong (_+ p) (+-comm m n) ⟩
  (n + m) + p ≡⟨ +-assoc n m p ⟩
  n + (m + p) ∎

+-distrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
+-distrib m n zero = begin
  (m + n) * zero      ≡⟨ *-comm (m + n) zero ⟩
  zero * m + zero * n ≡⟨ cong ((zero * m) +_) (*-comm zero n) ⟩
  zero * m + n * zero ≡⟨ cong (_+ (n * zero)) (*-comm zero m) ⟩
  m * zero + n * zero ∎
+-distrib m n (suc p) = begin
  (m + n) * suc p               ≡⟨ *-suc (m + n) p ⟩
  m + n + (m + n) * p           ≡⟨ cong ((m + n) +_) (+-distrib m n p) ⟩
  m + n + (m * p + n * p)       ≡⟨ +-assoc m n (m * p + n * p) ⟩
  m + (n + (m * p + n * p))     ≡⟨ cong (m +_) (sym (+-assoc n (m * p) (n * p))) ⟩
  m + (n + m * p + n * p)       ≡⟨ cong (m +_) (cong (_+ (n * p)) (+-comm n (m * p))) ⟩
  m + (m * p + n + n * p)       ≡⟨ cong (m +_) (+-assoc (m * p) n (n * p)) ⟩
  m + (m * p + (n + n * p))     ≡⟨ sym (+-assoc m (m * p) (n + n * p)) ⟩
  m + m * p + (n + n * p)       ≡⟨ cong (_+ (n + n * p)) (sym (*-suc m p)) ⟩
  m * suc p + (n + n * p)       ≡⟨ cong ((m * suc p) +_) (sym (*-suc n p)) ⟩
  m * suc p + (n * suc p)       ∎

_ : (5 + 3) * 2 ≡ 5 * 2 + 3 * 2
_ = begin
  (5 + 3) * 2   ≡⟨ +-distrib 5 3 2 ⟩
  5 * 2 + 3 * 2 ∎

main = run {0ℓ} (putStrLn "complies")

-- % agda --compile -l standard-library -i . peano.agda && ./peano
