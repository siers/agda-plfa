module Nr20220818 where

open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Product -- using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

data Suit : Set where
  spades : Suit
  hearts : Suit
  diamonds : Suit
  clubs : Suit

data Rank : ℕ → Set where
  ace : Rank 1
  two : Rank 2
  three : Rank 3
  four : Rank 4
  five : Rank 5
  six : Rank 6
  seven : Rank 7
  eight : Rank 8
  nine : Rank 9
  ten : Rank 10
  jack : Rank 11
  queen : Rank 12
  king : Rank 13

rank : {n : ℕ} → Rank n → ℕ
rank {n} _ = n

_ : rank jack ≡ 11
_ = refl

card : ∀ (r : Σ ℕ Rank) → (s : Suit) → Σ ℕ Rank × Suit
card r s = r , s
