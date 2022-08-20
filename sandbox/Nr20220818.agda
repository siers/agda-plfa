module Nr20220818 where

open import Data.Fin as F using (Fin; toℕ; fromℕ<)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Function.Base using (_∘_)
open import Function.Bijection as Bij using (_⤖_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional using (Unique; al)
open import Data.List.Relation.Unary.AllPairs
open import Relation.Nullary.Decidable using (toWitness)
import Relation.Unary as U
open import Relation.Nullary.Negation using (¬?)

data Suit : Set where
  spades : Suit
  hearts : Suit
  diamonds : Suit
  clubs : Suit

data Rank : Set where
  ace : Rank
  two : Rank
  three : Rank
  four : Rank
  five : Rank
  six : Rank
  seven : Rank
  eight : Rank
  nine : Rank
  ten : Rank
  jack : Rank
  queen : Rank
  king : Rank

fromRank : Rank → Fin 13
fromRank ace = fromℕ< {0} (s≤s (z≤n {12}))
fromRank two = fromℕ< {1} (s≤s (s≤s (z≤n {11})))
fromRank three = fromℕ< (<ᵇ⇒< 2 13 tt)
fromRank four = fromℕ< (<ᵇ⇒< 3 13 tt)
fromRank five = fromℕ< (<ᵇ⇒< 4 13 tt)
fromRank six = fromℕ< (<ᵇ⇒< 5 13 tt)
fromRank seven = fromℕ< (<ᵇ⇒< 6 13 tt)
fromRank eight = fromℕ< (<ᵇ⇒< 7 13 tt)
fromRank nine = fromℕ< (<ᵇ⇒< 8 13 tt)
fromRank ten = fromℕ< (<ᵇ⇒< 9 13 tt)
fromRank jack = fromℕ< (<ᵇ⇒< 10 13 tt)
fromRank queen = fromℕ< (<ᵇ⇒< 11 13 tt)
fromRank king = fromℕ< (<ᵇ⇒< 12 13 tt)

toRank : Fin 13 → Rank
toRank F.zero = ace
toRank (F.suc F.zero) = two
toRank (F.suc (F.suc F.zero)) = three
toRank (F.suc (F.suc (F.suc F.zero))) = four
toRank (F.suc (F.suc (F.suc (F.suc F.zero)))) = five
toRank (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) = six
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))) = seven
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))) = eight
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))) = nine
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))) = ten
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))) = jack
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))) = queen
toRank (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))) = king

ri : Rank ⤖ Fin 13
ri = Bij.bijection fromRank toRank inj inv
  where
  inj : ∀ {ra : Rank} {rb : Rank} → fromRank ra ≡ fromRank rb → ra ≡ rb
  inj {ace} {ace} refl = refl
  inj {two} {two} refl = refl
  inj {three} {three} refl = refl
  inj {four} {four} refl = refl
  inj {five} {five} refl = refl
  inj {six} {six} refl = refl
  inj {seven} {seven} refl = refl
  inj {eight} {eight} refl = refl
  inj {nine} {nine} refl = refl
  inj {ten} {ten} refl = refl
  inj {jack} {jack} refl = refl
  inj {queen} {queen} refl = refl
  inj {king} {king} refl = refl

  inv : ∀ (f : Fin 13) → fromRank (toRank f) ≡ f
  inv F.zero = refl
  inv (F.suc F.zero) = refl
  inv (F.suc (F.suc F.zero)) = refl
  inv (F.suc (F.suc (F.suc F.zero))) = refl
  inv (F.suc (F.suc (F.suc (F.suc F.zero)))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))) = refl
  inv (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))) = refl

card : Rank → Suit → Rank × Suit
card = _,_

l : List ℕ
l = 1 ∷ 5 ∷ 2 ∷ 4 ∷ []

decUnique : U.Decidable Unique
decUnique = allPairs? (λ a b → ¬? (a ≟ b))

_ : Unique l
_ = toWitness {_} {_} {decUnique l} tt
