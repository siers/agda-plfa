module Nr20220818 where

open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Function.Injection as Inj using (_↣_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality.Properties as EqProp

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

_ : (1 < 2) ≡ (1 < 2)
_ = refl

-- _ : 2 < 12
-- _ = <ᵇ⇒< 2 12 tt

rank : Rank → Fin 14
rank ace = fromℕ< {0} (s≤s (z≤n {13}))
rank two = fromℕ< {1} (s≤s (s≤s (z≤n {12})))
rank three = fromℕ< (<ᵇ⇒< 2 14 tt)
rank four = fromℕ< (<ᵇ⇒< 4 14 tt)
rank five = fromℕ< (<ᵇ⇒< 5 14 tt)
rank six = fromℕ< (<ᵇ⇒< 6 14 tt)
rank seven = fromℕ< (<ᵇ⇒< 7 14 tt)
rank eight = fromℕ< (<ᵇ⇒< 8 14 tt)
rank nine = fromℕ< (<ᵇ⇒< 9 14 tt)
rank ten = fromℕ< (<ᵇ⇒< 10 14 tt)
rank jack = fromℕ< (<ᵇ⇒< 11 14 tt)
rank queen = fromℕ< (<ᵇ⇒< 12 14 tt)
rank king = fromℕ< (<ᵇ⇒< 13 14 tt)

_ : toℕ (rank jack) ≡ 11
_ = refl

rs : Setoid 0ℓ 0ℓ
rs = EqProp.setoid Rank

ri : Rank ↣ Fin 14
ri = Inj.injection rank proof
  where
  proof : ∀ {ra : Rank} {rb : Rank} → rank ra ≡ rank rb → ra ≡ rb
  proof {ace} {ace} refl = refl
  proof {two} {two} refl = refl
  proof {three} {three} refl = refl
  proof {four} {four} refl = refl
  proof {five} {five} refl = refl
  proof {six} {six} refl = refl
  proof {seven} {seven} refl = refl
  proof {eight} {eight} refl = refl
  proof {nine} {nine} refl = refl
  proof {ten} {ten} refl = refl
  proof {jack} {jack} refl = refl
  proof {queen} {queen} refl = refl
  proof {king} {king} refl = refl

card : Rank → Suit → Rank × Suit
card = _,_
