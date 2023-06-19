module sandbox.Nr20230618 where

open import Data.Bool using (Bool; true; false)
open import Data.Fin as F using (Fin; toℕ; fromℕ<)
open import Data.Sum hiding (swap)
open import Data.Vec.Base
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product hiding (swap)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
import Data.Maybe
open import Data.Nat.DivMod using (_/_)

open import Data.List hiding (_++_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Properties using (unfold-reverse; ++-assoc)
-- open import Relation.Nullary.Decidable using (toWitness)
-- import Relation.Unary as Un
import Relation.Binary as Bin
import Relation.Nullary as Nul
-- open import Relation.Nullary.Negation using (¬?)

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

data Card : Set where
  card : Suit → Rank → Card

Stack : Set
Stack = List Card

suits : List Suit
suits = spades ∷ hearts ∷ diamonds ∷ clubs ∷ []

ranks : List Rank
ranks = ace ∷ two ∷ three ∷ four ∷ five ∷ six ∷ seven ∷ eight ∷ nine ∷ ten ∷ jack ∷ queen ∷ king ∷ []

deck : Stack
deck = concatMap (\s → Data.List.map (card s) ranks) suits

decSuit : Bin.Decidable {A = Suit} _≡_
decSuit spades = λ { spades → Nul.yes refl ; hearts → Nul.no (λ()) ; diamonds → Nul.no (λ()) ; clubs → Nul.no (λ()) }
decSuit hearts = λ { hearts → Nul.yes refl ; spades → Nul.no (λ()) ; diamonds → Nul.no (λ()) ; clubs → Nul.no (λ()) }
decSuit diamonds = λ { diamonds → Nul.yes refl ; hearts → Nul.no (λ()) ; spades → Nul.no (λ()) ; clubs → Nul.no (λ()) }
decSuit clubs = λ { clubs → Nul.yes refl ; hearts → Nul.no (λ()) ; diamonds → Nul.no (λ()) ; spades → Nul.no (λ()) }

decRank : Bin.Decidable {A = Rank} _≡_
decRank ace = λ { ace → Nul.yes refl ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) }
decRank two = λ { two → Nul.yes refl ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) }
decRank three = λ { three → Nul.yes refl ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) }
decRank four = λ { four → Nul.yes refl ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) }
decRank five = λ { five → Nul.yes refl ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) }
decRank six = λ { six → Nul.yes refl ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) }
decRank seven = λ { seven → Nul.yes refl ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) }
decRank eight = λ { eight → Nul.yes refl ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) }
decRank nine = λ { nine → Nul.yes refl ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) }
decRank ten = λ { ten → Nul.yes refl ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) }
decRank jack = λ { jack → Nul.yes refl ; queen → Nul.no (λ()) ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) }
decRank queen = λ { queen → Nul.yes refl ; king → Nul.no (λ()) ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) }
decRank king = λ { king → Nul.yes refl ; ace → Nul.no (λ()) ; two → Nul.no (λ()) ; three → Nul.no (λ()) ; four → Nul.no (λ()) ; five → Nul.no (λ()) ; six → Nul.no (λ()) ; seven → Nul.no (λ()) ; eight → Nul.no (λ()) ; nine → Nul.no (λ()) ; ten → Nul.no (λ()) ; jack → Nul.no (λ()) ; queen → Nul.no (λ()) }

decCard : Bin.Decidable {A = Card} _≡_
decCard c@(card s r) c′@(card s′ r′) with decSuit s s′ | decRank r r′
... | Nul.yes refl | Nul.yes refl = Nul.yes refl
... | Nul.no s≢s′  | _            = Nul.no λ{ refl → s≢s′ refl }
... | _            | Nul.no r≢r′  = Nul.no λ{ refl → r≢r′ refl }

v1 : Vec ℕ 3
v1 = 1 ∷ 2 ∷ 3 ∷ []
v2 : Vec ℕ 2
v2 = 6 ∷ 7 ∷ []
v3 : Vec ℕ 5
v3 = 1 ∷ 6 ∷ 2 ∷ 7 ∷ 3 ∷ []
v4 : Vec ℕ 6
v4 = 1 ∷ 5 ∷ 2 ∷ 6 ∷ 3 ∷ 7 ∷ []
x : v1 ⋎ v2 ≡ v3
x = refl
y : v1 ⋎ (5 ∷ v2) ≡ v4
y = refl

-- irb(main):016:0> def diff1(n, int); int.to_a.map { |x| buckets = n.times.to_a.map { |m| (x + m) / n }; [buckets, buckets.sum, x] }; end
-- => :diff1
-- irb(main):017:0> diff1(3, (-5..20)).each(&method(:p)); nil
-- irb(main):014:0> def check_diff1(n, int); int.to_a.all? { |x| buckets = n.times.to_a.map { |m| (x + m) / n }; buckets.sum == x }; end
-- => :check_diff1
-- irb(main):016:0> (1..100).all? { |x| diff1(x, (-1000..1000)) };
-- => true
postulate ≡-bucket-2 : (n : ℕ) → n ≡ (n + 1) / 2 + (n / 2)

-- 1. make deck Vec n Card, add M for shuffle
-- 2. Model cards as Fin or find some library that generically gives you equality decidables
-- 3. prove or find proof that for AndarBaharShuffle deck N M where N < M has a next :: rest
record AndarBaharShuffle (n : ℕ) (m : ℕ) (deck : Vec Card n) : Set where
  field
    joker : Card
    andar : Vec Card ((m + 1) / 2)
    bahar : Vec Card ((m + 0) / 2)
    shuffle : Vec Card m
    -- rest : Vec Card (((m + 0) / 2) + ((m + 1) / 2))
    rest : Vec Card m
    p1 : n ≤ m
    p21 : ((m + 1) / 2) + ((m + 0) / 2) ≡ m
    -- p22 : andar ⋎ bahar ≡ shuffle
    -- invariant : andar ⋎ bahar ≡ rest  ×  deck ≡ joker ∷ (shuffle ++ rest)

-- unfold-reverse-assoc : {A : Set} → (x : A) → (a b : List A) → reverse a ++ (x ∷ b) ≡ reverse (x ∷ a) ++ b
-- unfold-reverse-assoc x a b = sym (trans (cong (_++ b) (unfold-reverse x a)) (++-assoc (reverse a) ([ x ]) b))

-- ≡-card-added : (deck : Stack) → (shuffle : Stack) → (rest : Stack) → (joker : Card) → (next : Card)
--   → (deck ≡ joker ∷ (reverse shuffle ++ (next ∷ rest)))
--   → (deck ≡ joker ∷ (reverse (next ∷ shuffle) ++ rest))
-- ≡-card-added deck shuffle rest joker next order =
--   trans order (cong (joker ∷_) (unfold-reverse-assoc next shuffle rest))
