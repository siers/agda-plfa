module sandbox.Nr20221125 where

open import Data.Bool using (Bool; true; false)
open import Data.Fin as F using (Fin; toℕ; fromℕ<)
open import Data.Sum hiding (swap)
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product hiding (swap)
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Function.Base using (_∘_)
open import Function.Bijection as Bij using (_⤖_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
open import Data.Unit
import Data.Maybe

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Properties using (unfold-reverse; ++-assoc)
open import Relation.Nullary.Decidable using (toWitness)
import Relation.Unary as Un
import Relation.Binary as Bin
import Relation.Nullary as Nul
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

decUnique : Un.Decidable Unique
decUnique = allPairs? (λ a b → ¬? (decCard a b))

_ : Unique deck
_ = toWitness {_} {_} {decUnique deck} tt

open import Data.List.Relation.Binary.Permutation.Propositional as LPr using (_↭_; prep; swap; refl) renaming (trans to ↭-trans)

_ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
_ = ↭-trans (prep 1 (swap 2 3 refl)) (swap 1 3 refl)

-- interleaving x and y gives you z
data Interleave {A : Set} : (x y z : List A) → Set where
  empty : Interleave [] [] []
  more : {a : A} {x y z : List A} → Interleave x y z → Interleave y (a ∷ x) (a ∷ z)

data Interleaving {A : Set} : (x y z : List A) → Set where
  interleavingR : {x y z : List A} → Interleave y x z → Interleaving x y z
  interleavingL : {x y z : List A} → Interleave x y z → Interleaving x y z

intl : Interleaving (1 ∷ 3 ∷ []) (2 ∷ []) (1 ∷ 2 ∷ 3 ∷ [])
intl = interleavingR (more (more (more empty)))

-- deck  =  joker ++ shuffle ++ rest  =  joker ++ (shuffle ~ interleaving andar bahar) ++ rest
ShuffleInvariant : Stack → Card → Stack → Stack → Stack → Stack → Set
ShuffleInvariant   deck    joker  a       b       shuffle rest =
  Interleave a b shuffle × (deck ≡ (joker ∷ (reverse shuffle ++ rest)))

data X : (x : ℕ) → (y : ℕ) → List ℕ → x ≡ y → Set where
  -- unsurprisingly, I can put a value in a type
  xx : X 1 1 [] refl
  -- I can ask for values to be specific as well
  yy : X 2 2 [] refl → X 3 3 [] refl
  -- can't use pattern matching in "a" or "b" (that also excludes matching against "l")
  zz : (l : List ℕ) → (eq : 1 ≡ 2) → ( a , b : List ℕ × List ℕ ) → X 1 2 (1 ∷ l) eq → X 1 2 [] eq

≡-comm : ∀ {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
≡-comm refl = refl

unfold-reverse-assoc : {A : Set} → (x : A) → (a b : List A) → reverse a ++ (x ∷ b) ≡ reverse (x ∷ a) ++ b
unfold-reverse-assoc x a b = ≡-comm (trans (cong (_++ b) (unfold-reverse x a)) (++-assoc (reverse a) ([ x ]) b))

add-deck : (deck : Stack) → (shuffle : Stack) → (rest : Stack) → (joker : Card) → (next : Card)
  → (deck ≡ joker ∷ (reverse shuffle ++ (next ∷ rest))) → (deck ≡ joker ∷ (reverse (next ∷ shuffle) ++ rest))
add-deck deck shuffle rest joker next order =
  trans order (cong (joker ∷_) (unfold-reverse-assoc next shuffle rest))

-- 5 decks + joker
data AndarBaharShuffle (deck : Stack) : (joker : Card) (one two shuffle rest : Stack) (invariant : ShuffleInvariant deck joker one two shuffle rest) → Set where
  start : (joker : Card) (rest : Stack) → (order : deck ≡ ([ joker ] ++ rest)) → AndarBaharShuffle deck joker [] [] [] rest (empty , order)
  andar :
    (joker next : Card) (andar bahar shuffle rest : Stack) →
    (( intlv , order ) : ShuffleInvariant deck joker andar bahar shuffle (next ∷ rest)) →
    AndarBaharShuffle deck joker andar bahar shuffle (next ∷ rest) ( intlv , order ) →
    AndarBaharShuffle deck joker bahar (next ∷ andar) (next ∷ shuffle) rest ( (more intlv) , (add-deck deck shuffle rest joker next order) )
  bahar :
    (joker next : Card) (andar bahar shuffle rest : Stack) →
    (( intlv , order ) : ShuffleInvariant deck joker bahar andar shuffle (next ∷ rest)) →
    AndarBaharShuffle deck joker bahar andar shuffle (next ∷ rest) ( intlv , order ) →
    AndarBaharShuffle deck joker andar (next ∷ bahar) (next ∷ shuffle) rest ( (more intlv) , (add-deck deck shuffle rest joker next order) )

x : (Data.List.head deck) ≡ Data.Maybe.just (card spades ace)
x = refl

rest = Data.List.drop 1 deck

-- a : {invariant : ShuffleInvariant deck joker one two shuffle rest} → AndarBaharShuffle deck (card spades ace) [] [] [] rest invariant
-- a = 1
