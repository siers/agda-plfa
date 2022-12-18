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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs
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

open import Data.List.Relation.Binary.Permutation.Propositional as LPr
open PermutationReasoning

_ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
_ = trans (prep 1 (swap 2 3 refl)) (swap 1 3 refl)

data Interleave {A : Set} : (x y z : List A) → Set where
  empty : Interleave [] [] []
  more : {a : A} {x y z : List A} → Interleave x y z → Interleave y (a ∷ x) (a ∷ z)

data Interleaving {A : Set} : (x y z : List A) → Set where
  interleavingR : {x y z : List A} → Interleave y x z → Interleaving x y z
  interleavingL : {x y z : List A} → Interleave x y z → Interleaving x y z

intl : Interleaving (1 ∷ 3 ∷ []) (2 ∷ []) (1 ∷ 2 ∷ 3 ∷ [])
intl = interleavingR (more (more (more empty)))

ShuffleInvariant : Stack → Card → Stack → Stack → Stack → Set
ShuffleInvariant deck joker andar bahar rest = (∃ λ shuffle → (Interleaving andar bahar shuffle × deck ≡ ([ joker ] ++ shuffle ++ rest)))

postulate fakeInvariant : Set -- λ deck joker andar bahar rest → (∃ λ shuffle → (Interleaving andar bahar shuffle × deck ↭ ([ joker ] ++ shuffle ++ rest)))

data X : (x : ℕ) → (y : ℕ) → x ≡ y → Set where
  x : X 1 1 refl

data AndarBahar (deck : Stack) : (joker : Card) (andar bahar rest : Stack) (invariant : ShuffleInvariant deck joker andar bahar rest) → Set where
  start : (joker : Card) (rest : Stack) → (order : deck ≡ ([ joker ] ++ rest)) → AndarBahar deck joker [] [] rest ([] , (interleavingL empty , order))
  deal :
    (joker next : Card) (andar bahar rest : Stack) →
    (invariant : ShuffleInvariant deck joker andar bahar (next ∷ rest)) → AndarBahar deck joker andar bahar (next ∷ rest) invariant →
    (invariant′ : ShuffleInvariant deck joker andar bahar rest) → AndarBahar deck joker andar bahar rest invariant′

-- advance : (joker next : Card) (andar bahar rest : Stack) → AndarBahar deck joker -- fuuuuck, this don't seem right
