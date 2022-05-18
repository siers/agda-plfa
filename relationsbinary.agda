module relationsbinary where

open import Function using (_∘_)
open import Data.String.Base hiding (concat; intersperse)
open import Data.List using (List; _∷_; []; intersperse; foldl)
open import Data.Nat

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
  ⟨1⟩ : One (⟨⟩ I)
  _O : ∀ {b : Bin} → One b → One (b O)
  _I : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
  ⟨O⟩ : Can (⟨⟩ O)
  C : ∀ {b : Bin} → One b → Can b

open import Data.Empty

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
_ = C (⟨1⟩)

_ : Can (⟨⟩ I O)
_ = C (⟨1⟩ O)

_ : Can (⟨⟩ I I)
_ = C (⟨1⟩ I)

_ : Can (⟨⟩ I O O)
_ = C (⟨1⟩ O O)

outputs : List String
outputs =
  (". + 1 = " ++ ((binToStr ∘ inc) ⟨⟩)) ∷
  ("0 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ O))) ∷
  ("1 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I))) ∷
  ("5 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I O I))) ∷
  ("7 + 1 = " ++ ((binToStr ∘ inc) (⟨⟩ I I I))) ∷
  []

inc-can-long : ∀ {b : Bin} → Can b → Can (inc b)
inc-can-long {⟨⟩} (C ())
inc-can-long {⟨⟩ O} ⟨0⟩ = C ⟨1⟩
inc-can-long {⟨⟩ I} (C ⟨1⟩) = C (⟨1⟩ O)
inc-can-long (C (o O)) = C (o I)
inc-can-long {b} (C (o I)) = can-suffix-O (inc-can-long (C o))
  where
    can-suffix-O : ∀ {b : Bin} → Can (inc b) → Can ((inc b) O)
    can-suffix-O {⟨⟩ I} (C o) = C (o O)
    can-suffix-O {c} (C o) = C (o O)

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one ⟨1⟩ = (⟨1⟩ O)
inc-one (o O) = (o I)
inc-one (o I) = (inc-one o) O

inc-can-short : ∀ {b : Bin} → Can b → Can (inc b)
inc-can-short {⟨⟩} (C ())
inc-can-short {⟨⟩ O} ⟨0⟩ = C ⟨1⟩
inc-can-short {b} (C o) = C (inc-one o)

fromCan : ∀ {b : Bin} → Can b → Bin
fromCan {b} _ = b

-- to : ∀ {n : ℕ} → Can Bin
-- to zero = ⟨O⟩
-- to (suc n) = inc-can (to n)

main = run {0ℓ} ((putStrLn ∘ foldl (_++_) "" ∘ intersperse "\n") outputs)
