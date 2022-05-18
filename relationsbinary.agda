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

inc-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-can {⟨⟩} (C ())
inc-can {⟨⟩ O} ⟨0⟩ = C ⟨1⟩
inc-can {⟨⟩ I} (C ⟨1⟩) = C (⟨1⟩ O)
inc-can (C (o O)) = C (o I)
inc-can {b} (C (o I)) = helper (inc-can (C o))
  where
    helper : ∀ {b : Bin} → Can (inc b) → Can ((inc b) O)
    helper {⟨⟩ I} (C o) = C (o O)
    helper {c} (C o) = C (o O)

main = run {0ℓ} ((putStrLn ∘ foldl (_++_) "" ∘ intersperse "\n") outputs)
