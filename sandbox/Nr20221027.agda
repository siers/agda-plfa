{-# OPTIONS --guardedness #-}

module sandbox.Nr20221027 where

open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List.Base
open import Data.Char
open import Data.String hiding (_<_; length)
open import Data.String.Properties renaming (_==_ to _≡ᵇ_)
open import Data.Nat hiding (_≡ᵇ_)

data Edit : Set where
  copy : String → Edit
  ins : String → Edit
  del : String → Edit

shortest : {A : Set} → List A → List A → List A
shortest a b = if (length b <ᵇ length a) then b else a

diff : List String → List String → List Edit
diff [] [] = []
diff (a ∷ aa) [] = del a ∷ diff aa []
diff [] (b ∷ bb) = ins b ∷ diff [] bb
-- diff A@(a ∷ aa) B@(b ∷ bb) = copy a ∷ diff aa bb
diff A@(a ∷ aa) B@(b ∷ bb) with a ≡ᵇ b
... | true = copy a ∷ diff aa bb
... | false = shortest (del a ∷ diff aa B) (ins b ∷ diff A bb)

-- diff : List String → List String → List Edit
-- diff [] [] = []
-- diff (a ∷ aa) [] = del a ∷ diff aa []
-- diff [] (b ∷ bb) = ins b ∷ diff [] bb
-- diff A@(a ∷ aa) B@(b ∷ bb) with a ≡ᵇ b
-- ... | true = copy a ∷ diff aa bb
-- ... | false = shortest (diff' (inj₁ a) aa bb) (diff' (inj₂ b) aa bb)
-- -- ... | false = (del a ∷ diff aa B)
-- -- ... | false = (ins b ∷ diff A bb)
--   where
--     diff' : String ⊎ String → List String → List String → List Edit
--     diff' (inj₁ a) aa bb = ins b ∷ diff (a ∷ aa) bb
--     diff' (inj₂ b) aa bb = del a ∷ diff aa (b ∷ bb)
