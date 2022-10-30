{-# OPTIONS --guardedness #-}

module sandbox.Nr20221027 where

open import Function.Base using (_on_; _∘_)
open import Data.Product using (uncurry; _,_; _×_)
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List.Base hiding (_++_)
open import Data.Char
import Data.Char as Char
import Data.String as String
open import Data.String hiding (_<_; length)
open import Data.String.Properties renaming (_==_ to _≡ᵇˢ_)
open import Data.Nat

open import IO
import Level

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
diff A@(a ∷ aa) B@(b ∷ bb) =
  if a ≡ᵇˢ b
  then copy a ∷ diff aa bb
  else shortest (del a ∷ diff aa B) (ins b ∷ diff A bb)

showEdit : Edit → String
showEdit (copy s) = "\x1b[0m" ++ s
showEdit (ins s) = "\x1b[31m+" ++ s
showEdit (del s) = "\x1b[32m-" ++ s

diffString : String → String → String
diffString a b = (a ++ "/" ++ b ++ ": ") ++ joinEdits ((diff on charStrings) a b)
  where
    joinEdits : List Edit → String
    joinEdits = (_++ "\x1b[0m") ∘ String.intersperse "" ∘ map showEdit

    charStrings : String → List String
    charStrings = map String.fromChar ∘ String.toList

diffStrings : List (String × String)
diffStrings =
  ("gello" , "hellod") ∷
  ("gelloed" , "hello world") ∷
  -- ("es šodien gāju pa ielu" , "tu šodien gāji pa tiltu") ∷ -- CPU 100%, never finished
  []

main = run {Level.zero} (IO.List.mapM (putStrLn ∘ uncurry diffString) diffStrings)
