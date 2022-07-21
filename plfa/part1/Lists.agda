module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

reverse : ∀ {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-distrib-++ : ∀ {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-distrib-++ [] ys = sym (++-identityʳ (reverse ys))
reverse-distrib-++ xs@(x ∷ s) ys =
  begin
  reverse (xs ++ ys) ≡⟨⟩
  reverse ((x ∷ s) ++ ys) ≡⟨⟩
  reverse (x ∷ (s ++ ys)) ≡⟨⟩
  reverse (s ++ ys) ++ [ x ] ≡⟨⟩
  reverse (s ++ ys) ++ [ x ] ≡⟨ cong (_++ [ x ]) (reverse-distrib-++ s ys) ⟩
  (reverse ys ++ reverse s) ++ [ x ] ≡⟨ ++-assoc (reverse ys) (reverse s) [ x ] ⟩
  reverse ys ++ (reverse s ++ [ x ]) ≡⟨⟩
  reverse ys ++ reverse xs
  ∎
