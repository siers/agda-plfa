module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong)
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

open import IO
open import Level using (0ℓ)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- wrote this myself
≤-refl : ∀ (n : ℕ) → n ≤ n
≤-refl zero = z≤n {zero}
≤-refl (suc n) = s≤s (≤-refl n)

-- -- wrote this myself
-- ≤-trans : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
-- ≤-trans zero zero p = z≤n p
-- ≤-trans zero (suc n) p = ≤-trans zero n p
-- ≤-trans (suc m) n p = ≤-trans m n p

-- ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
-- ≤-antisym z≤n z≤n              =  refl
-- ≤-antisym z≤n       (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
-- ≤-antisym (s≤s m≤n) zero       =  cong suc (≤-antisym m≤n n≤m)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward (z≤n {n})
≤-total m zero = flipped (z≤n {m})
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans zero    (suc n) (suc p) z<s n<p = z<s
<-trans (suc m) (suc n) (suc p) (s<s m<n) (s<s n<p) = s<s (<-trans m n p m<n n<p)

<-trans2 : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans2 {p = suc p} z<s n<p = z<s {p}
<-trans2 (s<s m<n) (s<s n<p) = s<s (<-trans2 m<n n<p)

≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero (suc n) _ = z<s
≤-iff-< (suc m) (suc n) (s≤s m<n) = s<s (≤-iff-< m n m<n)

-- _ : zero ≡ zero
-- _ = refl

-- mine
data Trichotomy (m n : ℕ) : Set where
  trile : m < n → Trichotomy m n
  trigt : n < m → Trichotomy m n
  triequal : m ≡ n → Trichotomy m n

-- mine
trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = triequal refl
trichotomy zero (suc n) = trile (z<s)
trichotomy (suc m) zero = trigt (z<s)
trichotomy (suc m) (suc n) with trichotomy m n
... | trile m<n = trile (s<s m<n)
... | trigt n<m = trigt (s<s n<m)
... | triequal m≡n = triequal (cong suc m≡n)

-- even/odd section

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

--

-- exercise (stretch), mine
o+o≡e : ∀ {i j : ℕ} → odd i → odd j → even (i + j)
o+o≡e oi@(suc zero) oj@(suc zero) = suc (suc zero)
o+o≡e oi@(suc zero) oj@(suc (suc oj')) = suc (suc (o+o≡e oi oj'))
o+o≡e oi@(suc (suc oi')) oj = suc (suc (o+o≡e oi' oj))

--

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

data Can : Bin → Set where
  ⟨⟩ : Can (⟨⟩ I)
  _O : ∀ {b : Bin} → Can b → Can (b O)
  -- _O : ∀ {b : Bin} {n : b ≢ ⟨⟩} → Can b → Can (b O)
  _I : ∀ {b : Bin} → Can b → Can (b I)

open import Data.Empty

_ : Can ⟨⟩ → ⊥
_ = \ ()

-- _ : Can (⟨⟩ O)
-- _ = ⟨⟩

_ : Can (⟨⟩ I)
_ = ⟨⟩

_ : Can (⟨⟩ I O)
_ = ⟨⟩ O

_ : Can (⟨⟩ I I)
_ = ⟨⟩ I

_ : Can (⟨⟩ I O O)
_ = ⟨⟩ O O

main = run {0ℓ} (putStrLn "complies")
