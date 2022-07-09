module negation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (suc-injective; ≤-pred)
open import Data.Nat using (ℕ; zero; _+_; _*_; _≤_; suc; s≤s; z≤n; _<_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

open import isomorphism using (_≃_; extensionality)

<-irreflexive : ∀ n → ¬ (n < n)
<-irreflexive (suc m) (s≤s m≤m) = <-irreflexive m m≤m

trichotomy : Trichotomous (_≡_) (_<_)
trichotomy zero    zero    = tri≈ (λ()) refl (λ())
trichotomy zero    (suc n) = tri< (s≤s (z≤n {n})) (λ()) (λ())
trichotomy (suc n) zero    = tri> (λ()) (λ()) (s≤s (z≤n {n}))
trichotomy (suc n) (suc m) with trichotomy n m
... | tri< n<m n≉m n≯m = tri< (s≤s n<m)      (n≉m ∘ suc-injective) (n≯m ∘ ≤-pred)
... | tri≈ n≮m n≈m n≯m = tri≈ (n≮m ∘ ≤-pred) (cong suc n≈m)        (n≯m ∘ ≤-pred)
... | tri> n≮m n≉m n>m = tri> (n≮m ∘ ≤-pred) (n≉m ∘ suc-injective) (s≤s n>m)
