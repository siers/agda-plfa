module quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product as P using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′; map)
open import Function.Base using (id; _∘_; _∋_)
open import isomorphism using (_≃_; extensionality)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} → (∀ (a : A) → B a × C a) ≃ (∀ (a : A) → B a) × (∀ (a : A) → C a)
∀-distrib-× =
  record
    { to = λ ap → ⟨ (proj₁ ∘ ap) , (proj₂ ∘ ap) ⟩
    ; from = λ (⟨ ab , ac ⟩) → λ a → ⟨ ab a , ac a ⟩
    ; from∘to = λ _ → refl
    ; to∘from = λ _ → refl
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- _ : 3 ≡ [ (_+ 3) , (_+ 2) ] (ℕ ⊎ ℕ ∋ inj₁ 0)
-- _ = refl

[]∘map : ∀ {A B AA BB Z : Set} → (f : A → B) → (g : B → Z) → (ff : AA → BB) → (gg : BB → Z) → (∀ (s : A ⊎ AA) → ([ g , gg ]′ ∘ map f ff) s ≡ [ (g ∘ f) , (gg ∘ ff) ]′ s)
[]∘map f g ff gg (inj₁ _) = refl
[]∘map f g ff gg (inj₂ _) = refl

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ a , bc ⟩ → map ⟨ a ,_⟩ ⟨ a ,_⟩ bc}
    ; from = [ (λ{⟨ a , b ⟩ → ⟨ a , inj₁ b ⟩}) , (λ{⟨ a , c ⟩ → ⟨ a , inj₂ c ⟩}) ]
    ; from∘to = λ{ ⟨ a , (inj₁ b) ⟩ → refl ; ⟨ a , (inj₂ c) ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ a , b ⟩) → refl ; (inj₁ ⟨ a , b ⟩) → refl }
    }
