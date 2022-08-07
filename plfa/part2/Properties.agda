module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N} → M —→ N → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

data Progress (M : Term) : Set where
  step : ∀ {N} → M —→ N → Progress M
  done : Value M → Progress M

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M

progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done (V-zero)                         =  step β-zero
... | done (V-suc VL)                       =  step (β-suc VL)
progress (⊢μ ⊢M)                            =  step β-μ

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢m with progress ⊢m
... | step (m—→n) = no (—→¬V m—→n)
... | done v = yes v

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)    =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)  =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero      =  ⊢zero
rename ρ (⊢suc ⊢M)  =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)
                    =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)    =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢ƛ (drop ⊢N)
... | no  x≢y       =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)  =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero      =  ⊢zero
subst ⊢V (⊢suc ⊢M)  =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl      =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y       =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl      =  ⊢μ (drop ⊢M)
... | no  x≢y       =  ⊢μ (subst ⊢V (swap x≢y ⊢M))

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where
  done : Value N → Finished N
  out-of-gas : Finished N

data Steps (L : Term) : Set where
  steps : ∀ {N} → L —↠ N → Finished N → Steps L

eval : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Steps L
eval {L} (gas zero)    ⊢L                     =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                 =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
... | steps M—↠N fin                       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

-- in nvim-agda: use <Leader>n (AgdaCompute) to convert to the steps (... ∎) out-of-gas
_ : eval (gas 3) ⊢sucμ ≡
  steps
  (μ "x" ⇒ (`suc (` "x"))
  —→⟨ β-μ ⟩
  `suc (μ "x" ⇒ (`suc (` "x")))
  —→⟨ ξ-suc β-μ ⟩
  `suc (`suc (μ "x" ⇒ (`suc (` "x"))))
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
  `suc (`suc (`suc (μ "x" ⇒ (`suc (` "x"))))) ∎)
  out-of-gas
_ = refl

four : Term
four = `suc `suc `suc `suc `zero

⊢four : ∀ {Γ} → Γ ⊢ four ⦂ `ℕ
⊢four = ⊢suc (⊢suc (⊢suc (⊢suc ⊢zero)))

⊢mul·two·two : ∀ {Γ} → Γ ⊢ mul · two · two ⦂ `ℕ
⊢mul·two·two = ⊢mul · ⊢two · ⊢two

-- this is one of those it "takes pages to prove 2 * 2 is 4"
⊢mul-eval : eval (gas 100) ⊢mul·two·two ≡ steps (
  (μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `suc (`suc `zero) · `suc (`suc `zero)
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc (`suc `zero) · `suc (`suc `zero)
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc (`suc `zero) ·
  ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ]
  —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc (`suc `zero) · ((μ "*" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ (μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "n" · (` "*" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ])
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · ((ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ]
  —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc `zero · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc ((ƛ "n" ⇒ case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ]
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `zero · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc ((ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc `zero)))
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero))))) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc `zero)) ])
  —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
  (ƛ "n" ⇒ case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc (`suc (`suc `zero)))
  —→⟨ β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero)))) ⟩
  case `suc (`suc `zero) [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc (`suc (`suc `zero)))) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `suc `zero · `suc (`suc (`suc (`suc `zero))))
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  `suc ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `suc `zero · `suc (`suc (`suc (`suc `zero))))
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  `suc ((ƛ "n" ⇒ case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc (`suc (`suc `zero))))
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero))))) ⟩
  `suc case `suc `zero [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc (`suc (`suc `zero)))) ]
  —→⟨ ξ-suc (β-suc V-zero) ⟩
  `suc (`suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · `zero · `suc (`suc (`suc (`suc `zero)))))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  `suc (`suc ((ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ])) · `zero · `suc (`suc (`suc (`suc `zero)))))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
  `suc (`suc ((ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · ` "n") ]) · `suc (`suc (`suc (`suc `zero)))))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero)))))) ⟩
  `suc (`suc case `zero [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc "m" ⇒ `suc ((μ "+" ⇒ (ƛ "m" ⇒ (ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]))) · ` "m" · `suc (`suc (`suc (`suc `zero)))) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
  `suc (`suc (`suc (`suc (`suc (`suc `zero))))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc (V-suc (V-suc V-zero)))))))
⊢mul-eval = refl
