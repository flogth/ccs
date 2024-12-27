open import Action
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product
open import Data.Nat

module Step.SubstitutionLabels {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Syntax A {dec} {Action}
  open import Step A

  infix 10 _⟨_⟩⇒_
  data _⟨_⟩⇒_ : {n m : ℕ} → (P : Proc n) → (Aτ × Subst n m) → (Q : Proc m) → Set ℓ where
    Prefix : ∀ {n m} {α : Aτ} {P : Proc n} {σ : Subst n m} →
      α ∙ P ⟨ α , σ ⟩⇒ (⟪ σ ⟫ P)

    Sumₗ : ∀ {n m} {α : Aτ} {P Q : Proc n} {P' : Proc m} {σ : Subst n m} →
         P ⟨ α , σ ⟩⇒ P' →
      ----------------------------------------
        (P ＋ Q) ⟨ α , σ ⟩⇒ P'

    Sumᵣ : ∀ {n m} {α : Aτ} {P Q : Proc n} {Q' : Proc m} {σ : Subst n m} →
         Q ⟨ α , σ ⟩⇒ Q' →
      ----------------------------------------
        (P ＋ Q) ⟨ α , σ ⟩⇒ Q'

    Compₗ : ∀ {n m} {α : Aτ} {P Q : Proc n} {P' : Proc m} {σ : Subst n m} →
          P ⟨ α , σ ⟩⇒ P' →
      ----------------------------------------
        (P ∣ Q) ⟨ α , σ ⟩⇒ (P' ∣ ⟪ σ ⟫ Q)

    Compᵣ : ∀ {n m} {α : Aτ} {P Q : Proc n} {Q' : Proc m} {σ : Subst n m} →
          Q ⟨ α , σ ⟩⇒ Q' →
      ----------------------------------------
        (P ∣ Q) ⟨ α , σ ⟩⇒ ((⟪ σ ⟫ P) ∣ Q')

    Sync : ∀ {n m} {a : A} {P Q : Proc n} {P' Q' : Proc m} {σ : Subst n m} →
         P ⟨ act a , σ ⟩⇒ P' →
         Q ⟨ act (comp a) , σ ⟩⇒ Q' →
      ----------------------------------------
        (P ∣ Q) ⟨ τ , σ ⟩⇒ (P' ∣ Q')

    Res : ∀ {n m} {α} {a : A} {P : Proc n} {P' : Proc m} {σ : Subst n m} →
        P ⟨ α , σ ⟩⇒ P' →
        α ≉ act a →
      ----------------------------------------
        (P ∖ a) ⟨ act a , σ ⟩⇒ (P' ∖ a)

    Ren : ∀ {n m} {α} {φ : Renaming} {P : Proc n} {P' : Proc m} {σ : Subst n m} →
        P ⟨ α , σ ⟩⇒ P' →
      ----------------------------------------
        (P [ φ ]) ⟨ ⟨ φ ⟩Aτ α , σ ⟩⇒ (P' [ φ ])

    Fix : ∀ {n m} {α} {P : Proc (suc n)} {P' : Proc m} {σ : Subst n m} →
        P ⟨ α , (subst-zero (fix P)) ⨾ σ ⟩⇒ P' →
      ----------------------------------------
        fix P ⟨ α , σ ⟩⇒ P'

  step : LTS (Aτ × ∀ {n m} → Subst n m)
  step .LTS.step P (a , s ) Q = P ⟨ a , s ⟩⇒ Q
