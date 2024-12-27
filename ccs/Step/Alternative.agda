open import Action
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat

module Step.Alternative {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Syntax A {dec} {Action}
  open import Step A

  infix 10 _⟨_⟩fix⇒_
  data _⟨_⟩fix⇒_ : {n m : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc m) → Set ℓ where
    Prefix : ∀ {n} {α : Aτ} {P : Proc n} →
      (α ∙ P) ⟨ α ⟩fix⇒ P

    Sumₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} →
      P ⟨ α ⟩fix⇒ P' →
      ----------------------------------------
      (P ＋ Q) ⟨ α ⟩fix⇒ P'

    Sumᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} →
      Q ⟨ α ⟩fix⇒ Q' →
      ----------------------------------------
      (P ＋ Q) ⟨ α ⟩fix⇒ Q'

    Compₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} →
      P ⟨ α ⟩fix⇒ P' →
      ----------------------------------------
      (P ∣ Q) ⟨ α ⟩fix⇒ (P' ∣ Q)

    Compᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} →
      Q ⟨ α ⟩fix⇒ Q' →
      ----------------------------------------
      (P ∣ Q) ⟨ α ⟩fix⇒ (P ∣ Q')

    Sync : ∀ {n} {a : A} {P P' Q Q' : Proc n} →
      P ⟨ act a ⟩fix⇒ P' →
      Q ⟨ act (comp a) ⟩fix⇒ Q' →
      ----------------------------------------
      (P ∣ Q) ⟨ τ ⟩fix⇒ (P' ∣ Q')

    Res : ∀ {n} {α} {a : A} {P P' : Proc n} →
      P ⟨ α ⟩fix⇒ P' →
      α ≉ act a →
      ----------------------------------------
      (P ∖ a) ⟨ act a ⟩fix⇒ (P' ∖ a)

    Ren : ∀ {n} {α} {φ : Renaming} {P P' : Proc n} →
      P ⟨ α ⟩fix⇒ P' →
      ----------------------------------------
      (P [ φ ]) ⟨ ⟨ φ ⟩Aτ α ⟩fix⇒ (P' [ φ ])

    Fix : ∀ {n} {α : Aτ} {P P' : Proc (suc n)}  →
      P ⟨ α ⟩fix⇒ P' →
      ----------------------------------------
      (fix P) ⟨ α ⟩fix⇒ (P' [0↦ (fix P) ])

  step : LTS Aτ
  step .LTS.step = _⟨_⟩fix⇒_
