open import Action
open import Relation.Binary.Core using (Rel)
open import Data.Fin
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; sym) renaming (subst to ≡-subst)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List; _∷_ ; []; _++_; map)

module Step {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  import Syntax
  open Syntax A {dec} {Action}
  open import Guarded A {dec} {Action}

  infix 10 _⟨_⟩⇒_

  data _⟨_⟩⇒_ : {n : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc n) → Set ℓ where
    Prefix : ∀ {n} {α : Aτ} {P : Proc n} →
      (α ∙ P) ⟨ α ⟩⇒ P

    Sumₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      (P ＋ Q) ⟨ α ⟩⇒ P'

    Sumᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} →
      Q ⟨ α ⟩⇒ Q' →
      ----------------------------------------
      (P ＋ Q) ⟨ α ⟩⇒ Q'

    Compₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      (P ∣ Q) ⟨ α ⟩⇒ (P' ∣ Q)

    Compᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} →
      Q ⟨ α ⟩⇒ Q' →
      ----------------------------------------
      (P ∣ Q) ⟨ α ⟩⇒ (P ∣ Q')

    Sync : ∀ {n} {a : A} {P P' Q Q' : Proc n} →
      P ⟨ act a ⟩⇒ P' →
      Q ⟨ act (comp a) ⟩⇒ Q' →
      ----------------------------------------
      (P ∣ Q) ⟨ τ ⟩⇒ (P' ∣ Q')

    Res : ∀ {n} {α} {a : A} {P P' : Proc n} →
      P ⟨ α ⟩⇒ P' →
      α ≢ act a →
      α ≢ act (comp a) →
      ----------------------------------------
      (P ∖ a) ⟨ act a ⟩⇒ (P' ∖ a)

    Ren : ∀ {n} {α} {φ : Renaming} {P P' : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      (P [ φ ]) ⟨ ⟨ φ ⟩Aτ α ⟩⇒ (P' [ φ ])

  -- usual operational semantics of fixpoint
  infix 10 _⟨_⟩fix⇒_
  data _⟨_⟩fix⇒_ : {n : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc n) → Set ℓ where
    Step : ∀ {n} {α : Aτ} {P P' : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      P ⟨ α ⟩fix⇒ P'

    Fix : ∀ {n} {α : Aτ} {P : Proc (suc n)} {P' : Proc n} →
      (P [0↦ fix P ]) ⟨ α ⟩fix⇒ P' →
      ----------------------------------------
      (fix P) ⟨ α ⟩fix⇒ P'

  -- adapted fixpoint semantics
  infix 10 _⟨_⟩fix'⇒_
  data _⟨_⟩fix'⇒_ : {n : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc n) → Set ℓ where
    Step' : ∀ {n} {α : Aτ} {P P' : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      P ⟨ α ⟩fix'⇒ P'

    Fix' : ∀ {n} {α : Aτ} {P P' : Proc (suc n)}  →
      P ⟨ α ⟩fix'⇒ P' →
      ----------------------------------------
      (fix P) ⟨ α ⟩fix'⇒ (P' [0↦ (fix P) ])

  infix 10 _⟨_⟩_⇒_

  data _⟨_⟩_⇒_ : {n m : ℕ} → (P : Proc n) → (α : Aτ) → Subst n m → (Q : Proc m) → Set ℓ where
    Prefix : ∀ {n} {α : Aτ} {P : Proc n} {σ : Subst n n} →
      α ∙ P ⟨ α ⟩ σ ⇒ (⟪ σ ⟫ P)

    Sumₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} {σ : Subst n n} →
         P ⟨ α ⟩ σ ⇒ P' →
      ----------------------------------------
        (P ＋ Q) ⟨ α ⟩ σ ⇒ P'

    Sumᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} {σ : Subst n n} →
         Q ⟨ α ⟩ σ ⇒ Q' →
      ----------------------------------------
        (P ＋ Q) ⟨ α ⟩ σ ⇒ Q'

    Compₗ : ∀ {n} {α : Aτ} {P P' Q : Proc n} {σ : Subst n n} →
          P ⟨ α ⟩ σ ⇒ P' →
      ----------------------------------------
        (P ∣ Q) ⟨ α ⟩ σ ⇒ (P' ∣ ⟪ σ ⟫ Q)

    Compᵣ : ∀ {n} {α : Aτ} {P Q Q' : Proc n} {σ : Subst n n} →
          Q ⟨ α ⟩ σ ⇒ Q' →
      ----------------------------------------
        (P ∣ Q) ⟨ α ⟩ σ ⇒ ((⟪ σ ⟫ P) ∣ Q')

    Sync : ∀ {n} {a : A} {P P' Q Q' : Proc n} {σ : Subst n n} →
         P ⟨ act a ⟩ σ ⇒ P' →
         Q ⟨ act (comp a) ⟩ σ ⇒ Q' →
      ----------------------------------------
        (P ∣ Q) ⟨ τ ⟩ σ ⇒ (P' ∣ Q')

    Res : ∀ {n} {α} {a : A} {P P' : Proc n} {σ : Subst n n} →
        P ⟨ α ⟩ σ ⇒ P' →
        α ≢ act a →
        α ≢ act (comp a) →
      ----------------------------------------
        (P ∖ a) ⟨ act a ⟩ σ ⇒ (P' ∖ a)

    Ren : ∀ {n} {α} {φ : Renaming} {P P' : Proc n} {σ : Subst n n} →
        P ⟨ α ⟩ σ ⇒ P' →
      ----------------------------------------
        (P [ φ ]) ⟨ ⟨ φ ⟩Aτ α ⟩ σ ⇒ (P' [ φ ])

    Fix : ∀ {n} {α} {P : Proc (suc n)} {P' : Proc n} {σ : Subst n n} →
        P ⟨ α ⟩ subst-zero (fix P) ⨾ σ ⇒ P' →
      ----------------------------------------
        fix P ⟨ α ⟩ σ ⇒ P'
