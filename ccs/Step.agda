open import Action
open import Relation.Binary.Core using (Rel)
open import Data.Empty

module Step {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  import Syntax
  open Syntax A _≈_ {Action}

  _≉_ : Rel A ℓ
  a ≉ b = a ≈ b → ⊥

  -- one-step relation without `fix`
  infix 3 _⟨_⟩⇒_
  data _⟨_⟩⇒_ : CCS → Aτ → CCS → Set ℓ where
    Prefix : ∀ {α} {P} →
    ------------------------
      α ∙ P ⟨ α ⟩⇒ P

    Sumₗ : ∀ {α} {P Q P'} →
      P ⟨ α ⟩⇒ P' →
      ---------------------
      (P ＋ Q) ⟨ α ⟩⇒ P'

    Sumᵣ : ∀ {α} {P Q Q'} →
      Q ⟨ α ⟩⇒ Q' →
      ------------------
      (P ＋ Q) ⟨ α ⟩⇒ Q'

    Compₗ : ∀ {α} {P Q P'} →
      P ⟨ α ⟩⇒ P' →
      -------------------
      P ∣ Q ⟨ α ⟩⇒ P' ∣ Q

    Compᵣ : ∀ {α} {P Q Q'} →
      Q ⟨ α ⟩⇒ Q' →
      -------------------
      P ∣ Q ⟨ α ⟩⇒ P ∣ Q'

    Sync : ∀ {a : A} {P P' Q Q'} →
      P ⟨ act a ⟩⇒ P' →
      Q ⟨ act (comp a)  ⟩⇒ Q' →
      --------------------
      P ∣ Q ⟨ τ ⟩⇒ P' ∣ Q'

    Res : ∀ {a b : A}  {P P'} →
      P ⟨ act a ⟩⇒ P' →
      a ≉  b →
      a ≉ comp b →
      ---------------------------
      (P ∖ a) ⟨ act a ⟩⇒ (P' ∖ a)

    Ren : ∀ {a} {φ : Renaming} {P P'} →
      P ⟨ act a ⟩⇒ P' →
      -------------------------------------
      (P [ φ ]) ⟨ act (φ $ a) ⟩⇒ (P' [ φ ])

  infix 3 _⟨_⟩fix⇒_
  data _⟨_⟩fix⇒_ : CCS → Aτ → CCS → Set ℓ where
    Step : ∀ {α} {P P'} →
      P ⟨ α ⟩⇒ P' →
      --------------
      P ⟨ α ⟩fix⇒ P'
    Fix : ∀ {α} {P P'} →
      (P [ zero ↦ fix P ]) ⟨ α ⟩fix⇒ P' →
      fix P ⟨ α ⟩fix⇒ P'

  infix 3 _⟨_⟩fix'⇒_
  data _⟨_⟩fix'⇒_ : CCS → Aτ → CCS → Set ℓ where
    Step' : ∀ {α} {P P'} →
      P ⟨ α ⟩⇒ P' →
      P ⟨ α ⟩fix'⇒ P'
    Fix' : ∀ {α} {P P'} →
      P ⟨ α ⟩fix'⇒ P' →
      fix P ⟨ α ⟩fix'⇒ (P' [ zero ↦  fix P ])
