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

  data Context : Set ℓ where
    ∅ : Context
    _,_ : Context → CCS → Context

  data _∋_ : Context → CCS → Set ℓ where
    Z : ∀ {Γ A} → (Γ , A) ∋ A

    S_ : ∀ {Γ A B} →
      Γ ∋ A →
      (Γ , B) ∋ A

  -- one-step relation without `fix`
  infix 3 _⊢_⟨_⟩⇒_
  data _⊢_⟨_⟩⇒_ : Context → CCS → Aτ → CCS → Set ℓ where
    Prefix : ∀ {α} {P} {Γ} →
    ------------------------
      Γ ⊢ α ∙ P ⟨ α ⟩⇒ P

    Sumₗ : ∀ {α} {P Q P'} {Γ} →
      Γ ⊢ P ⟨ α ⟩⇒ P' →
      ---------------------
      Γ ⊢ (P ＋ Q) ⟨ α ⟩⇒ P'

    Sumᵣ : ∀ {α} {P Q Q'} {Γ} →
      Γ ⊢ Q ⟨ α ⟩⇒ Q' →
      ------------------
      Γ ⊢ (P ＋ Q) ⟨ α ⟩⇒ Q'

    Compₗ : ∀ {α} {P Q P'} {Γ} →
      Γ ⊢ P ⟨ α ⟩⇒ P' →
      -------------------
      Γ ⊢ P ∣ Q ⟨ α ⟩⇒ P' ∣ Q

    Compᵣ : ∀ {α} {P Q Q'} {Γ} →
      Γ ⊢ Q ⟨ α ⟩⇒ Q' →
      -------------------
      Γ ⊢ P ∣ Q ⟨ α ⟩⇒ P ∣ Q'

    Sync : ∀ {a : A} {P P' Q Q'} {Γ} →
      Γ ⊢ P ⟨ act a ⟩⇒ P' →
      Γ ⊢ Q ⟨ act (comp a)  ⟩⇒ Q' →
      --------------------
      Γ ⊢ P ∣ Q ⟨ τ ⟩⇒ P' ∣ Q'

    Res : ∀ {a b : A}  {P P'} {Γ} →
      Γ ⊢ P ⟨ act a ⟩⇒ P' →
      a ≉  b →
      a ≉ comp b →
      ---------------------------
      Γ ⊢ (P ∖ a) ⟨ act a ⟩⇒ (P' ∖ a)

    Ren : ∀ {a} {φ : Renaming} {P P'} {Γ} →
      Γ ⊢ P ⟨ act a ⟩⇒ P' →
      -------------------------------------
      Γ ⊢ (P [ φ ]) ⟨ act (φ $ a) ⟩⇒ (P' [ φ ])

  -- usual semantics of fixpoint
  infix 3 _⊢_⟨_⟩fix⇒_
  data _⊢_⟨_⟩fix⇒_ : Context → CCS → Aτ → CCS → Set ℓ where
    Step : ∀ {α} {P P'} {Γ} →
      Γ ⊢ P ⟨ α ⟩⇒ P' →
      ------------------
      Γ ⊢ P ⟨ α ⟩fix⇒ P'

    Fix : ∀ {α} {P P'} {Γ} →
      Γ ⊢ (P [ zero ↦ fix P ]) ⟨ α ⟩fix⇒ P' →
      -------------------------------------
      Γ ⊢ fix P ⟨ α ⟩fix⇒ P'

  -- alternative semantics of fixpoint
  infix 3 _⊢_⟨_⟩fix'⇒_
  data _⊢_⟨_⟩fix'⇒_ : Context → CCS → Aτ → CCS → Set ℓ where
    Step' : ∀ {α} {P P'} {Γ} →
      Γ ⊢ P ⟨ α ⟩⇒ P' →
      -------------------
      Γ ⊢ P ⟨ α ⟩fix'⇒ P'

    Fix' : ∀ {α} {P P'} {Γ} →
      (Γ , fix P) ⊢ P ⟨ α ⟩fix'⇒ P' →
      -------------------------------------------
      Γ ⊢ fix P ⟨ α ⟩fix'⇒ (P' [ zero ↦  fix P ])
