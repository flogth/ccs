open import Action
open import Relation.Binary.Core using (Rel)

module Step {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  import Syntax
  open Syntax A _≈_ {Action}

  infix 10 _⟨_⟩⇒_

  data _⟨_⟩⇒_ : {n m : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc m) → Set ℓ where
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
  data _⟨_⟩fix'⇒_ : {n m : ℕ} → (P : Proc n) → (α : Aτ) → (Q : Proc m) → Set ℓ where
    Step' : ∀ {n} {α : Aτ} {P P' : Proc n} →
      P ⟨ α ⟩⇒ P' →
      ----------------------------------------
      P ⟨ α ⟩fix'⇒ P'

    Fix' : ∀ {n} {α : Aτ} {P P' : Proc (suc n)}  →
      P ⟨ α ⟩fix'⇒ P' →
      ----------------------------------------
      (fix P) ⟨ α ⟩fix'⇒ (P' [0↦ (fix P) ])

  -- Equivalence of the two semantics
  
  fix-equiv-to : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (s : P ⟨ α ⟩fix⇒ P') →
    P ⟨ α ⟩fix'⇒ P'
  fix-equiv-to (Step s) = Step' s
  fix-equiv-to (Fix {P = ∅} (Step ()))
  fix-equiv-to (Fix {P = # x} s) = {!!}
  fix-equiv-to (Fix {P = α ∙ P} s) = {!!}
  fix-equiv-to (Fix {P = P ＋ Q} s) = {!!}
  fix-equiv-to (Fix {P = P ∣ Q} s) = {!!}
  fix-equiv-to (Fix {P = P ∖ a} s) = {!!}
  fix-equiv-to (Fix {P = P [ φ ]} s) = {!!}
  fix-equiv-to (Fix {P = fix P} s) = {!!}

  fix-equiv-from : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (s : P ⟨ α ⟩fix'⇒ P') →
    P ⟨ α ⟩fix⇒ P'
  fix-equiv-from (Step' s) = Step s
  fix-equiv-from (Fix' {P = ∅} (Step' ()))
  fix-equiv-from (Fix' {P = # x} s) = {!!}
  fix-equiv-from (Fix' {P = α ∙ P} s) = {!!}
  fix-equiv-from (Fix' {P = P ＋ Q} s) = {!!}
  fix-equiv-from (Fix' {P = P ∣ Q} s) = {!!}
  fix-equiv-from (Fix' {P = P ∖ a} s) = {!!}
  fix-equiv-from (Fix' {P = P [ φ ]} s) = {!!}
  fix-equiv-from (Fix' {P = fix P} s) = {!!}
