open import Level renaming (suc to lsuc)
open import Relation.Binary.Core using (Rel)
open import Data.Sum
open import Data.Empty
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable

module Action {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) (dec : Decidable _≈_) where

  data Tau : Set where
    tau : Tau

  record Act : Set (lsuc ℓ) where
    field
      comp : A → A
      compp : ∀ (a : A) → comp (comp a) ≈ a

    Aτ : Set ℓ
    Aτ = A ⊎ Tau

    τ : Aτ
    τ = inj₂ tau

    act : A → Aτ
    act = inj₁

    _≉_ : Rel A ℓ
    a ≉ b = a ≈ b → ⊥

    _≈ᶜ_ : A → A → Set ℓ
    a ≈ᶜ a' = a ≈ a' ⊎ a ≈ (comp a')

    decᶜ : Decidable _≈ᶜ_
    decᶜ x y with dec x y
    ... | no ¬a with dec x (comp y)
    decᶜ x y | no ¬a | no ¬b = no (λ {(inj₁ p) → ¬a p ; (inj₂ q) → ¬b q})
    decᶜ x y | no ¬a | yes b = yes (inj₂ b)
    decᶜ x y | yes a = yes (inj₁ a)

  module Renaming (Action : Act) where
    open Act Action
    record IsRenaming (f : A → A) : Set ℓ where
      field
        respects-comp : ∀ {a : A} →
          f (comp a) ≈ comp (f a)

    record Renaming : Set ℓ where
      field
        f : A → A
        isRenaming : IsRenaming f

    -- apply a renaming
    _$_ : Renaming → A → A
    f $ a = Renaming.f f a

    -- lift (A → A) to (Aτ → Aτ)
    ⟨_⟩Aτ : Renaming → Aτ → Aτ
    ⟨ φ ⟩Aτ (inj₁ a) = inj₁ (φ $ a)
    ⟨ φ ⟩Aτ (inj₂ tau) = inj₂ tau
