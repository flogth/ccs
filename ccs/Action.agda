open import Level renaming (suc to lsuc)
open import Data.Sum
open import Data.Empty
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

module Action {ℓ} (A : Set ℓ) (dec : DecidableEquality A) where

  data Tau : Set where
    tau : Tau

  record Act : Set (lsuc ℓ) where
    field
      comp : A → A
      compp : ∀ (a : A) → comp (comp a) ≡ a

    Aτ : Set ℓ
    Aτ = A ⊎ Tau

    τ : Aτ
    τ = inj₂ tau

    act : A → Aτ
    act = inj₁

    _≈_ : A → A → Set ℓ
    a ≈ a' = a ≡ a' ⊎ a ≡ (comp a')

    ≈-dec : Decidable _≈_
    ≈-dec x y with dec x y
    ... | no ¬a with dec x (comp y)
    ≈-dec x y | no ¬a | no ¬b = no (λ {(inj₁ p) → ¬a p ; (inj₂ q) → ¬b q})
    ≈-dec x y | no ¬a | yes b = yes (inj₂ b)
    ≈-dec x y | yes a = yes (inj₁ a)

  module Renaming (Action : Act) where
    open Act Action
    record IsRenaming (f : A → A) : Set ℓ where
      field
        respects-comp : ∀ {a : A} →
          f (comp a) ≡ comp (f a)

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
