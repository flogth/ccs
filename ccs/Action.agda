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

    data _≈_ : Aτ → Aτ → Set ℓ where
      τ-eq : inj₂ tau ≈ inj₂ tau

      a-eq : ∀ {a b : A} → a ≡ b → inj₁ a ≈ inj₁ b

      a-eq-comp : ∀ {a b : A} → a ≡ comp b → inj₁ a ≈ inj₁ b

    ≈-dec : Decidable _≈_
    ≈-dec (inj₁ x) (inj₁ y) with dec x y | dec x (comp y)
    ... | yes p | yes q = yes (a-eq p)
    ... | yes p | no q = yes (a-eq p)
    ... | no p  | yes q = yes (a-eq-comp q)
    ... | no p  | no q = no λ {(a-eq a) → p a ; (a-eq-comp b) → q b}
    ≈-dec (inj₁ x) (inj₂ y) = no λ ()
    ≈-dec (inj₂ y) (inj₁ x) = no λ ()
    ≈-dec (inj₂ tau) (inj₂ tau) = yes τ-eq

    _≉_ : Aτ → Aτ → Set ℓ
    a ≉ b = a ≈ b → ⊥

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
