{-# OPTIONS --sized-types #-}
open import SynchronizationTree
open import Action
open import Relation.Binary.Core

open import Codata.Sized.Thunk
open import Size

module _ {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  import Syntax
  open Syntax A _≈_ {Action}

  data ⟦_⟧≡_ : CCS → {i : Size} →  Tree Aτ i → Set ℓ where
    empty : ⟦ ∅ ⟧≡ leaf

    prefix : ∀ {α} {i} {P : CCS} {T : Tree Aτ i} →
      ⟦ P ⟧≡ T →
      ⟦ α ∙ P ⟧≡ node {i = ∞} α (record { force = [ T ] })
