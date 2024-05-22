{-# OPTIONS --guardedness #-}
open import Action
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Data.Product
import Syntax

module Bisimilarity {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where

  open Act Action
  open Syntax A _≈_ {Action}

  module _ (step : CCS → Aτ → CCS → Set ℓ) where

    record _~_ (s t : CCS) : Set ℓ where
      coinductive
      field
        l : ∀ {α} {s'} →
         step s α s' →
         Σ CCS λ t' → step t α t'

        r : ∀ {α} {t'} →
         step t α t' →
         Σ CCS λ s' → step s α s'
    open _~_

    reflexive : Reflexive _~_
    reflexive = record {
      l = λ {α} {s'} step → s' , step
      ; r = λ {α} {t'} step → t' , step }

    symmetric : Symmetric _~_
    symmetric {x} {y} x~y = record {
      l = λ step → r x~y step
      ; r = λ  step → l x~y step }

    transitive : Transitive _~_
    transitive i~j j~k = record {
      l = λ step → l j~k (proj₂ (l i~j step))
      ; r = λ step → r i~j (proj₂ (r j~k step)) }

    equivalence : IsEquivalence _~_
    equivalence = record {
      refl = reflexive
      ; sym = symmetric
      ; trans = transitive }
