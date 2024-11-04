{-# OPTIONS --guardedness #-}
open import Action
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Data.Product
import Syntax

module Bisimilarity {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open import Syntax {ℓ} A {dec} {Action}

  module _ (step : ∀ {n} → Proc n → Aτ → Proc n → Set ℓ) where

  -- Strong Bisimilarity
    record _~_ {n} (s t : Proc n) : Set ℓ where
      coinductive
      field
        forth : ∀ {α} {s'} →
         step s α s' →
         Σ (Proc n) λ t' → step t α t'

        back : ∀ {α} {t'} →
         step t α t' →
         Σ (Proc n) λ s' → step s α s'
    open _~_

    reflexive : ∀ {n} → Reflexive (_~_ {n})
    reflexive = record {
        forth = λ {α} {s'} z → s' , z
      ; back = λ {α} {t'} z → t' , z }

    symmetric : ∀ {n} → Symmetric (_~_ {n})
    symmetric z = record { forth = back z ; back = forth z }

    transitive : ∀ {n} → Transitive (_~_ {n})
    transitive i~j j~k = record {
        forth = λ step → forth j~k (proj₂ (forth i~j step))
      ; back = λ step → back i~j (proj₂ (back j~k step)) }

    equivalence : ∀ {n} →  IsEquivalence (_~_ {n})
    equivalence = record {
        refl = reflexive
      ; sym = symmetric
      ; trans = transitive }
