{-# OPTIONS --guardedness #-}
open import Action

open import Relation.Binary.Core
open import Relation.Binary.Structures

module SumSemilattice {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where

  import Syntax
  open Syntax A _≈_ {Action}
  import Bisimilarity
  open Bisimilarity A _≈_ {Action}

  -- ＋-congruent : Congruent₂ _~_ _＋_
  -- ＋-congruent {x} {y} {u} {v} x~y u~v = record {
  --   l = ll
  --   ; r = rr }
  --   where ll : {α : Action A} {s' : CCS} → x ＋ u ⟨ α ⟩⇒ s' →
  --              Σ CCS (λ t' → (y ＋ v) ⟨ α ⟩⇒ t')
  --         ll {α} {s'} (sumₗ step) = let p = (l x~y step) in
  --                                       proj₁ p , sumₗ (proj₂ p)
  --         ll {α} {s'} (sumᵣ step) = let p = (l u~v step) in
  --                                       proj₁ p , sumᵣ (proj₂ p)

  --         rr : {α : Action A} {t' : CCS} → y ＋ v ⟨ α ⟩⇒ t' →
  --              Σ CCS (λ s' → (x ＋ u) ⟨ α ⟩⇒ s')
  --         rr {α} {t'} (sumₗ step) = let p = (r x~y step) in
  --                                       proj₁ p , sumₗ (proj₂ p)
  --         rr {α} {t'} (sumᵣ step) = let p = (r u~v step) in
  --                                       proj₁ p , sumᵣ (proj₂ p)

  -- ＋-comm : Commutative _~_ _＋_
  -- ＋-comm p q = record {l = ll ; r = rr }
  --   where ll : {α : Action A} {s' : CCS} → p ＋ q ⟨ α ⟩⇒ s' →
  --              Σ CCS (λ t' → (q ＋ p) ⟨ α ⟩⇒ t')
  --         ll {α} {s'} (sumₗ step) = s' , sumᵣ step
  --         ll {α} {s'} (sumᵣ step) = s' , sumₗ step

  --         rr : {α : Action A} {t' : CCS} → q ＋ p ⟨ α ⟩⇒ t' →
  --              Σ CCS (λ s' → (p ＋ q) ⟨ α ⟩⇒ s')
  --         rr {α} {t'} (sumₗ step) = t' , sumᵣ step
  --         rr {α} {t'} (sumᵣ step) = t' , sumₗ step

  -- ＋-assoc : Associative _~_ _＋_
  -- ＋-assoc x y z = record {
  --   l = ll
  --   ; r = rr }
  --   where ll : {α : Action A} {s' : CCS} → (x ＋ y) ＋ z ⟨ α ⟩⇒ s' →
  --              Σ CCS (_⟨_⟩⇒_ (x ＋ (y ＋ z)) α)
  --         ll {α} {s'} (sumₗ (sumₗ step)) = s' , (sumₗ step)
  --         ll {α} {s'} (sumₗ (sumᵣ step)) = s' , (sumᵣ (sumₗ step))
  --         ll {α} {s'} (sumᵣ step) = s' , (sumᵣ (sumᵣ step))

  --         rr : {α : Action A} {t' : CCS} → x ＋ (y ＋ z) ⟨ α ⟩⇒ t' →
  --              Σ CCS (_⟨_⟩⇒_ ((x ＋ y) ＋ z) α)
  --         rr {α} {t'} (sumₗ step) = t' , sumₗ (sumₗ step)
  --         rr {α} {t'} (sumᵣ (sumₗ step)) = t' , (sumₗ (sumᵣ step))
  --         rr {α} {t'} (sumᵣ (sumᵣ step)) = t' , (sumᵣ step)

  -- ＋-idem : Idempotent _~_ _＋_
  -- ＋-idem  x = record {
  --   l = ll
  --   ; r = rr }

  --   where ll : {α : Action A} {s' : CCS} → x ＋ x ⟨ α ⟩⇒ s' →
  --              Σ CCS (_⟨_⟩⇒_ x α)
  --         ll {α} {s'} (sumₗ step) = s' , step
  --         ll {α} {s'} (sumᵣ step) = s' , step

  --         rr : {α : Action A} {t' : CCS} → x ⟨ α ⟩⇒ t' →
  --              Σ CCS (_⟨_⟩⇒_ (x ＋ x) α)
  --         rr {α} {s'} step = s' , (sumₗ step)


  -- ∅＋x : LeftIdentity _~_ ∅ _＋_
  -- ∅＋x x = record { l = ll ; r = rr }
  --   where ll : {α : Action A} {s' : CCS} → ∅ ＋ x ⟨ α ⟩⇒ s' →
  --              Σ CCS (_⟨_⟩⇒_ x α)
  --         ll {α} {s'} (sumᵣ step) = s' , step
  --         rr : {α : Action A} {t' : CCS} → x ⟨ α ⟩⇒ t' →
  --              Σ CCS (_⟨_⟩⇒_ (∅ ＋ x) α)
  --         rr {α} {t'} step = t' , sumᵣ step

  -- x＋∅ : RightIdentity _~_ ∅ _＋_
  -- x＋∅ x = transitive (＋-comm x ∅) (∅＋x x)

  -- ＋-id : Identity _~_ ∅ _＋_
  -- ＋-id = ∅＋x , x＋∅

  -- ＋-monoid : IsMonoid _~_ _＋_ ∅
  -- ＋-monoid = record {
  --   isSemigroup = record {
  --     isMagma = record {
  --       isEquivalence = equivalence
  --       ; ∙-cong = ＋-congruent }
  --     ; assoc = ＋-assoc }
  --   ; identity = ＋-id }

  -- ＋-bounded-semilattice : IsBoundedMeetSemilattice _~_ _＋_ ∅
  -- ＋-bounded-semilattice = record {
  --   isCommutativeMonoid = record {
  --     isMonoid = ＋-monoid
  --     ; comm = ＋-comm }
  --   ; idem = ＋-idem }
