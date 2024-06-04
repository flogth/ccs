{-# OPTIONS --sized-types #-}
open import Codata.Sized.Colist renaming (map to cmap)
open import Data.Vec.Bounded using (toList)
open import Data.Nat hiding (_⊔_)
open import Level
open import Size
open import Codata.Sized.Thunk
open import Relation.Unary.Sized

open import Data.Unit
open import Data.Product

module SynchronizationTree where
open Codata.Sized.Colist public

mutual

  record Tree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') (i : Size) : Set (ℓ ⊔ ℓ') where
    coinductive
    field
      children : {j : Size< i} → Thunk (Colist (SubTree X A j)) i

  data SubTree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') : Size → Set (ℓ ⊔ ℓ') where
    name : {i : Size} → X → SubTree X A i
    action : {i : Size} → A → Tree X A i → SubTree X A (↑ i)

open Tree
open SubTree

actˢ : ∀ {ℓ ℓ'} {X : Set ℓ} {A : Set ℓ'} {i : Size} → A → Tree X A i → Tree X A (↑ i)
actˢ a T = record { children = record { force = {!!} } }

-- shallow concatenation
_++ˢ_ : ∀ {ℓ ℓ'} {A : Set ℓ} {X : Set ℓ'} {i : Size} {j : Size< i} → Tree X A i  → Tree X A i → Tree X A i
l ++ˢ r = record {
          children = record {
            force = (force (children l)) ++ force (children r) } }


mutual
  stmap : ∀ {ℓ ℓ'} {A B : Set ℓ} {X : Set ℓ'} → (A → B) → ∀[ SubTree X A ] → ∀[ SubTree X B ]
  stmap f x = {!!}

  tmap : ∀ {ℓ ℓ'} {A B : Set ℓ} {X : Set ℓ'} → (A → B) → ∀[ Tree X A ] → ∀[ Thunk (Tree X B) ]
  tmap f t =  {!!}
