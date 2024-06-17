{-# OPTIONS --sized-types  #-}
open import Codata.Sized.Colist renaming (map to cmap)
open import Codata.Sized.Thunk using (force)
open import Level using (_⊔_)
open import Size

module SynchronizationTree where
open Codata.Sized.Colist public

mutual
  record Tree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') (i : Size) : Set (ℓ ⊔ ℓ') where
    coinductive
    field
      children : {j : Size< i} → Colist (SubTree X A j) j

  data SubTree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') : Size → Set (ℓ ⊔ ℓ') where
    name : {i : Size} → X → SubTree X A i
    action : {i : Size} → A → Tree X A i → SubTree X A i

open Tree

actˢ : ∀ {ℓ ℓ'} {X : Set ℓ} {A : Set ℓ'} {i : Size} → A → Tree X A (↑ i) → Tree X A (↑ i)
actˢ a T = λ where .children → [ action a T ]

interleave : ∀ {ℓ} {i : Size} {A : Set ℓ} → Colist A i → Colist A i → Colist A i
interleave [] ys = ys
interleave (x ∷ xs) ys = x ∷ λ where .force → interleave ys (force xs)

-- shallow concatenation
_++ˢ_ : ∀ {ℓ ℓ'} {A : Set ℓ} {X : Set ℓ'} {i : Size}  → Tree X A (↑ i)  → Tree X A (↑ i) → Tree X A (↑ i)
l ++ˢ r = λ where .children → interleave (children l) (children r)

map′ : ∀ {i} {ℓ ℓ'} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ'} →
       (A → B) → SubTree X A i → SubTree X B i
map′ σ (name x) = name x
map′ σ (action a p) = action (σ a) λ where .children → cmap (map′ σ) (children p)

tmap : ∀ {i} {ℓ ℓ'} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ'} →
       (A → B) → Tree X A i → Tree X B i
children (tmap σ t) = cmap (map′ σ) (children t)
