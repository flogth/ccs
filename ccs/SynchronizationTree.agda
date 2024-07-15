{-# OPTIONS --sized-types  #-}
open import Codata.Sized.Colist renaming (map to cmap)
open import Codata.Sized.Thunk using (force)
open import Level using (_⊔_)
open import Size
open import Relation.Unary.Sized

module SynchronizationTree where

mutual
  record Tree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') (i : Size) : Set (ℓ ⊔ ℓ') where
    coinductive
    field
      children : {j : Size< i} → Colist (SubTree X A j) j

  data SubTree {ℓ ℓ'} (X : Set ℓ) (A : Set ℓ') : Size → Set (ℓ ⊔ ℓ') where
    bot : {i : Size} → SubTree X A i
    name : {i : Size} → X → SubTree X A i
    action : {i : Size} → A → Tree X A i → SubTree X A i

open Tree

interleave : ∀ {ℓ} {A : Set ℓ} → ∀[ Colist A ⇒ Colist A ⇒ Colist A ]
interleave [] ys = ys
interleave (x ∷ xs) ys = x ∷ λ where .force → interleave ys (force xs)

module _ {ℓa ℓx} {A : Set ℓa} {X : Set ℓx} where

  actˢ : A → ∀[ Tree X A ⇒ Tree X A ]
  actˢ a T = λ where .children → [ action a T ]

  _++ˢ_ : ∀[ Tree X A ⇒ Tree X A ⇒ Tree X A ]
  l ++ˢ r = λ where .children → interleave (children l) (children r)

  tmap′ : ∀ {ℓb} {B : Set ℓb} → (A → B) → ∀[ SubTree X A ⇒ SubTree X B ]
  tmap′ σ (bot) = bot
  tmap′ σ (name x) = name x
  tmap′ σ (action a p) = action (σ a) λ where .children → cmap (tmap′ σ) (children p)

  tmap : ∀ {ℓb} {B : Set ℓb} → (A → B) → ∀[ Tree X A ⇒ Tree X B ]
  children (tmap σ t) = cmap (tmap′ σ) (children t)
