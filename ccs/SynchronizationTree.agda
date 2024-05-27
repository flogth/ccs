{-# OPTIONS --sized-types #-}
open import Codata.Sized.Colist
open import Data.Vec.Bounded using (toList)
open import Data.Nat
open import Level
open import Size
open import Codata.Sized.Thunk

open import Data.Unit

module SynchronizationTree where
open Codata.Sized.Colist public

data Tree {ℓ} (A : Set ℓ) : Size → Set ℓ where
  leaf : Tree A ∞
  node : ∀ {i} → A → Thunk (Colist (Tree A i)) i → Tree A i
