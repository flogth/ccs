{-# OPTIONS --sized-types  #-}
open import SynchronizationTree
open import Action

open import Size
open import Data.Fin
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.Core
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable
open import Data.Bool using (true ; false)

module _ {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {dec : Decidable _≈_} {Action : Act A _≈_} where
  open Act Action
  import Syntax
  open Syntax A _≈_ {Action}
  open Action.Renaming A _≈_ Action
  open Tree

  ST : (n : ℕ) → Set ℓ
  ST n = Tree (Fin n) Aτ ∞

  Par : {n : ℕ} → ST n → ST n → ST n
  children (Par {n} l r) = go (children l) (children r)
    where go : {j : Size< ∞} → Colist (SubTree (Fin n) Aτ j) j → Colist (SubTree (Fin n) Aτ j) j → Colist (SubTree (Fin n) Aτ j) j
          go [] [] = []
          go [] (x ∷ xs) = x ∷ xs
          go (x ∷ xs) [] = x ∷ xs
          go (action a x ∷ xs) (action a' y ∷ ys) = {!!}
          go (x ∷ xs) (y ∷ ys) = {!!}

  Res : {n : ℕ} → (a : A) → ST n → ST n
  children (Res {n} a t) = go (children t)
    where go : {j : Size< ∞} → Colist (SubTree (Fin n) Aτ j) j → Colist (SubTree (Fin n) Aτ j) j
          go [] = []
          go (name x ∷ cs) = {!!}
          go (action (inj₁ a') t' ∷ cs) with (dec a a')
          ... | false because proof = {!!}
          ... | true because proof = {!!}
          go (action (inj₂ tau) t' ∷ cs) = action (inj₂ tau) (Res a {!t'!}) ∷ {!!}

  ⟦_⟧ : {n : ℕ} (P : Proc n) → ST n
  ⟦ ∅ ⟧ = λ where .children → []
  ⟦ # x ⟧ = λ where .children → [ name x ]
  ⟦ α ∙ P ⟧ = actˢ α ⟦ P ⟧
  ⟦ P ＋ Q ⟧ = ⟦ P ⟧ ++ˢ ⟦ Q ⟧
  ⟦ P ∣ Q ⟧ = Par ⟦ P ⟧ ⟦ Q ⟧
  ⟦ P ∖ a ⟧ = Res a ⟦ P ⟧
  ⟦ P [ φ ] ⟧ = tmap ⟨ φ ⟩Aτ ⟦ P ⟧
  ⟦ fix P ⟧ = {!!}
