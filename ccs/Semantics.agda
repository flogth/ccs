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

  ST : (n : ℕ) → Set ℓ
  ST n = Tree (Fin n) Aτ ∞

  Par : {n : ℕ} → ST n → ST n → ST n
  Tree.children (Par l r) = {!!}

  Res : {n : ℕ} → (a : A) → ST n → ST n
  Tree.children (Res {n} a t) = go (Tree.children t)
    where go : {j : Size< ∞} → Colist (SubTree (Fin n) Aτ j) j → Colist (SubTree (Fin n) Aτ j) j
          go [] = []
          go (name x ∷ cs) = {!!}
          go (action (inj₁ a') t' ∷ cs) with (dec a a')
          ... | false because proof = {!!}
          ... | true because proof = {!!}
          go (action (inj₂ tau) t' ∷ cs) = action (inj₂ tau) (Res a {!t'!}) ∷ {!!}
  
  ⟦_⟧ : {n : ℕ} (P : Proc n) → ST n
  ⟦ ∅ ⟧ = record { children = [] }
  ⟦ # x ⟧ = record { children = [ name x ] }
  ⟦ α ∙ P ⟧ = actˢ α ⟦ P ⟧
  ⟦ P ＋ Q ⟧ = ⟦ P ⟧ ++ˢ ⟦ Q ⟧
  ⟦ P ∣ Q ⟧ = Par ⟦ P ⟧ ⟦ Q ⟧
  ⟦ P ∖ a ⟧ = Res a ⟦ P ⟧
  ⟦ P [ φ ] ⟧ = tmap ⟨ φ ⟩Aτ ⟦ P ⟧
  ⟦ fix P ⟧ = {!!}
