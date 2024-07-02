{-# OPTIONS --sized-types  #-}
open import SynchronizationTree
open import Action

open import Size
open import Data.Fin
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable
open import Data.Bool using (true ; false)
open import Codata.Sized.Colist
open import Codata.Sized.Thunk
open import Relation.Unary.Sized

module _ {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {dec : Decidable _≈_} {Action : Act A _≈_ dec} where
  open Act Action
  import Syntax
  open Syntax A _≈_  {dec} {Action}
  open Action.Renaming A _≈_ dec Action
  open Tree

  ST : (n : ℕ) → SizedSet ℓ
  ST n = Tree (Fin n) Aτ

  Par : {n : ℕ} → ∀[ ST n ⇒ ST n ⇒ ST n ]
  children (Par {n} l r) = go (children l) (children r)
    where go : {j : Size< ∞} → ∀[ Colist (SubTree (Fin n) Aτ j) ⇒
             Colist (SubTree (Fin n) Aτ j)  ⇒ Colist (SubTree (Fin n) Aτ j) ]
          go [] [] = []
          go [] (x ∷ xs) = x ∷ xs
          go (x ∷ xs) [] = x ∷ xs
          go (name x ∷ xs) (name y ∷ ys) = {!!}
          go (name x ∷ xs) (action a t ∷ ys) = {!!}
          go (action a t ∷ xs) (name y ∷ ys) = {!!}
          go (action (inj₁ a) ta ∷ xs) (action (inj₁ b) tb ∷ ys) with decᶜ a b
          ... | no ¬a = {!!}
          ... | yes a₁ = {!!}
          go (action (inj₁ x) ta ∷ xs) (action (inj₂ tau) tb ∷ ys) = {!!}
          go (action (inj₂ tau) ta ∷ xs) (action (inj₁ x) tb ∷ ys) = {!!}
          go (action (inj₂ tau) ta ∷ xs) (action (inj₂ tau) tb ∷ ys) = {!!}
          
          
  Res : {n : ℕ} → (a : A) → ∀[ ST n ⇒ ST n ]
  children (Res {n} a t) = go (children t)
    where 
      go : {j : Size} → ∀[ (Colist (SubTree (Fin n) Aτ j)) ⇒ (Colist (SubTree (Fin n) Aτ j)) ]
      go [] = []
      go (name x ∷ cs) = name x ∷ λ where .force → go (force cs)
      go (action (inj₁ a') t' ∷ cs) with (dec a a')
      ... | false because proof = action (inj₁ a') (Res a t') ∷ λ where .force → go (force cs)
      ... | true because proof = []
      go (action (inj₂ tau) t' ∷ cs) = action (inj₂ tau) (Res a t') ∷ λ where .force → go (force cs)
  
  ⟦_⟧ : {n : ℕ} {i : Size} (P : Proc n) → ST n i
  ⟦ ∅ ⟧ = λ where .children → []
  ⟦ # x ⟧ = λ where .children → [ name x ]
  ⟦ α ∙ P ⟧   = actˢ α ⟦ P ⟧
  ⟦ P ＋ Q ⟧   = ⟦ P ⟧ ++ˢ ⟦ Q ⟧
  ⟦ P ∣ Q ⟧   = Par ⟦ P ⟧ ⟦ Q ⟧
  ⟦ P ∖ a ⟧   = Res a ⟦ P ⟧
  ⟦ P [ φ ] ⟧ = tmap ⟨ φ ⟩Aτ ⟦ P ⟧
  ⟦ fix P ⟧   = {!!}
