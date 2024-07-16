{-# OPTIONS --sized-types  #-}
open import SynchronizationTree
open import Action

open import Size
open import Data.Fin
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable
open import Codata.Sized.Colist renaming (map to cmap)
open import Codata.Sized.Thunk
open import Relation.Unary.Sized

module Semantics {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  import Syntax
  open Syntax A {dec} {Action}
  open Action.Renaming A dec Action
  open Tree

  ST : (n : ℕ) → SizedSet ℓ
  ST n = Tree (Fin n) Aτ

  Par : {n : ℕ} → ∀[ ST n ⇒ ST n ⇒ ST n ]
  children (Par {n} l r) = go (children l) (children r)
    where
      go : {j : Size< ∞} → ∀[ Colist (SubTree (Fin n) Aτ j) ⇒
             Colist (SubTree (Fin n) Aτ j)  ⇒ Colist (SubTree (Fin n) Aτ j) ]
      go [] [] = []
      go [] (y ∷ ys) = y ∷ ys
      go (x ∷ xs) [] = x ∷ xs
      go (bot ∷ xs) (bot ∷ ys) = bot ∷ λ where .force → go (force xs) (force ys)
      go (bot ∷ xs) (name x ∷ ys) = bot ∷ λ where .force → go (force xs) (force ys)
      go (bot ∷ xs) (action x x₁ ∷ ys) = bot ∷ λ where .force → go (force xs) (force ys)
      go (name x ∷ xs) (bot ∷ ys) = bot ∷ λ where .force → go (force xs) (force ys)
      go (name x ∷ xs) (name y ∷ ys)
        = interleave (name x ∷ λ where .force → go (force xs) (name y ∷ ys))
                     (name y ∷ λ where .force → go (name x ∷ xs) (force ys))
      go (name x ∷ xs) (action a t ∷ ys)
        = interleave (name x ∷ λ where .force → go (force xs) {!!})
                     ({!!} ∷ λ where .force → go (name x ∷ xs) (force ys))
      go (action a t ∷ xs) (bot ∷ ys) = bot ∷ λ where .force → go (force xs) (force ys)
      go (action a t ∷ xs) (name y ∷ ys)
        = interleave ({!!} ∷ λ where .force → go (force xs) (name y ∷ ys))
                     (name y ∷ λ where .force → go {!!} (force ys))
      go (action (inj₁ a) t ∷ xs) (action (inj₁ b) t' ∷ ys) with ≈-dec a b
      ... | no a≉b = action τ (Par t t') ∷ λ where .force → go (force xs) (force ys)
      ... | yes a≈b = interleave (action (act a) (Par t (actˢ (act b) t')) ∷ λ where .force → go (force xs) (force ys))
                                 (action (act b) (Par (actˢ (act a) t) t) ∷ λ where .force → go (force xs) (force ys))
      go (action (inj₁ a) t ∷ xs) (action (inj₂ tau) t' ∷ ys)
         = interleave (action (act a) (Par t (actˢ τ t')) ∷ λ where .force → go (force xs) (force ys))
                      (action τ (Par (actˢ (act a) t) t) ∷ λ where .force → go (force xs) (force ys))
      go (action (inj₂ tau) t ∷ xs) (action (inj₁ b) t' ∷ ys)
         = interleave (action τ (Par t (actˢ (act b) t')) ∷ λ where .force → go (force xs) (force ys))
                       (action (act b) (Par (actˢ τ t) t) ∷ λ where .force → go (force xs) (force ys))
      go (action (inj₂ tau) t ∷ xs) (action (inj₂ tau) t' ∷ ys)
         = interleave (action τ (Par t (actˢ τ t')) ∷ λ where .force → go (force xs) (force ys))
                      (action τ (Par (actˢ τ t) t) ∷ λ where .force → go (force xs) (force ys))

  Res : {n : ℕ} → (a : A) → ∀[ ST n ⇒ ST n ]
  children (Res {n} a t) = cmap go (children t)
    where
      go : ∀[ SubTree (Fin n) Aτ ⇒ SubTree (Fin n) Aτ ]
      go bot = bot
      go (name x) = name x
      go (action (inj₁ a') t) with dec a a'
      ... | no ¬p = action (inj₁ a') (Res a t)
      ... | yes p = bot
      go (action (inj₂ tau) t) = action τ (Res a t)

  ⟦_⟧ : {n : ℕ} {i : Size} (P : Proc n) → ST n i
  ⟦ ∅ ⟧ = λ where .children → []
  ⟦ # x ⟧ = λ where .children → [ name x ]
  ⟦ α ∙ P ⟧   = actˢ α ⟦ P ⟧
  ⟦ P ＋ Q ⟧   = ⟦ P ⟧ ++ˢ ⟦ Q ⟧
  ⟦ P ∣ Q ⟧   = Par ⟦ P ⟧ ⟦ Q ⟧
  ⟦ P ∖ a ⟧   = Res a ⟦ P ⟧
  ⟦ P [ φ ] ⟧ = tmap ⟨ φ ⟩Aτ ⟦ P ⟧
  ⟦ fix P ⟧   = {!!}
