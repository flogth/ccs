{-# OPTIONS --guardedness #-}
open import Action

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (_++_)

module Semantics {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  import Syntax
  open Syntax A {dec} {Action}
  open Action.Renaming A dec Action
  open import FreeAlgebra A {dec} {Action}

  record FST (L : Set ℓ) : Set ℓ where
    coinductive
    constructor node
    field
      children : List L

  open FST

  Sub : ∀ (X Y : Set ℓ) → Set ℓ
  Sub X Y = List (Maybe X) → Y

  B : ∀ (X Y : Set ℓ) → Set ℓ
  B X Y = Sub X Y × FST (Aτ × Sub X Y)

  ϱ : ∀ {X Y : Set ℓ} → Sig (X × B X Y) → B X (Σ* (X ⊎ Y))
  ϱ (dead , []) = (λ _ → app dead [])
                , (node [])
  ϱ (name m , []) = {!!}
                  , (node [])
  ϱ (prefix α , (P , σ , _) ∷ []) = (λ x → app (prefix α) (var (inj₂ (σ x)) ∷ []))
                                  , node ((α , λ x → var (inj₂ (σ x))) ∷ [])
  ϱ {X} {Y} (plus , (P , σP , bP) ∷ (Q , σQ , bQ) ∷ []) = (λ x → app plus (var (inj₂ (σP x)) ∷ var (inj₂ (σQ x)) ∷ []))
                                                , node (b (children bP) ++ b (children bQ))
    where
      b : List (Aτ × Sub X Y) → List (Aτ × Sub X (Σ* (X ⊎ Y)))
      b = Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ x)))

  ϱ (par , (P , σP , bP) ∷ (Q , σQ , bQ) ∷ []) = {!!}
                                               , {!!}
  ϱ (restr β , (P , σP , bP) ∷ []) = (λ x → app (restr β) ((var (inj₂ (σP x))) ∷ []))
                                   , node (Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ x))) (Data.List.filter (λ (α , _) → ≉-dec α (act β)) (children bP)))

  ϱ (ren φ , (P , σP , bP) ∷ []) = (λ x → app (ren φ) ((var (inj₂ (σP x))) ∷ []))
                                 , node (Data.List.map (λ (α , σ) → (⟨ φ ⟩Aτ α) , λ x → var (inj₂ (σ x))) (children bP))
  ϱ (fix , (P , σP , bP) ∷ []) = (λ x → app fix (var (inj₂ (σP (nothing ∷ x))) ∷ []))
                               , node (Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ (nothing ∷ x)))) (children bP))
