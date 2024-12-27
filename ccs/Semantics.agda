{-# OPTIONS --guardedness #-}
open import Action

open import Relation.Binary.Definitions using (Decidable ; DecidableEquality)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (_++_)
open import Data.Nat

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
  ϱ (name m , []) = (λ x → lookupM m x (app (name m) []) λ P → app fix (var (inj₁ P) ∷ []))
                  , (node [])
    where
      lookupM : ∀ {A C : Set ℓ} → ℕ → List (Maybe A) → C → (A → C) → C
      lookupM zero [] c f = c
      lookupM zero (just x ∷ xs) c f = f x
      lookupM zero (nothing ∷ xs) c f = c
      lookupM (suc n) [] c f = c
      lookupM (suc n) (x ∷ xs) c f = lookupM n xs c f

  ϱ (prefix α , (P , σ , _) ∷ []) = (λ x → app (prefix α) (var (inj₂ (σ x)) ∷ []))
                                  , node ((α , λ x → var (inj₂ (σ x))) ∷ [])
  ϱ {X} {Y} (plus , (P , σP , bP) ∷ (Q , σQ , bQ) ∷ []) = (λ x → app plus (var (inj₂ (σP x)) ∷ var (inj₂ (σQ x)) ∷ []))
                                                , node (b (children bP) ++ b (children bQ))
    where
      b : List (Aτ × Sub X Y) → List (Aτ × Sub X (Σ* (X ⊎ Y)))
      b = Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ x)))

  ϱ {X} {Y} (par , (P , σP , bP) ∷ (Q , σQ , bQ) ∷ []) = (λ x → app par (var (inj₂ (σP x)) ∷ var (inj₂ (σQ x)) ∷ []))
                                               , node (Data.List.map (λ (α , σ) → α , λ x → app par (var (inj₂ (σ x)) ∷ var (inj₂ (σQ x)) ∷ [])) (children bP)
                                                      ++ Data.List.map (λ (α , σ) → α , λ x → app par (var (inj₂ (σP x)) ∷ var (inj₂ (σ x)) ∷ [])) (children bQ)
                                                      ++ zipPWith ≈fst-dec (λ (_ , σ) (_ , σ') → τ , λ x → app par (var (inj₂ (σ x)) ∷ var (inj₂ (σ' x)) ∷ [])) (children bP) (children bQ))
    where
      _>>=_ : ∀ {A B : Set ℓ} → List A → (A → List B) → List B
      m >>= g = concatMap g m

      case : ∀ {A B C : Set ℓ} → {P : A → B → Set ℓ} → Decidable P → (f : A → B → C) → C → A → B → C
      case p f g x y with p x y
      ... | yes _ = f x y
      ... | no _ = g

      _≈fst_ : (Aτ × Sub X Y) → (Aτ × Sub X Y) → Set ℓ
      a ≈fst b = proj₁ a ≈ proj₁ b

      ≈fst-dec : Decidable _≈fst_
      ≈fst-dec (x , _) (y , _) = ≈-dec x y

      zipPWith : ∀ {A B C : Set ℓ} → {P : A → B → Set ℓ} → Decidable P → (f : A → B → C) → List A → List B → List C
      zipPWith p f xs ys = xs >>= λ x → ys >>= λ y → case p (λ a b → f a b ∷ []) [] x y

  ϱ (restr β , (P , σP , bP) ∷ []) = (λ x → app (restr β) ((var (inj₂ (σP x))) ∷ []))
                                   , node (Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ x))) (Data.List.filter (λ (α , _) → ≉-dec α (act β)) (children bP)))

  ϱ (ren φ , (P , σP , bP) ∷ []) = (λ x → app (ren φ) ((var (inj₂ (σP x))) ∷ []))
                                 , node (Data.List.map (λ (α , σ) → (⟨ φ ⟩Aτ α) , λ x → var (inj₂ (σ x))) (children bP))
  ϱ (fix , (P , σP , bP) ∷ []) = (λ x → app fix (var (inj₂ (σP (nothing ∷ x))) ∷ []))
                               , node (Data.List.map (λ (α , σ) → α , λ x → var (inj₂ (σ (nothing ∷ x)))) (children bP))
