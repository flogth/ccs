{-# OPTIONS --allow-unsolved-metas #-} -- TODO: remove
open import Relation.Binary.Core using (Rel)
open import Action
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Level renaming (suc to lsuc)
open import Data.Fin hiding (_>_ ; #_)
open import Relation.Binary.Definitions using (Decidable)

module Guarded {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {dec : Decidable _≈_} {Action : Act A _≈_ dec} where
  open Act Action
  open Action.Renaming A _≈_ dec Action
  import Syntax
  open Syntax A _≈_ {dec} {Action}

  data guarded {n} : (P : Proc n) → (m : ℕ) → Set ℓ where
    guarded-∅ : ∀ {m} → guarded ∅ m

    guarded-＋ : ∀ {P Q} {m} →
      guarded P m →
      guarded Q m →
      guarded (P ＋ Q) m

    guarded-∣ : ∀ {P Q} {m} →
      guarded P m →
      guarded Q m →
      guarded (P ∣ Q) m

    guarded-∖ : ∀ {P} {α} {m} →
      guarded P m →
      guarded (P ∖ α) m

    guarded-ren : ∀ {P} {φ} {m} →
      guarded P m →
      guarded (P [ φ ]) m

    guarded-∙ : ∀ {α} {P} {m} →
      guarded P 0 →
      guarded (α ∙ P) m

    guarded-fix : ∀ {P} {m} →
      guarded P (suc m) →
      guarded (fix P) m

  guarded-subst : ∀ {n} {P : Proc (suc n)} (m : ℕ) {σ : Fin (suc n) → Proc n} →
                  guarded P m → guarded (subst σ P) m
  guarded-subst m guarded-∅ = guarded-∅
  guarded-subst m (guarded-＋ p q) = guarded-＋ (guarded-subst m p) (guarded-subst m q)
  guarded-subst m (guarded-∣ p q) = guarded-∣ (guarded-subst m p) (guarded-subst m q)
  guarded-subst m (guarded-∖ x) = guarded-∖ (guarded-subst m x)
  guarded-subst m (guarded-ren x) = guarded-ren (guarded-subst m x)
  guarded-subst m (guarded-∙ x) = guarded-∙ (guarded-subst 0 x)
  guarded-subst m (guarded-fix x) = guarded-fix (guarded-subst (suc m) x)
