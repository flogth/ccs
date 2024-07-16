{-# OPTIONS --allow-unsolved-metas #-} -- TODO: remove
open import Relation.Binary.Core using (Rel)
open import Action
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Level renaming (suc to lsuc)
open import Data.Fin hiding (_>_ ; #_)
open import Relation.Binary.Definitions using (DecidableEquality)

module Guarded {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  import Syntax
  open Syntax A {dec} {Action}

  data guarded {n} : (P : Proc n)  → Set ℓ where
    guarded-∅ : guarded ∅ 

    guarded-＋ : ∀ {P Q} →
      guarded P →
      guarded Q →
      guarded (P ＋ Q)

    guarded-∣ : ∀ {P Q} →
      guarded P →
      guarded Q →
      guarded (P ∣ Q)

    guarded-∖ : ∀ {P} {α} →
      guarded P →
      guarded (P ∖ α)

    guarded-ren : ∀ {P} {φ} →
      guarded P →
      guarded (P [ φ ])

    guarded-∙ : ∀ {α} {P} →
      guarded (α ∙ P)

    guarded-fix : ∀ {P} →
      guarded P →
      guarded (fix P)

  -- guarded-subst : ∀ {n} {P : Proc (suc n)} (m : ℕ) {σ : Fin (suc n) → Proc n} →
  --                 guarded P m → guarded (subst σ P) m
  -- guarded-subst m guarded-∅ = guarded-∅
  -- guarded-subst m (guarded-＋ p q) = guarded-＋ (guarded-subst m p) (guarded-subst m q)
  -- guarded-subst m (guarded-∣ p q) = guarded-∣ (guarded-subst m p) (guarded-subst m q)
  -- guarded-subst m (guarded-∖ x) = guarded-∖ (guarded-subst m x)
  -- guarded-subst m (guarded-ren x) = guarded-ren (guarded-subst m x)
  -- guarded-subst m (guarded-∙ x) = guarded-∙ (guarded-subst 0 x)
  -- guarded-subst m (guarded-fix x) = guarded-fix (guarded-subst (suc m) x)
