open import Action
open import Relation.Binary.Core using (Rel)

module Syntax {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  open import Data.Nat public
  open import Data.Fin using (Fin ; raise)

  infix 20 _∣_
  infix 20 _＋_
  infix 25 _∙_

  data Proc : ℕ → Set ℓ where
    ∅ : ∀ {n} → Proc n

    #_ : ∀ {n} →
      (x : Fin n) →
      Proc n

    _∙_ : ∀ {n} →
      (α : Aτ) →
      (P : Proc n) →
      Proc n
    _＋_ : ∀ {n} →
      (P Q : Proc n) →
      Proc n
    _∣_ : ∀ {n} →
      (P Q : Proc n) →
      Proc n
    _∖_ : ∀ {n} →
      (P : Proc n) →
      (a : A) →
      Proc n
    _[_] : ∀ {n} →
      (P : Proc n) →
      (φ : Renaming) →
      Proc n
    fix : ∀ {n} →
      (P : Proc (suc n)) →
      Proc n

  ext : ∀ {n m} → (ρ : Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  ext ρ Fin.zero = Fin.zero
  ext ρ (Fin.suc x) = Fin.suc (ρ x)

  rename : ∀ {n m} → (ρ : Fin n → Fin m) → Proc n → Proc m
  rename ρ ∅ = ∅
  rename ρ (# x) = # (ρ x)
  rename ρ (α ∙ P) = α ∙ (rename ρ P)
  rename ρ (P ＋ Q) = (rename ρ P) ＋ (rename ρ Q)
  rename ρ (P ∣ Q) = (rename ρ P) ∣ (rename ρ Q)
  rename ρ (P ∖ a) = (rename ρ P) ∖ a
  rename ρ (P [ φ ]) = (rename ρ P) [ φ ]
  rename ρ (fix P) = fix (rename (ext ρ) P)

  exts : ∀ {n m} → (σ : Fin n → Proc m) → Fin (suc n) → Proc (suc m)
  exts σ Fin.zero = # Fin.zero
  exts σ (Fin.suc x) = rename Fin.suc (σ x)

  subst : ∀ {n m} → (σ : Fin n → Proc m) → Proc n → Proc m
  subst σ ∅ = ∅
  subst σ (# x) = σ x
  subst σ (α ∙ P) = α ∙ subst σ P
  subst σ (P ＋ Q) = subst σ P ＋ subst σ Q
  subst σ (P ∣ Q) = subst σ P ∣ subst σ Q
  subst σ (P ∖ a) = subst σ P ∖ a
  subst σ (P [ φ ]) = subst σ P [ φ ]
  subst σ (fix P) = fix (subst (exts σ) P)

  _[0↦_] : ∀ {n} → Proc (suc n) → Proc n → Proc n
  _[0↦_] {n} P Q = subst σ P
    where
      σ : Fin (suc n) → Proc n
      σ Fin.zero = Q
      σ (Fin.suc x) = # x
