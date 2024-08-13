{-# OPTIONS --allow-unsolved-metas #-}
open import Action
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open ≡-Reasoning

module Syntax {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
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

  subst-zero : {n : ℕ} → Proc n → Fin (suc n) → Proc n
  subst-zero Q Fin.zero = Q
  subst-zero Q (Fin.suc x) = # x

  _[0↦_] : ∀ {n} → Proc (suc n) → Proc n → Proc n
  _[0↦_] {n} P Q = subst (subst-zero Q) P

  _[1↦_] : ∀ {n} → Proc (suc (suc n)) → Proc n → Proc (suc n)
  _[1↦_] {n} P Q = subst (exts (subst-zero Q)) P

  Subst : ℕ → ℕ → Set ℓ
  Subst n m = Fin n → Proc m

  ⟪_⟫ : ∀ {n m} → Subst n m  → Proc n → Proc m
  ⟪ σ ⟫ M = subst σ M

  ids : ∀ {n} → Subst n n
  ids n = # n

  ↑ : ∀ {n} → Subst n (suc n)
  ↑ x = # (Fin.suc x)

  infixr 6 _⊙_
  _⊙_ : ∀ {n m} → Proc m → Subst n m → Subst (suc n) m
  (M ⊙ σ) Fin.zero = M
  (M ⊙ σ) (Fin.suc x) = σ x

  infixr 5 _⨾_
  _⨾_ : ∀ {n m p} → Subst n m → Subst m p → Subst n p
  (σ ⨾ τ) x = ⟪ τ ⟫ (σ x)

  sub-zero : ∀ {n m} {P : Proc m} {σ : Subst n m} →
     ⟪ P ⊙ σ ⟫ (# Fin.zero)  ≡ P
  sub-zero = refl

  sub-suc : ∀ {n m} {P : Proc m} {σ : Subst n m} →
    (↑ ⨾ P ⊙ σ) ≡ σ
  sub-suc = refl

  subst-Z-cons-ids : ∀ {n} {P : Proc n} →
    subst-zero P ≡ (P ⊙ ids)
  subst-Z-cons-ids {zero} {P} = {!!}
  subst-Z-cons-ids {suc n} {P} = {!!}

  sub-dist : ∀ {n m p} {σ : Subst n m} {σ' : Subst m p} {P : Proc m} →
    (P ⊙ σ) ⨾ σ' ≡ ⟪ σ' ⟫ P ⊙ (σ ⨾ σ')
  sub-dist = {!!}

  exts-seq : ∀ {n m p} {σ : Subst n m} {σ' : Subst m p} →
    (exts σ ⨾ exts σ') ≡ exts (σ ⨾ σ')
  exts-seq = {!!}

  exts-suc-shift : ∀ {n m} {σ : Subst n m} →
    exts σ ≡ (# Fin.zero ⊙ (σ ⨾ ↑))
  exts-suc-shift = {!!}

  cong-sub : ∀ {n m} {σ σ' : Subst n m} {P P' : Proc n} →
    (σ ≡ σ') → P ≡ P' → ⟪ σ ⟫ P ≡ ⟪ σ' ⟫ P'
  cong-sub {P = ∅} ss refl = refl
  cong-sub {P = # x} refl refl = refl
  cong-sub {P = α ∙ P} refl refl = refl
  cong-sub {P = P ＋ Q} refl refl = refl
  cong-sub {P = P ∣ Q} refl refl = refl
  cong-sub {P = P ∖ a} refl refl = refl
  cong-sub {P = P [ φ ]} refl refl = refl
  cong-sub {P = fix P} refl refl = refl

  cong-cons : ∀ {n m} {P Q : Proc m} {σ σ' : Subst n m} →
    P ≡ Q → σ ≡ σ' →
    (P ⊙ σ) ≡ (Q ⊙ σ')
  cong-cons = {!!}


  cong-seq : ∀ {n m p} {σ σ' : Subst n m} {τ τ' : Subst m p}
    → σ ≡ σ' → τ ≡ τ'
    → (σ ⨾ τ) ≡ (σ' ⨾ τ')
  cong-seq = {!!}

  sub-idR : ∀ {n m} {σ : Subst n m} → (σ ⨾ ids) ≡ σ
  sub-idR = {!!}

  sub-idL : ∀ {n m} {σ : Subst n m} → (ids ⨾ σ) ≡ σ
  sub-idL = {!!}

  sub-sub : ∀ {n m p} {P : Proc n} {σ : Subst n m} {σ' : Subst m p} →
    ⟪ σ' ⟫ (⟪ σ ⟫ P) ≡ ⟪ σ ⨾ σ' ⟫ P
  sub-sub {P = ∅} = refl
  sub-sub {P = # x} = refl
  sub-sub {P = α ∙ P} = cong (α ∙_) (sub-sub {P = P})
  sub-sub {P = P ＋ Q} {σ} {σ'} = trans (cong (_＋ subst σ' (subst σ Q)) (sub-sub {P = P})) (cong (⟪ σ ⨾ σ' ⟫ P ＋_) (sub-sub {P = Q}))
  sub-sub {P = P ∣ Q} {σ} {σ'} = trans (cong (_∣ subst σ' (subst σ Q)) (sub-sub {P = P})) (cong (⟪ σ ⨾ σ' ⟫ P ∣_) (sub-sub {P = Q}))
  sub-sub {P = P ∖ a} = cong (_∖ a) (sub-sub {P = P})
  sub-sub {P = P [ φ ]} = cong (_[ φ ]) (sub-sub {P = P})
  sub-sub {P = fix P} {σ} {σ'} = begin
    ⟪ σ' ⟫ (⟪ σ ⟫ (fix P)) ≡⟨⟩
    fix (⟪ exts σ' ⟫ (⟪ exts σ ⟫ P)) ≡⟨ cong fix (sub-sub {P = P} {σ = exts σ} {σ' = exts σ'}) ⟩
    fix (⟪ exts σ ⨾ exts σ' ⟫ P) ≡⟨ cong fix (cong-sub {P = P} exts-seq refl) ⟩
    fix (⟪ exts (σ ⨾ σ') ⟫ P) ∎

  sub-assoc : ∀ {n m p q} {σ : Subst n m} {τ : Subst m p} {θ : Subst p q} →
    (σ ⨾ τ) ⨾ θ ≡ σ ⨾ τ ⨾ θ
  sub-assoc = {!!}

  subst-commute : ∀ {n m} {P : Proc (suc (suc n))} {Q : Proc (suc n)} {σ : Subst (suc n) m } →
     ⟪ exts σ ⟫ P [0↦ ⟪ σ ⟫ Q ] ≡ ⟪ σ ⟫ (P [0↦ Q ])
  subst-commute {n} {m} {P} {Q} {σ} = begin
      subst (subst-zero (subst σ Q)) (subst (exts σ) P)
    ≡⟨ cong-sub {P = ⟪ exts σ ⟫ P} subst-Z-cons-ids refl ⟩
      subst (subst σ Q ⊙ #_) (subst (exts σ) P)
    ≡⟨ sub-sub {P = P} ⟩
      subst (exts σ ⨾ (subst σ Q ⊙ #_)) P
    ≡⟨ cong-sub {P = P} (cong-seq exts-suc-shift refl) refl ⟩
      subst (((# Fin.zero) ⊙ (σ ⨾ (λ z → # Fin.suc z))) ⨾ (subst σ Q ⊙ #_)) P
    ≡⟨ cong-sub {P = P} sub-dist refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ ((σ ⨾ ↑) ⨾ (⟪ σ ⟫ Q ⊙ ids)) ⟫ P
    ≡⟨ cong-sub {P = P} (cong-cons refl (sub-assoc {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (σ ⨾ ↑ ⨾ (⟪ σ ⟫ Q) ⊙ ids) ⟫ P
    ≡⟨ cong-sub {P = P} refl refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (σ ⨾ ids) ⟫ P
    ≡⟨ cong-sub {P = P}  (cong-cons refl (sub-idR {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ σ ⟫ P
    ≡⟨ cong-sub {P = P} (cong-cons refl (sub-idL {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (ids ⨾ σ) ⟫ P
    ≡⟨ cong-sub {P = P} (sym sub-dist) refl ⟩
      ⟪ (Q ⊙ ids) ⨾ σ ⟫ P
    ≡⟨ sym (sub-sub {P = P}) ⟩
      ⟪ σ ⟫ (⟪ Q ⊙ ids ⟫ P)
    ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub {P = P} subst-Z-cons-ids refl)) ⟩
    ⟪ σ ⟫ (P [0↦ Q ]) ∎
