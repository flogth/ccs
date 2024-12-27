open import Action
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open ≡-Reasoning
open import Function

module Syntax {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Data.Nat
  open import Data.Fin using (Fin ; raise)

  infix 20 _∣_
  infix 21 _＋_
  infix 25 _∙_
  infix 25 #_

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
    subst-zero P ≗ (P ⊙ ids)
  subst-Z-cons-ids Fin.zero = refl
  subst-Z-cons-ids (Fin.suc x) = refl

  sub-dist : ∀ {n m p} {σ : Subst n m} {σ' : Subst m p} {P : Proc m} →
    (P ⊙ σ) ⨾ σ' ≗ ⟪ σ' ⟫ P ⊙ (σ ⨾ σ')
  sub-dist Fin.zero = refl
  sub-dist (Fin.suc x) = refl

  cong-ext : ∀ {n m} {σ σ' : Fin n → Fin m} →
    σ ≗ σ' → ext σ ≗ ext σ'
  cong-ext eq Fin.zero = refl
  cong-ext eq (Fin.suc x) = cong Fin.suc (eq x)

  cong-rename : ∀ {n m} {ρ ρ' : Fin n → Fin m} →
    ρ ≗ ρ' →
    rename ρ ≗ rename ρ'
  cong-rename eq ∅ = refl
  cong-rename eq (# x) = cong #_ (eq x)
  cong-rename eq (α ∙ P) = cong (α ∙_) (cong-rename eq P)
  cong-rename eq (P ＋ Q) = cong₂ _＋_ (cong-rename eq P) (cong-rename eq Q)
  cong-rename eq (P ∣ Q) = cong₂ _∣_ (cong-rename eq P) (cong-rename eq Q)
  cong-rename eq (P ∖ a) = cong (_∖ a) (cong-rename eq P)
  cong-rename eq (P [ φ ]) = cong (_[ φ ]) (cong-rename eq P)
  cong-rename eq (fix P) = cong fix (cong-rename (cong-ext eq) P)

  compose-rename : ∀ {n m p} {ρ : Fin m → Fin p} {ρ' : Fin n → Fin m} →
    rename ρ ∘ rename ρ' ≗ rename (ρ ∘ ρ')
  compose-rename ∅ = refl
  compose-rename (# x) = refl
  compose-rename (α ∙ P) = cong (α ∙_) (compose-rename P)
  compose-rename (P ＋ Q) = cong₂ _＋_ (compose-rename P) (compose-rename Q)
  compose-rename (P ∣ Q) = cong₂ _∣_ (compose-rename P) (compose-rename Q)
  compose-rename (P ∖ a) = cong (_∖ a) (compose-rename P)
  compose-rename (P [ φ ]) = cong (_[ φ ]) (compose-rename P)
  compose-rename (fix P)
    = cong fix (trans (compose-rename P)
      (cong-rename (λ{ Fin.zero → refl ; (Fin.suc x) → refl}) P))

  commute-subst-rename : ∀ {n m} {σ : Subst n m}
    {ρ₁ : Fin n → Fin (suc n)} {ρ₂ : Fin m → Fin (suc m)} →
    (exts σ) ∘ ρ₁ ≗ rename ρ₂ ∘ σ →
    subst (exts σ) ∘ (rename ρ₁) ≗ rename ρ₂ ∘ subst σ
  commute-subst-rename eq ∅ = refl
  commute-subst-rename eq (# x) = eq x
  commute-subst-rename eq (α ∙ P) = cong (α ∙_) (commute-subst-rename eq P)
  commute-subst-rename eq (P ＋ Q) = cong₂ _＋_ (commute-subst-rename eq P) (commute-subst-rename eq Q)
  commute-subst-rename eq (P ∣ Q) = cong₂ _∣_ (commute-subst-rename eq P) (commute-subst-rename eq Q)
  commute-subst-rename eq (P ∖ a) = cong (_∖ a) (commute-subst-rename eq P)
  commute-subst-rename eq (P [ φ ]) = cong (_[ φ ]) (commute-subst-rename eq P)
  commute-subst-rename {σ = σ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} eq (fix P) = cong fix (commute-subst-rename lemma P)
    where lemma : exts (exts σ) ∘ ext ρ₁ ≗ rename (ext ρ₂) ∘ exts σ
          lemma Fin.zero = refl
          lemma (Fin.suc x) = begin
              (exts (exts σ) ∘ ext ρ₁) (Fin.suc x)
            ≡⟨ cong (rename Fin.suc) (eq x) ⟩
            rename Fin.suc (rename ρ₂ (σ x))
            ≡⟨ compose-rename (σ x) ⟩
            rename (λ z → Fin.suc (ρ₂ z)) (σ x)
            ≡⟨ sym (compose-rename (σ x)) ⟩
              (rename (ext ρ₂) ∘ exts σ) (Fin.suc x) ∎

  exts-seq : ∀ {n m p} {σ : Subst n m} {σ' : Subst m p} →
    (exts σ ⨾ exts σ') ≗ exts (σ ⨾ σ')
  exts-seq Fin.zero = refl
  exts-seq {σ = σ} (Fin.suc x) = commute-subst-rename (λ _ → refl) (σ x)

  subst-ext : ∀ {n m} → {σ σ' : Fin n → Proc m} →
    σ ≗ σ' → subst σ ≗ subst σ'
  subst-ext eqσ ∅ = refl
  subst-ext eqσ (# x) = eqσ x
  subst-ext eqσ (α ∙ P) = cong (α ∙_) (subst-ext eqσ P)
  subst-ext eqσ (P ＋ Q) = cong₂ _＋_ (subst-ext eqσ P) (subst-ext eqσ Q)
  subst-ext eqσ (P ∣ Q) = cong₂ _∣_ (subst-ext eqσ P) (subst-ext eqσ Q)
  subst-ext eqσ (P ∖ a) = cong (_∖ a) (subst-ext eqσ P)
  subst-ext eqσ (P [ φ ]) = cong (_[ φ ]) (subst-ext eqσ P)
  subst-ext eqσ (fix P)
    = cong fix (subst-ext
                 (λ { Fin.zero → refl ;
                     (Fin.suc x) → cong (rename Fin.suc) (eqσ x) })
                 P)

  cong-sub : ∀ {n m} {σ σ' : Subst n m} {P P' : Proc n} →
    (σ ≗ σ') → P ≡ P' → ⟪ σ ⟫ P ≡ ⟪ σ' ⟫ P'
  cong-sub {P = P} eq refl = subst-ext eq P


  rename-subst-ren : ∀ {n m} {ρ : Fin n → Fin m}
                   → rename ρ ≗ ⟪ ids ∘ ρ ⟫
  rename-subst-ren ∅ = refl
  rename-subst-ren (# x) = refl
  rename-subst-ren (α ∙ P) = cong (α ∙_) (rename-subst-ren P)
  rename-subst-ren (P ＋ Q) = cong₂ _＋_ (rename-subst-ren P) (rename-subst-ren Q)
  rename-subst-ren (P ∣ Q) = cong₂ _∣_ (rename-subst-ren P) (rename-subst-ren Q)
  rename-subst-ren (P ∖ a) = cong (_∖ a) (rename-subst-ren P)
  rename-subst-ren (P [ φ ]) = cong (_[ φ ]) (rename-subst-ren P)
  rename-subst-ren (fix P)
    = trans (cong fix (rename-subst-ren P))
            (cong fix (cong-sub {P = P}
                                (λ{ Fin.zero → refl ; (Fin.suc x) → refl})
                                refl))

  exts-suc-shift : ∀ {n m} {σ : Subst n m} →
    exts σ ≗ (# Fin.zero ⊙ (σ ⨾ ↑))
  exts-suc-shift Fin.zero = refl
  exts-suc-shift {σ = σ} (Fin.suc x) = rename-subst-ren (σ x)

  cong-cons : ∀ {n m} {P Q : Proc m} {σ σ' : Subst n m} →
    P ≡ Q → σ ≗ σ' →
    (P ⊙ σ) ≗ (Q ⊙ σ')
  cong-cons refl eq Fin.zero = refl
  cong-cons refl eq (Fin.suc x) = eq x

  cong-seq : ∀ {n m p} {σ σ' : Subst n m} {τ τ' : Subst m p}
    → σ ≗ σ' → τ ≗ τ'
    → (σ ⨾ τ) ≗ (σ' ⨾ τ')
  cong-seq {σ' = σ'} {τ = τ} eqσ eqτ x
    = trans (cong (subst τ) (eqσ x))
            (cong-sub {P = σ' x} eqτ refl)

  sub-id : ∀ {n} (P : Proc n) → ⟪ ids ⟫ P ≡ P
  sub-id ∅ = refl
  sub-id (# x) = refl
  sub-id (α ∙ P) = cong (α ∙_) (sub-id P)
  sub-id (P ＋ Q) = cong₂ _＋_ (sub-id P) (sub-id Q)
  sub-id (P ∣ Q) = cong₂ _∣_ (sub-id P) (sub-id Q)
  sub-id (P ∖ a) = cong (_∖ a) (sub-id P)
  sub-id (P [ φ ]) = cong (_[ φ ]) (sub-id P)
  sub-id (fix P)
    = trans (cong fix (cong-sub {P = P}
                        (λ { Fin.zero → refl ; (Fin.suc x) → refl }) refl))
            (cong fix (sub-id P))

  sub-idR : ∀ {n m} {σ : Subst n m} → (σ ⨾ ids) ≗ σ
  sub-idR {σ = σ} x = sub-id (σ x)

  sub-idL : ∀ {n m} {σ : Subst n m} → (ids ⨾ σ) ≗ σ
  sub-idL x = refl

  sub-sub : ∀ {n m p} {P : Proc n} {σ : Subst n m} {σ' : Subst m p} →
    ⟪ σ' ⟫ (⟪ σ ⟫ P) ≡ ⟪ σ ⨾ σ' ⟫ P
  sub-sub {P = ∅} = refl
  sub-sub {P = # x} = refl
  sub-sub {P = α ∙ P} = cong (α ∙_) (sub-sub {P = P})
  sub-sub {P = P ＋ Q} = cong₂ _＋_ (sub-sub {P = P}) (sub-sub {P = Q})
  sub-sub {P = P ∣ Q} = cong₂ _∣_ (sub-sub {P = P}) (sub-sub {P = Q})
  sub-sub {P = P ∖ a} = cong (_∖ a) (sub-sub {P = P})
  sub-sub {P = P [ φ ]} = cong (_[ φ ]) (sub-sub {P = P})
  sub-sub {P = fix P} {σ} {σ'} = begin
    ⟪ σ' ⟫ (⟪ σ ⟫ (fix P)) ≡⟨⟩
    fix (⟪ exts σ' ⟫ (⟪ exts σ ⟫ P)) ≡⟨ cong fix (sub-sub {P = P} {σ = exts σ} {σ' = exts σ'}) ⟩
    fix (⟪ exts σ ⨾ exts σ' ⟫ P) ≡⟨ cong fix (cong-sub {P = P} exts-seq refl) ⟩
    fix (⟪ exts (σ ⨾ σ') ⟫ P) ∎

  sub-assoc : ∀ {n m p q} {σ : Subst n m} {τ : Subst m p} {θ : Subst p q} →
    (σ ⨾ τ) ⨾ θ ≗ σ ⨾ τ ⨾ θ
  sub-assoc {σ = σ} x = sub-sub {P = σ x}

  subst-commute : ∀ {n m} {P : Proc (suc (suc n))} {Q : Proc (suc n)} {σ : Subst (suc n) m } →
     ⟪ exts σ ⟫ P [0↦ ⟪ σ ⟫ Q ] ≡ ⟪ σ ⟫ (P [0↦ Q ])
  subst-commute {n} {m} {P} {Q} {σ} = begin
      subst (subst-zero (subst σ Q)) (subst (exts σ) P)
    ≡⟨ cong-sub {P = ⟪ exts σ ⟫ P} subst-Z-cons-ids refl ⟩
      subst (subst σ Q ⊙ #_) (subst (exts σ) P)
    ≡⟨ sub-sub {P = P} ⟩
      subst (exts σ ⨾ (subst σ Q ⊙ #_)) P
    ≡⟨ cong-sub {P = P} (cong-seq exts-suc-shift λ _ → refl) refl ⟩
      subst (((# Fin.zero) ⊙ (σ ⨾ (λ z → # Fin.suc z))) ⨾ (subst σ Q ⊙ #_)) P
    ≡⟨ cong-sub {P = P} sub-dist refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ ((σ ⨾ ↑) ⨾ (⟪ σ ⟫ Q ⊙ ids)) ⟫ P
    ≡⟨ cong-sub {P = P} (cong-cons refl (sub-assoc {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (σ ⨾ ↑ ⨾ (⟪ σ ⟫ Q) ⊙ ids) ⟫ P
    ≡⟨ cong-sub {P = P} (λ _ → refl) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (σ ⨾ ids) ⟫ P
    ≡⟨ cong-sub {P = P}  (cong-cons refl (sub-idR {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ σ ⟫ P
    ≡⟨ cong-sub {P = P} (cong-cons refl (sub-idL {σ = σ})) refl ⟩
      ⟪ ⟪ σ ⟫ Q ⊙ (ids ⨾ σ) ⟫ P
    ≡⟨ cong-sub {P = P} (sym ∘ sub-dist) refl ⟩
      ⟪ (Q ⊙ ids) ⨾ σ ⟫ P
    ≡⟨ sym (sub-sub {P = P}) ⟩
      ⟪ σ ⟫ (⟪ Q ⊙ ids ⟫ P)
    ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub {P = P} subst-Z-cons-ids refl)) ⟩
    ⟪ σ ⟫ (P [0↦ Q ]) ∎
