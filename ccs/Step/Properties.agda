open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.List
open import Data.Product
open import Action

module Step.Properties {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  import Syntax
  open Syntax A {dec} {Action}
  open import Guarded A {dec} {Action}
  open import Step A


  guarded-step : ∀ {n} → {P : Proc n} → guarded P →
                 List (Σ Aτ λ α → Σ (Proc n) λ P' → P ⟨ α ⟩⇒ P')
  guarded-step guarded-∅ = []
  guarded-step (guarded-＋ p q) = let ps = guarded-step p in Data.List.map (λ (a , P , s) → a , {!P ＋ Q!} , {!!}) ps
  guarded-step (guarded-∣ p q) = {!!}
  guarded-step (guarded-∖ guard) = {!!}
  guarded-step (guarded-ren guard) = {!!}
  guarded-step (guarded-∙) = {!!}
  guarded-step (guarded-fix guard) = {!!}

  -- Equivalence of the two semantics

  subst-step-fix : ∀ {n} {α : Aτ} (P : Proc (suc n)) {Q T : Proc  n} →
    guarded P →
    (P [0↦ T ]) ⟨ α ⟩fix⇒ Q →
    Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩fix⇒ Q' [0↦ T ]) × (Q ≡ Q' [0↦ T ])
  subst-step-fix ∅ gP s = {!!}
  subst-step-fix (α ∙ P) gP s = {!!}
  subst-step-fix (P ＋ Q) gP s = {!!}
  subst-step-fix (P ∣ Q) gP s = {!!}
  subst-step-fix (P ∖ a) gP s = {!!}
  subst-step-fix (P [ φ ]) gP s = {!!}
  subst-step-fix (fix P) gP s = {!!}
  
  fix-equiv-to : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (guarded P) →
    (s : P ⟨ α ⟩fix⇒ P') →
    P ⟨ α ⟩fix'⇒ P'
  fix-equiv-to gP (Step s) = Step' s
  fix-equiv-to gP (Fix {P = ∅} (Step ()))
  fix-equiv-to gP (Fix {P = # zero} s) = fix-equiv-to gP s
  fix-equiv-to gP (Fix {P = Syntax.# suc x} (Step ()))
  fix-equiv-to (guarded-fix gP) (Fix {P = α ∙ P} {P' = P'} s) rewrite (proj₂ (proj₂ (subst-step-fix (α ∙ P) gP s))) = let (Q , qs , p) = subst-step-fix (α ∙ P) gP s in {!!}
  fix-equiv-to (guarded-fix gP) (Fix {P = P ＋ Q} (Step x)) = let (Q, ps, p) = subst-step-fix (P ＋ Q) gP {! !}  in {!!}
  fix-equiv-to gP (Fix {P = P ∣ Q} s) = {!!}
  fix-equiv-to gP (Fix {P = P ∖ a} s) = {!!}
  fix-equiv-to gP (Fix {P = P [ φ ]} s) = {!!}
  fix-equiv-to gP (Fix {P = fix P} s) = fix-equiv-to gP {!!}

  fix-equiv-from : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (s : P ⟨ α ⟩fix'⇒ P') →
    P ⟨ α ⟩fix⇒ P'
  fix-equiv-from (Step' s) = Step s
  fix-equiv-from (Fix' {P = ∅} (Step' ()))
  fix-equiv-from (Fix' {P = # x} s) = {!!}
  fix-equiv-from (Fix' {P = α ∙ P} s) = {!!}
  fix-equiv-from (Fix' {P = P ＋ Q} s) = {!!}
  fix-equiv-from (Fix' {P = P ∣ Q} s) = {!!}
  fix-equiv-from (Fix' {P = P ∖ a} s) = {!!}
  fix-equiv-from (Fix' {P = P [ φ ]} s) = {!!}
  fix-equiv-from (Fix' {P = fix P} s) = {!!}
