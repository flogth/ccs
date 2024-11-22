open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality renaming (subst to ≡-subst) hiding ([_])
open import Data.Fin
open import Data.Product
open import Action

module Step.Properties {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Syntax {ℓ} A {dec} {Action}
  open import Guarded {ℓ} A {dec} {Action}
  open import Step {ℓ} A {dec} {Action}

  -- Equivalence of the two semantics

  subst-step : ∀ {n} {α : Aτ} (P : Proc (suc n)) → (S : Proc  n) {Q T : Proc  n} →
    guarded P →
    S ⟨ α ⟩fix⇒ Q →
    S ≡ P [0↦ T ] →
    Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩fix⇒ Q') × (Q ≡ Q' [0↦ T ])
  subst-step (α ∙ P) _ g Prefix refl = P , Prefix , refl
  subst-step (P ＋ _) _ {T = T} (guarded-＋ gP _) (Sumₗ s) refl with subst-step P (P [0↦ T ]) gP s refl
  ... | P' , s , eq = P' , Sumₗ s , eq
  subst-step (_ ＋ Q) _ {T = T} (guarded-＋ _ gQ) (Sumᵣ s) refl with subst-step Q (Q [0↦ T ]) gQ s refl
  ... | Q' , s , eq = Q' , Sumᵣ s , eq
  subst-step (P ∣ Q) _ {T = T} (guarded-∣ gP _) (Compₗ s) refl with subst-step P (P [0↦ T ]) gP s refl
  ... | P' , s , eq = (P' ∣ Q) , Compₗ s , cong (_∣ (Q [0↦ T ])) eq
  subst-step (P ∣ Q) _ {T = T} (guarded-∣ _ gQ) (Compᵣ s) refl with subst-step Q (Q [0↦ T ]) gQ s refl
  ... | Q' , s , eq = (P ∣ Q') , Compᵣ s , cong ((P [0↦ T ]) ∣_) eq
  subst-step (P ∣ Q) _ {T = T} (guarded-∣ gP gQ) (Sync {P' = P''} {Q' = Q''} s t) refl with subst-step P (P [0↦ T ]) gP s refl | subst-step Q (Q [0↦ T ]) gQ t refl
  ... | P' , sP , eqP | Q' , sQ , eqQ = P' ∣ Q' , Sync sP sQ , trans (cong (_∣ Q'') eqP) (cong ((P' [0↦ T ]) ∣_) eqQ)
  subst-step (P ∖ a) _ {T = T} (guarded-∖ gP) (Res s p q) refl with subst-step P (P [0↦ T ]) gP s refl
  ... | P' , s , eq = (P' ∖ a) , Res s p q , cong (_∖ a) eq
  subst-step (P [ φ ]) _ {T = T} (guarded-ren gP) (Ren s) refl with subst-step P (P [0↦ T ]) gP s refl
  ... | P' , s , eq = (P' [ φ ]) , Ren s , cong (_[ φ ]) eq
  subst-step (fix P) _ {Q} {T} (guarded-fix gP) (Fix s) refl =
    let (P' , s , eq) = subst-step (P [0↦ fix P ]) ((P [1↦ T ]) [0↦ fix (P [1↦ T ])]) (guarded-subst gP) s (subst-commute {P = P} {Q = fix P} {σ = subst-zero T})
    in P' , Fix s , eq

  fix-equiv-to : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (guarded P) →
    P ⟨ α ⟩fix⇒ P' →
    P ⟨ α ⟩fix'⇒ P'
  fix-equiv-to (guarded-＋ gP _) (Sumₗ s) = Sumₗ (fix-equiv-to gP s)
  fix-equiv-to (guarded-＋ _ gQ) (Sumᵣ s) = Sumᵣ (fix-equiv-to gQ s)
  fix-equiv-to (guarded-∣ gP _) (Compₗ s) = Compₗ (fix-equiv-to gP s)
  fix-equiv-to (guarded-∣ _ gQ) (Compᵣ s) = Compᵣ (fix-equiv-to gQ s)
  fix-equiv-to (guarded-∣ gP gQ) (Sync s p) = Sync (fix-equiv-to gP s) (fix-equiv-to gQ p)
  fix-equiv-to (guarded-∖ gP) (Res s p q) = Res (fix-equiv-to gP s) p q
  fix-equiv-to (guarded-ren gP) (Ren s) = Ren (fix-equiv-to gP s)
  fix-equiv-to guarded-∙ Prefix = Prefix
  fix-equiv-to {α = α} (guarded-fix gP) (Fix {P = P} s) = let (_ , step , eq) = subst-step P (P [0↦ fix P ]) gP s refl in
    ≡-subst (λ h → fix P ⟨ α ⟩fix'⇒ h) (sym eq) (Fix' (fix-equiv-to gP step))

  step-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {σ : Subst (suc n) n} →
    P ⟨ α ⟩fix⇒ P' →
    ⟪ σ ⟫ P ⟨ α ⟩fix⇒ ⟪ σ ⟫ P'
  step-subst Prefix = Prefix
  step-subst (Sumₗ x) = Sumₗ (step-subst x)
  step-subst (Sumᵣ x) = Sumᵣ (step-subst x)
  step-subst (Compₗ x) = Compₗ (step-subst x)
  step-subst (Compᵣ x) = Compᵣ (step-subst x)
  step-subst (Sync x y) = Sync (step-subst x) (step-subst y)
  step-subst (Res x p q) = Res (step-subst x) p q
  step-subst (Ren x) = Ren (step-subst x)
  step-subst {α = α} {P = fix P} {P' = P'} {σ = σ} (Fix der) = Fix (≡-subst (_⟨ α ⟩fix⇒ ⟪ σ ⟫ P') helper (step-subst der))
     where
       helper : ⟪ σ ⟫ (P [0↦ fix P ]) ≡ (⟪ exts σ ⟫ P) [0↦ fix (⟪ exts σ ⟫ P) ]
       helper = sym (subst-commute  {P = P} {Q = fix P} {σ = σ})

  fix-equiv-from : ∀ {n} {α : Aτ} {P P' : Proc n} →
    P ⟨ α ⟩fix'⇒ P' →
    P ⟨ α ⟩fix⇒ P'
  fix-equiv-from Prefix = Prefix
  fix-equiv-from (Sumₗ s) = Sumₗ (fix-equiv-from s)
  fix-equiv-from (Sumᵣ s) = Sumᵣ (fix-equiv-from s)
  fix-equiv-from (Compₗ s) = Compₗ (fix-equiv-from s)
  fix-equiv-from (Compᵣ s) = Compᵣ (fix-equiv-from s)
  fix-equiv-from (Sync s p) = Sync (fix-equiv-from s) (fix-equiv-from p)
  fix-equiv-from (Res s p q) = Res (fix-equiv-from s) p q
  fix-equiv-from (Ren s) = Ren (fix-equiv-from s)
  fix-equiv-from (Fix' s) = Fix (step-subst (fix-equiv-from s))

  -- Equivalence of alternative fixpoint semantics and transitions with substitutions
  eqv-from : ∀ {n m} {α : Aτ} {P P' : Proc n} {P'' : Proc m} {σ : Subst n m} →
      P'' ≡ ⟪ σ ⟫ P' →
      P ⟨ α ⟩fix'⇒  P' →
      P ⟨ α ⟩ σ ⇒ P''
  eqv-from refl Prefix = Prefix
  eqv-from refl (Sumₗ x) = Sumₗ (eqv-from refl x)
  eqv-from refl (Sumᵣ x) = Sumᵣ (eqv-from refl x)
  eqv-from refl (Compₗ x) = Compₗ (eqv-from refl x)
  eqv-from refl (Compᵣ x) = Compᵣ (eqv-from refl x)
  eqv-from refl (Sync x y) = Sync (eqv-from refl x) (eqv-from refl y)
  eqv-from refl (Res x p q) = Res (eqv-from refl x) p q
  eqv-from refl (Ren x) = Ren (eqv-from refl x)
  eqv-from {α = α} {P = fix P} {σ = σ} refl (Fix' {P' = P'} x) rewrite (sub-sub {P = P'} {σ = subst-zero (fix P)} {σ' = σ}) = (Fix rec)
     where rec : P ⟨ α ⟩ (subst-zero (fix P) ⨾ σ) ⇒ ⟪ subst-zero (fix P) ⨾ σ ⟫ P'
           rec = eqv-from refl x

  eqv-to : ∀ {n m} {α : Aτ} {P : Proc n} {P'' : Proc m} {σ : Subst n m} →
    P ⟨ α ⟩ σ ⇒ P'' →
    ∃ λ P' → P'' ≡ ⟪ σ ⟫ P' × P ⟨ α ⟩fix'⇒ P'
  eqv-to {P = α ∙ P} Prefix = P , refl , Prefix
  eqv-to {σ = σ} (Sumₗ x) = let (P' , eq , s) = eqv-to x in P' , eq , (Sumₗ {!!})
  eqv-to (Sumᵣ x) = {!!}
  eqv-to (Compₗ x) = {!!}
  eqv-to (Compᵣ x) = {!!}
  eqv-to (Sync x x₁) = {!!}
  eqv-to (Res x x₁ x₂) = {!!}
  eqv-to (Ren x) = {!!}
  eqv-to (Fix x) = {!!}
