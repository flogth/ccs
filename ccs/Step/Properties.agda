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
    S ⟨ α ⟩⇒ Q →
    S ≡ P [0↦ T ] →
    Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩⇒ Q') × (Q ≡ Q' [0↦ T ])
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

  subst-step-fix : ∀ {n} {α : Aτ} (P : Proc (suc n)) → (S : Proc  n) {Q T : Proc  n} →
    guarded P →
    S ⟨ α ⟩fix⇒ Q →
    S ≡ P [0↦ T ] →
    Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩fix⇒ Q') × (Q ≡ Q' [0↦ T ])
  subst-step-fix P S g (Step x) eq with subst-step P S g x eq
  ... | Q' , s , eq = Q' , Step s , eq
  subst-step-fix {n} (fix P) .(fix (P [1↦ T ])) {Q}{T} (guarded-fix gP) (Fix der) refl
    with subst-step-fix (P [0↦ fix P ]) ((P [1↦ T ]) [0↦ fix (P [1↦ T ])]) (guarded-subst gP) der (subst-commute {P = P} {Q = fix P} {σ = subst-zero T})
  ... | P' , s , eq = P' , Fix s , eq

  fix-equiv-to : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (guarded P) →
    P ⟨ α ⟩fix⇒ P' →
    P ⟨ α ⟩fix'⇒ P'
  fix-equiv-to gP (Step s) = Step' s
  fix-equiv-to {α = α} {P' = P'} (guarded-fix gP) (Fix {P = P} s) with subst-step-fix P (P [0↦ fix P ]) gP s refl
  ... | Q' , step , eq = ≡-subst (λ h → fix P ⟨ α ⟩fix'⇒ h) (sym eq) (Fix' (fix-equiv-to gP step))

  step-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {σ : Subst (suc n) n} →
    P ⟨ α ⟩⇒ P' →
    ⟪ σ ⟫ P ⟨ α ⟩⇒ ⟪ σ ⟫ P'
  step-subst Prefix = Prefix
  step-subst (Sumₗ x) = Sumₗ (step-subst x)
  step-subst (Sumᵣ x) = Sumᵣ (step-subst x)
  step-subst (Compₗ x) = Compₗ (step-subst x)
  step-subst (Compᵣ x) = Compᵣ (step-subst x)
  step-subst (Sync x y) = Sync (step-subst x) (step-subst y)
  step-subst (Res x p q) = Res (step-subst x) p q
  step-subst (Ren x) = Ren (step-subst x)

  fix-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {σ : Subst (suc n) n} →
    P ⟨ α ⟩fix⇒ P' →
    ⟪ σ ⟫ P  ⟨ α ⟩fix⇒ ⟪ σ ⟫ P'
  fix-subst (Step x) = Step (step-subst x)
  fix-subst {α = α} {P = fix P} {P' = P'} {σ = σ} (Fix der) = Fix (≡-subst (_⟨ α ⟩fix⇒ ⟪ σ ⟫ P') helper (fix-subst der))
    where
      helper : ⟪ σ ⟫ (P [0↦ fix P ]) ≡ (⟪ exts σ ⟫ P) [0↦ fix (⟪ exts σ ⟫ P) ]
      helper = sym (subst-commute  {P = P} {Q = fix P} {σ = σ})

  fix-equiv-from : ∀ {n} {α : Aτ} {P P' : Proc n} →
    P ⟨ α ⟩fix'⇒ P' →
    P ⟨ α ⟩fix⇒ P'
  fix-equiv-from (Step' s) = Step s
  fix-equiv-from (Fix' s) = Fix (fix-subst (fix-equiv-from s))
