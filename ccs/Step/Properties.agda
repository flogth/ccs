open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality renaming (subst to ≡-subst) hiding ([_])
open ≡-Reasoning
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

  subst-swap : ∀ {n} (P : Proc (suc (suc n))) {T : Proc n} →
                (subst (exts (σ T)) P) [0↦ fix (subst (exts (σ T)) P)] ≡ subst (σ T) (P [0↦ fix P ])
  subst-swap ∅ = refl
  subst-swap (# x) = {!!}
  subst-swap (α ∙ P) {T} = cong (α ∙_) {!!}
  subst-swap (P ＋ Q) = begin
    {!!} ≡⟨ {!!} ⟩
    {!!} ∎
  subst-swap (P ∣ Q) = {!!}
  subst-swap (P ∖ a) = {!!}
  subst-swap (P [ φ ]) = {!!}
  subst-swap (fix P) = {!!}

  {-# TERMINATING #-}
  subst-step-fix : ∀ {n} {α : Aτ} (P : Proc (suc n)) {Q T : Proc  n} →
    guarded P →
    (P [0↦ T ]) ⟨ α ⟩fix⇒ Q →
    Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩fix⇒ Q') × (Q ≡ Q' [0↦ T ])
  subst-step-fix ∅ gP (Step ())
  subst-step-fix (α ∙ P) gP (Step Prefix) = P , Step Prefix , refl
  subst-step-fix (P ＋ Q) (guarded-＋ gP _) (Step (Sumₗ x)) with subst-step-fix P gP (Step x)
  ... | P' , Step s , eq = P' , Step (Sumₗ s) , eq
  subst-step-fix (P ＋ Q) (guarded-＋ _ gQ) (Step (Sumᵣ x)) with subst-step-fix Q gQ (Step x)
  ... | Q' , Step s , eq = Q' , Step (Sumᵣ s) , eq
  subst-step-fix (P ∣ Q) {T = T} (guarded-∣ gP _) (Step (Compₗ x)) with subst-step-fix P gP (Step x)
  ... | P' , Step s , eq = P' ∣ Q , Step (Compₗ s) , cong (λ h → h ∣ (Q [0↦ T ])) eq
  subst-step-fix (P ∣ Q) {T = T} (guarded-∣ _ gQ) (Step (Compᵣ x)) with subst-step-fix Q gQ (Step x)
  ... | Q' , Step s , eq = P ∣ Q' , Step (Compᵣ s) , cong (λ h → (P [0↦ T ]) ∣ h) eq
  subst-step-fix (P ∣ Q) {T = T} (guarded-∣ gP gQ) (Step (Sync {P' = P''} {Q' = Q''} x y)) with subst-step-fix P gP (Step x) | subst-step-fix Q gQ (Step y)
  ... | P' , Step sp , eqp | Q' , Step sq , eqq = P' ∣ Q' , Step (Sync sp sq) ,
      (begin
      P'' ∣ Q'' ≡⟨ cong (λ h → P'' ∣ h) eqq ⟩
      P'' ∣ (Q' [0↦ T ]) ≡⟨ cong (λ h → h ∣ (Q' [0↦ T ])) eqp ⟩
      (P' ∣ Q') [0↦ T ] ∎)
  subst-step-fix (P ∖ a) (guarded-∖ gP) (Step (Res x p q)) with subst-step-fix P gP (Step x)
  ... | P' , Step s , eq = (P' ∖ a) , Step (Res s p q) , cong (λ h → h ∖ a) eq
  subst-step-fix (P [ φ ]) (guarded-ren gP) (Step (Ren x)) with subst-step-fix P gP (Step x)
  ... | P' , Step s , eq = (P' [ φ ]) , Step (Ren s) , cong (λ h → h [ φ ]) eq
  subst-step-fix (fix P) {Q = Q} {T = T} (guarded-fix gP) (Fix x) rewrite subst-swap P {T = T} with subst-step-fix (P [0↦ fix P ]) (guarded-subst gP) x
  ... | P' , s , eq = P' , Fix s , eq


  fix-equiv-to : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (guarded P) →
    (s : P ⟨ α ⟩fix⇒ P') →
    P ⟨ α ⟩fix'⇒ P'
  fix-equiv-to gP (Step s) = Step' s
  fix-equiv-to {α = α} (guarded-fix gP) (Fix {P = P} s) with subst-step-fix P gP s
  ... | Q' , step , eq = ≡-subst (λ h → fix P ⟨ α ⟩fix'⇒ h) (sym eq) (Fix' (fix-equiv-to gP step))

  step-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {T : Proc n} →
    P ⟨ α ⟩⇒ P' →
    P [0↦ T ] ⟨ α ⟩⇒ P' [0↦ T ]
  step-subst Prefix = Prefix
  step-subst (Sumₗ x) = Sumₗ (step-subst x)
  step-subst (Sumᵣ x) = Sumᵣ (step-subst x)
  step-subst (Compₗ x) = Compₗ (step-subst x)
  step-subst (Compᵣ x) = Compᵣ (step-subst x)
  step-subst (Sync x y) = Sync (step-subst x) (step-subst y)
  step-subst (Res x p q) = Res (step-subst x) p q
  step-subst (Ren x) = Ren (step-subst x)

  fix-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {T : Proc n} →
    P ⟨ α ⟩fix⇒ P' →
    P [0↦ T ] ⟨ α ⟩fix⇒ P' [0↦ T ]
  fix-subst (Step x) = Step (step-subst x)
  fix-subst {T = T} (Fix x) with fix-subst {T = T} x
  ... | p = Fix {!!}

  fix-equiv-from : ∀ {n} {α : Aτ} {P P' : Proc n} →
    (s : P ⟨ α ⟩fix'⇒ P') →
    P ⟨ α ⟩fix⇒ P'
  fix-equiv-from (Step' s) = Step s
  fix-equiv-from (Fix' s) with fix-equiv-from s
  ... | p = Fix (fix-subst p)
