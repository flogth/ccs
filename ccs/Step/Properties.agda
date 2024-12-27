open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality renaming (subst to ≡-subst) hiding ([_])
open import Data.Fin hiding (#_)
open import Data.Product
open import Action

module Step.Properties {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Syntax {ℓ} A {dec} {Action}
  open import Guarded {ℓ} A {dec} {Action}
  open import Step {ℓ} A {dec} {Action}

  _⇔_ : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
  A ⇔ B = (A → B) × (B → A)

  -- Equivalence of the two fixpoint semantics
  module Standard⇔Alternative where

    open import Step.Standard {ℓ} A {dec} {Action}
    open import Step.Alternative {ℓ} A {dec} {Action} renaming (_⟨_⟩fix⇒_ to _⟨_⟩fix'⇒_; Fix to Fix')

    subst-fix-swap : ∀ {n} {α : Aτ} (P : Proc (suc n)) → (S : Proc  n) {Q T : Proc  n} →
      guarded P →
      S ⟨ α ⟩fix⇒ Q →
      S ≡ P [0↦ T ] →
      Σ (Proc (suc n)) λ Q' → (P ⟨ α ⟩fix⇒ Q') × (Q ≡ Q' [0↦ T ])
    subst-fix-swap (α ∙ P) _ g Prefix refl = P , Prefix , refl
    subst-fix-swap (P ＋ _) _ {T = T} (guarded-＋ gP _) (Sumₗ s) refl with subst-fix-swap P (P [0↦ T ]) gP s refl
    ... | P' , s , eq = P' , Sumₗ s , eq
    subst-fix-swap (_ ＋ Q) _ {T = T} (guarded-＋ _ gQ) (Sumᵣ s) refl with subst-fix-swap Q (Q [0↦ T ]) gQ s refl
    ... | Q' , s , eq = Q' , Sumᵣ s , eq
    subst-fix-swap (P ∣ Q) _ {T = T} (guarded-∣ gP _) (Compₗ s) refl with subst-fix-swap P (P [0↦ T ]) gP s refl
    ... | P' , s , eq = (P' ∣ Q) , Compₗ s , cong (_∣ (Q [0↦ T ])) eq
    subst-fix-swap (P ∣ Q) _ {T = T} (guarded-∣ _ gQ) (Compᵣ s) refl with subst-fix-swap Q (Q [0↦ T ]) gQ s refl
    ... | Q' , s , eq = (P ∣ Q') , Compᵣ s , cong ((P [0↦ T ]) ∣_) eq
    subst-fix-swap (P ∣ Q) _ {T = T} (guarded-∣ gP gQ) (Sync {P' = P''} {Q' = Q''} s t) refl with subst-fix-swap P (P [0↦ T ]) gP s refl | subst-fix-swap Q (Q [0↦ T ]) gQ t refl
    ... | P' , sP , eqP | Q' , sQ , eqQ = P' ∣ Q' , Sync sP sQ , trans (cong (_∣ Q'') eqP) (cong ((P' [0↦ T ]) ∣_) eqQ)
    subst-fix-swap (P ∖ a) _ {T = T} (guarded-∖ gP) (Res s p) refl with subst-fix-swap P (P [0↦ T ]) gP s refl
    ... | P' , s , eq = (P' ∖ a) , Res s p , cong (_∖ a) eq
    subst-fix-swap (P [ φ ]) _ {T = T} (guarded-ren gP) (Ren s) refl with subst-fix-swap P (P [0↦ T ]) gP s refl
    ... | P' , s , eq = (P' [ φ ]) , Ren s , cong (_[ φ ]) eq
    subst-fix-swap (fix P) _ {Q} {T} (guarded-fix gP) (Fix s) refl =
      let (P' , s , eq) = subst-fix-swap (P [0↦ fix P ]) ((P [1↦ T ]) [0↦ fix (P [1↦ T ])]) (guarded-subst gP) s (subst-commute {P = P} {Q = fix P} {σ = subst-zero T})
      in P' , Fix s , eq

    fix⇒fix' : ∀ {n} {α : Aτ} {P P' : Proc n} →
      (guarded P) →
      P ⟨ α ⟩fix⇒ P' →
      P ⟨ α ⟩fix'⇒ P'
    fix⇒fix' (guarded-＋ gP _) (Sumₗ s) = Sumₗ (fix⇒fix' gP s)
    fix⇒fix' (guarded-＋ _ gQ) (Sumᵣ s) = Sumᵣ (fix⇒fix' gQ s)
    fix⇒fix' (guarded-∣ gP _) (Compₗ s) = Compₗ (fix⇒fix' gP s)
    fix⇒fix' (guarded-∣ _ gQ) (Compᵣ s) = Compᵣ (fix⇒fix' gQ s)
    fix⇒fix' (guarded-∣ gP gQ) (Sync s p) = Sync (fix⇒fix' gP s) (fix⇒fix' gQ p)
    fix⇒fix' (guarded-∖ gP) (Res s p) = Res (fix⇒fix' gP s) p
    fix⇒fix' (guarded-ren gP) (Ren s) = Ren (fix⇒fix' gP s)
    fix⇒fix' guarded-∙ Prefix = Prefix
    fix⇒fix' {α = α} (guarded-fix gP) (Fix {P = P} s) = let (_ , step , eq) = subst-fix-swap P (P [0↦ fix P ]) gP s refl in
      ≡-subst (λ h → fix P ⟨ α ⟩fix'⇒ h) (sym eq) (Fix' (fix⇒fix' gP step))

    -- this direction does indeed hold only for guarded terms:
    module counter-example (α : A) where
      open import Relation.Nullary using (¬_)

      a ā : Aτ
      a = act α
      ā = act (comp α)

      cex : Proc zero
      cex = fix (# zero ∣ a ∙ ∅ ＋ ā ∙ ∅)

      fstep : ∃ λ P' → cex ⟨ τ ⟩fix⇒ P'
      fstep = (cex ∣ ∅) ∣ ∅ , Fix (Sync (Fix (Compᵣ (Sumₗ Prefix))) (Sumᵣ Prefix))

      no-step' : ∀ {m} {P' : Proc m } →  ¬ (cex ⟨ τ ⟩fix'⇒ P')
      no-step' (Fix' (Compᵣ (Sumₗ ())))
      no-step' (Fix' (Compᵣ (Sumᵣ ())))

    step-subst : ∀ {n} {α : Aτ} {P P' : Proc (suc n)} {σ : Subst (suc n) n} →
      P ⟨ α ⟩fix⇒ P' →
      ⟪ σ ⟫ P ⟨ α ⟩fix⇒ ⟪ σ ⟫ P'
    step-subst Prefix = Prefix
    step-subst (Sumₗ x) = Sumₗ (step-subst x)
    step-subst (Sumᵣ x) = Sumᵣ (step-subst x)
    step-subst (Compₗ x) = Compₗ (step-subst x)
    step-subst (Compᵣ x) = Compᵣ (step-subst x)
    step-subst (Sync x y) = Sync (step-subst x) (step-subst y)
    step-subst (Res x p) = Res (step-subst x) p
    step-subst (Ren x) = Ren (step-subst x)
    step-subst {α = α} {P = fix P} {P' = P'} {σ = σ} (Fix der) = Fix (≡-subst (_⟨ α ⟩fix⇒ ⟪ σ ⟫ P') helper (step-subst der))
       where
         helper : ⟪ σ ⟫ (P [0↦ fix P ]) ≡ (⟪ exts σ ⟫ P) [0↦ fix (⟪ exts σ ⟫ P) ]
         helper = sym (subst-commute  {P = P} {Q = fix P} {σ = σ})

    fix'⇒fix : ∀ {n} {α : Aτ} {P P' : Proc n} →
      P ⟨ α ⟩fix'⇒ P' →
      P ⟨ α ⟩fix⇒ P'
    fix'⇒fix Prefix = Prefix
    fix'⇒fix (Sumₗ s) = Sumₗ (fix'⇒fix s)
    fix'⇒fix (Sumᵣ s) = Sumᵣ (fix'⇒fix s)
    fix'⇒fix (Compₗ s) = Compₗ (fix'⇒fix s)
    fix'⇒fix (Compᵣ s) = Compᵣ (fix'⇒fix s)
    fix'⇒fix (Sync s p) = Sync (fix'⇒fix s) (fix'⇒fix p)
    fix'⇒fix (Res s p) = Res (fix'⇒fix s) p
    fix'⇒fix (Ren s) = Ren (fix'⇒fix s)
    fix'⇒fix (Fix' s) = Fix (step-subst (fix'⇒fix s))

    fix⇔fix' : ∀ {n} {α : Aτ} {P P' : Proc n} → (guarded P) → (P ⟨ α ⟩fix⇒ P') ⇔ (P ⟨ α ⟩fix'⇒ P')
    fix⇔fix' gP = (fix⇒fix' gP) , fix'⇒fix

  -- Equivalence of alternative fixpoint semantics and transitions with substitutions
  module Alternative⇔SubstitutionLabels where
    open import Step.Alternative A {dec} {Action} renaming (_⟨_⟩fix⇒_ to _⟨_⟩fix'⇒_; Fix to Fix')
    open import Step.SubstitutionLabels A {dec} {Action}
    fix'⇒step-subst : ∀ {n m} {α : Aτ} {P P' : Proc n} {P'' : Proc m} {σ : Subst n m} →
        P'' ≡ ⟪ σ ⟫ P' →
        P ⟨ α ⟩fix'⇒  P' →
        P ⟨ α , σ ⟩⇒ P''
    fix'⇒step-subst refl Prefix = Prefix
    fix'⇒step-subst refl (Sumₗ x) = Sumₗ (fix'⇒step-subst refl x)
    fix'⇒step-subst refl (Sumᵣ x) = Sumᵣ (fix'⇒step-subst refl x)
    fix'⇒step-subst refl (Compₗ x) = Compₗ (fix'⇒step-subst refl x)
    fix'⇒step-subst refl (Compᵣ x) = Compᵣ (fix'⇒step-subst refl x)
    fix'⇒step-subst refl (Sync x y) = Sync (fix'⇒step-subst refl x) (fix'⇒step-subst refl y)
    fix'⇒step-subst refl (Res x p) = Res (fix'⇒step-subst refl x) p
    fix'⇒step-subst refl (Ren x) = Ren (fix'⇒step-subst refl x)
    fix'⇒step-subst {α = α} {P = fix P} {σ = σ} refl (Fix' {P' = P'} x) rewrite (sub-sub {P = P'} {σ = subst-zero (fix P)} {σ' = σ}) = (Fix rec)
       where rec : P ⟨ α , (subst-zero (fix P) ⨾ σ) ⟩⇒ ⟪ subst-zero (fix P) ⨾ σ ⟫ P'
             rec = fix'⇒step-subst refl x

    step-subst⇒fix' : ∀ {n m} {α : Aτ} {P : Proc n} {P'' : Proc m} {σ : Subst n m} →
      P ⟨ α , σ ⟩⇒ P'' →
      ∃ λ P' → P'' ≡ ⟪ σ ⟫ P' × P ⟨ α ⟩fix'⇒ P'
    step-subst⇒fix' {P = α ∙ P} Prefix = P , refl , Prefix
    step-subst⇒fix' {σ = σ} (Sumₗ x) = let (P' , eq , s) = step-subst⇒fix' x in P' , eq , (Sumₗ s)
    step-subst⇒fix' (Sumᵣ x) = let (Q' , eq , s) = step-subst⇒fix' x in Q' , eq , (Sumᵣ s)
    step-subst⇒fix' {σ = σ} (Compₗ {Q = Q} x) = let (P' , eq , s) = step-subst⇒fix' x in P' ∣ Q , cong (_∣ ⟪ σ ⟫ Q) eq , Compₗ s
    step-subst⇒fix' {σ = σ} (Compᵣ {P = P} x) = let (Q' , eq , s) = step-subst⇒fix' x in P ∣ Q' , cong ((⟪ σ ⟫ P) ∣_) eq , Compᵣ s
    step-subst⇒fix' (Sync x y) = let (P' , eqP , sP) = step-subst⇒fix' x in
                        let (Q' , eqQ , sQ) = step-subst⇒fix' y in P' ∣ Q' , cong₂ _∣_ eqP eqQ , Sync sP sQ
    step-subst⇒fix' (Res {a = a} x p) = let (P' , eq , s) = step-subst⇒fix' x in (P' ∖ a) , cong (_∖ a) eq , Res s p
    step-subst⇒fix' (Ren {φ = φ} x) = let (P' , eq , s) = step-subst⇒fix' x in (P' [ φ ]) , cong (_[ φ ]) eq , Ren s
    step-subst⇒fix' {σ = σ} (Fix {P = P} x) = let (P' , eq , s) = step-subst⇒fix' x in (P' [0↦ fix P ]) , trans eq (sym (sub-sub {P = P'} {σ = subst-zero (fix P)} {σ' = σ}))  , Fix' s

    subst-step⇔fix' :  ∀ {n m} {α : Aτ} {P : Proc n} {P'' : Proc m} {σ : Subst n m} →
      (P ⟨ α , σ ⟩⇒ P'') ⇔ (∃ λ P' → P'' ≡ ⟪ σ ⟫ P' × P ⟨ α ⟩fix'⇒ P')
    subst-step⇔fix' = step-subst⇒fix' , (λ x → fix'⇒step-subst (proj₁ (proj₂ x)) (proj₂ (proj₂ x)))
