open import Action
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; cong) renaming (subst to ≡-subst)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes ; no)
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.List hiding ([_])
open import Data.Maybe
open import Data.Bool hiding (_≤?_)
open import Data.Fin hiding (#_ ; _≤?_)

module Step.ListLabels {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  open Action.Renaming A dec Action
  open import Syntax A {dec} {Action}
  open import Step A

  Sub : ℕ → Set ℓ
  Sub n = List (Maybe (Proc n))

  sub : ∀ {n m : ℕ} → Sub (suc n) → Proc m → Proc (n ⊔ m)
  sub ξ ∅ = ∅
  sub {n} {m} ξ (# x) with m ≤? length ξ
  ... | no _ = max-cast' n m (# x)
  ... | yes p = maybe (λ P → max-cast n m (fix P)) (max-cast' n m (# x)) (lookup ξ (inject≤ x p))
  sub ξ (α ∙ P) = α ∙ (sub ξ P)
  sub ξ (P ＋ Q) = (sub ξ P) ＋ (sub ξ Q)
  sub ξ (P ∣ Q) = (sub ξ P) ∣ (sub ξ Q)
  sub ξ (P ∖ a) = (sub ξ P) ∖ a
  sub ξ (P [ φ ]) = (sub ξ P) [ φ ]
  sub ξ (fix P) = fix (≡-subst Proc {!!} (sub (nothing ∷ ξ) P))

  infix 10 _⟨_⟩⇒_
  data _⟨_⟩⇒_ : {n m : ℕ} → (P : Proc m) → (Aτ × List (Maybe (Proc (suc n)))) → (Q : Proc (n ⊔ m)) → Set ℓ where
    Prefix : ∀ {n m} {α : Aτ} {P : Proc m} {ξ : Sub (suc n)} →
      α ∙ P ⟨ α , ξ ⟩⇒ sub ξ P

    Sumₗ : ∀ {n} {α : Aτ} {P Q : Proc n} {P' : Proc (n ⊔ n)} {ξ : Sub (suc n)} →
         P ⟨ α , ξ ⟩⇒ P' →
      ----------------------------------------
        (P ＋ Q) ⟨ α , ξ ⟩⇒ P'

    -- Sumᵣ : ∀ {n m} {α : Aτ} {P Q : Proc n} {Q' : Proc m} {σ : Subst n m} →
    --      Q ⟨ α , σ ⟩⇒ Q' →
    --   ----------------------------------------
    --     (P ＋ Q) ⟨ α , σ ⟩⇒ Q'

    Compₗ : ∀ {n m} {α : Aτ} {P Q : Proc m} {P' : Proc (n ⊔ m)} {ξ : Sub (suc n)} →
          P ⟨ α , ξ ⟩⇒ P' →
      ----------------------------------------
        (P ∣ Q) ⟨ α , ξ ⟩⇒ (P' ∣ sub ξ Q)

    -- Compᵣ : ∀ {n m} {α : Aτ} {P Q : Proc n} {Q' : Proc m} {σ : Subst n m} →
    --       Q ⟨ α , σ ⟩⇒ Q' →
    --   ----------------------------------------
    --     (P ∣ Q) ⟨ α , σ ⟩⇒ ((⟪ σ ⟫ P) ∣ Q')

    -- Sync : ∀ {n m} {a : A} {P Q : Proc n} {P' Q' : Proc m} {σ : Subst n m} →
    --      P ⟨ act a , σ ⟩⇒ P' →
    --      Q ⟨ act (comp a) , σ ⟩⇒ Q' →
    --   ----------------------------------------
    --     (P ∣ Q) ⟨ τ , σ ⟩⇒ (P' ∣ Q')

    -- Res : ∀ {n m} {α} {a : A} {P : Proc n} {P' : Proc m} {σ : Subst n m} →
    --     P ⟨ α , σ ⟩⇒ P' →
    --     α ≉ act a →
    --   ----------------------------------------
    --     (P ∖ a) ⟨ act a , σ ⟩⇒ (P' ∖ a)

    -- Ren : ∀ {n m} {α} {φ : Renaming} {P : Proc n} {P' : Proc m} {σ : Subst n m} →
    --     P ⟨ α , σ ⟩⇒ P' →
    --   ----------------------------------------
    --     (P [ φ ]) ⟨ ⟨ φ ⟩Aτ α , σ ⟩⇒ (P' [ φ ])

    Fix : ∀ {n} {α} {P : Proc (suc n)} {P' : Proc (n ⊔ n)} {ξ : Sub (suc n)} →
        P ⟨ α , just P ∷ ξ ⟩⇒ {!!} →
      ----------------------------------------
        fix P ⟨ α , ξ ⟩⇒ P'

  -- step : LTS (Aτ × ∀ {n m} → Subst n m)
  -- step .LTS.step P (a , s ) Q = P ⟨ a , s ⟩⇒ Q
