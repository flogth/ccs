{-# OPTIONS --allow-unsolved-metas #-} -- TODO: remove
open import Relation.Binary.Core using (Rel)
open import Action
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Level renaming (suc to lsuc)
open import Data.Fin

module Guarded {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  import Syntax
  open Syntax A _≈_ {Action}

  data _guarded-on_ {n} : Proc n → List Aτ → Set ℓ where
    
    guarded-∙ : ∀ {α} {P} {A} →
                α ∉ A →         -- TODO: work with ≈ᶜ Setoid
                (α ∙ P) guarded-on A

    guarded-＋ : ∀ {P Q} {A} →
              P guarded-on A →
              Q guarded-on A →
              (P ＋ Q) guarded-on A

    guarded-∣ : ∀ {P Q} {A} →
              P guarded-on A →
              Q guarded-on A →
              (P ∣ Q) guarded-on A

    guarded-∖ : ∀ {α} {P} {A} →
                P guarded-on (act α ∷ A) →
                (P ∖ α) guarded-on A

    guarded-ren : ∀ {P} {φ} {A} →
                  P guarded-on A →
                  (P [ φ ]) guarded-on A

    guarded-fix : ∀ {P} {A} →
                  P guarded-on A →
                  (fix P) guarded-on A

  open _guarded-on_

  guarded : ∀ {n} → Proc n → Set ℓ
  guarded P = P guarded-on []
  

  guarded-on-subst : ∀ {n} (P : Proc (suc n)) (A : List Aτ) → {σ : Fin (suc n) → Proc n} →
                  P guarded-on A → (subst σ P) guarded-on A
  guarded-on-subst (# x) A ()
  guarded-on-subst (α ∙ P) A (guarded-∙ x) = guarded-∙ x
  guarded-on-subst (P ＋ Q) A (guarded-＋ guardP guardQ)
    = guarded-＋ (guarded-on-subst P A guardP) (guarded-on-subst Q A guardQ)
  guarded-on-subst (P ∣ Q) A (guarded-∣ guardP guardQ)
    = guarded-∣ (guarded-on-subst P A guardP) (guarded-on-subst Q A guardQ)
  guarded-on-subst (P ∖ a) A (guarded-∖ guard) = guarded-∖ (guarded-on-subst P (act a ∷ A) guard )
  guarded-on-subst (P [ φ ]) A (guarded-ren guard) = guarded-ren (guarded-on-subst P A guard)
  guarded-on-subst (fix P) A (guarded-fix guard) = guarded-fix (guarded-on-subst P A guard)

  
  guarded-subst : ∀ {n} (P : Proc (suc n)) → {σ : Fin (suc n) → Proc n} →
                    guarded P → guarded (subst σ P)
  guarded-subst P = guarded-on-subst P []

  guarded-[0↦] : ∀ {n} (P : Proc (suc n)) → {Q : Proc n} →
                 guarded P → guarded (P [0↦ Q ])
  guarded-[0↦] P = guarded-subst P


  ∉-weaken : ∀ {ℓ} {A : Set ℓ} {a x : A} {xs : List A} → a ∉ x ∷ xs → a ∉ xs
  ∉-weaken p q = p (there q)

  ∉-perm : ∀ {ℓ} {A : Set ℓ} {a x y : A} {xs : List A} → a ∉ x ∷ y ∷ xs → a ∉ y ∷ x ∷ xs
  ∉-perm p (here a≡y) = p (there (here a≡y))
  ∉-perm p (there (here a≡x)) = p (here a≡x)
  ∉-perm p (there (there q)) = p (there (there q))

  guarded-perm : ∀ {n} → {P : Proc n} {a b : Aτ} {A : List Aτ} → P guarded-on (a ∷ b ∷ A) → P guarded-on (b ∷ a ∷ A)
  guarded-perm (guarded-∙ x) = guarded-∙ (∉-perm x)
  guarded-perm (guarded-＋ guardP guardQ) = guarded-＋ (guarded-perm guardP) (guarded-perm guardQ)
  guarded-perm (guarded-∣ guardP guardQ) = guarded-∣ (guarded-perm guardP) (guarded-perm guardQ)
  guarded-perm (guarded-∖ guard) = guarded-∖ {!!}
  guarded-perm (guarded-ren guard) = guarded-ren (guarded-perm guard)
  guarded-perm (guarded-fix guard) = guarded-fix (guarded-perm guard)

  guarded-weaken : ∀ {n} → (P : Proc n) → {a : Aτ} → {A : List Aτ} → P guarded-on (a ∷ A) → P guarded-on A
  guarded-weaken ∅ ()
  guarded-weaken (# x) ()
  guarded-weaken (α ∙ P) (guarded-∙ p) = guarded-∙ (∉-weaken p)
  guarded-weaken (P ＋ Q) (guarded-＋ guardP guardQ) = guarded-＋ (guarded-weaken P guardP) (guarded-weaken Q guardQ)
  guarded-weaken (P ∣ Q) (guarded-∣ guardP guardQ) =  guarded-∣ (guarded-weaken P guardP) (guarded-weaken Q guardQ)
  guarded-weaken (P ∖ a) (guarded-∖ guard) = guarded-∖ (guarded-weaken P (guarded-perm guard))
  guarded-weaken (P [ φ ]) (guarded-ren guard) = guarded-ren (guarded-weaken P guard)
  guarded-weaken (fix P) (guarded-fix guard) = guarded-fix (guarded-weaken P guard)
