open import Action
open import Relation.Binary.Core using (Rel)
open import Data.Empty
open import Function.Bundles

module Step {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  import Syntax
  open Syntax A _≈_ {Action}

  _≉_ : Rel A ℓ
  a ≉ b = a ≈ b → ⊥

  -- one-step relation without `fix`
  infix 3 _⟨_⟩⇒_
  data _⟨_⟩⇒_ : CCS → Aτ → CCS → Set ℓ where
    Prefix : ∀ {α} {P} →
    ------------------------
      α ∙ P ⟨ α ⟩⇒ P

    Sumₗ : ∀ {α} {P Q P'} →
      P ⟨ α ⟩⇒ P' →
      ---------------------
      (P ＋ Q) ⟨ α ⟩⇒ P'

    Sumᵣ : ∀ {α} {P Q Q'} →
      Q ⟨ α ⟩⇒ Q' →
      ------------------
      (P ＋ Q) ⟨ α ⟩⇒ Q'

    Compₗ : ∀ {α} {P Q P'} →
      P ⟨ α ⟩⇒ P' →
      -------------------
      P ∣ Q ⟨ α ⟩⇒ P' ∣ Q

    Compᵣ : ∀ {α} {P Q Q'}  →
      Q ⟨ α ⟩⇒ Q' →
      -------------------
      P ∣ Q ⟨ α ⟩⇒ P ∣ Q'

    Sync : ∀ {a : A} {P P' Q Q'} →
      P ⟨ act a ⟩⇒ P' →
      Q ⟨ act (comp a)  ⟩⇒ Q' →
      --------------------
      P ∣ Q ⟨ τ ⟩⇒ P' ∣ Q'

    Res : ∀ {a b : A}  {P P'} →
      P ⟨ act a ⟩⇒ P' →
      a ≉  b →
      a ≉ comp b →
      ---------------------------
      (P ∖ a) ⟨ act a ⟩⇒ (P' ∖ a)

    Ren : ∀ {a} {φ : Renaming} {P P'} →
      P ⟨ act a ⟩⇒ P' →
      -------------------------------------
      (P [ φ ]) ⟨ act (φ $ a) ⟩⇒ (P' [ φ ])

  -- usual semantics of fixpoint
  infix 3 _⟨_⟩fix⇒_
  data _⟨_⟩fix⇒_ : CCS → Aτ → CCS → Set ℓ where
    Step : ∀ {α} {P P'}  →
      P ⟨ α ⟩⇒ P' →
      ------------------
      P ⟨ α ⟩fix⇒ P'

    Fix : ∀ {α} {P P'} →
      (P [ zero ↦ fix P ]) ⟨ α ⟩fix⇒ P' →
      -------------------------------------
      fix P ⟨ α ⟩fix⇒ P'

  -- alternative semantics of fixpoint
  infix 3 _⟨_⟩fix'⇒_
  data _⟨_⟩fix'⇒_ : CCS → Aτ → CCS → Set ℓ where
    Step' : ∀ {α} {P P'} →
      P ⟨ α ⟩⇒ P' →
      -------------------
      P ⟨ α ⟩fix'⇒ P'

    Fix' : ∀ {α} {P P'} →
      P ⟨ α ⟩fix'⇒ P' →
      -------------------------------------------
      fix P ⟨ α ⟩fix'⇒ (P' [ zero ↦  fix P ])

  open import Relation.Binary.PropositionalEquality hiding ([_])

  closed-subst : ∀ {n m} {n<m : n < m} {Q} (P : CCS) → closed m P → P ≡ P [ n ↦ Q ]
  closed-subst ∅ Pc = refl
  closed-subst {n} (# x) (var-closed x<n) with compare x n
  ... | less .x k = refl
  ... | equal .x = {!!}
  ... | greater .n k = {!!}
  closed-subst {n<m = n<m} (α ∙ P) (act-closed Pc)  = cong (_∙_ α) (closed-subst {n<m = n<m} P Pc)
  closed-subst {n<m = n<m} (P ＋ Q) (＋-closed Pc Qc) = cong₂ _＋_ (closed-subst {n<m = n<m} P Pc) (closed-subst {n<m = n<m} Q Qc)
  closed-subst {n<m = n<m} (P ∣ Q) (∣-closed Pc Qc) = cong₂ _∣_ (closed-subst {n<m = n<m} P Pc) (closed-subst {n<m = n<m} Q Qc)
  closed-subst {n<m = n<m} (P ∖ α) (res-closed Pc) = cong (λ h → h ∖ α) (closed-subst {n<m = n<m} P Pc)
  closed-subst {n<m = n<m} (P [ φ ]) (ren-closed Pc) = cong (λ h → h [ φ ]) (closed-subst {n<m = n<m} P Pc)
  closed-subst {n<m = n<m} (fix P) (fix-closed Pc) = cong fix (closed-subst {n<m = {!!}} P Pc)

  subst-idem : ∀ (P : CCS) {Q} {Qc : closed 0 Q} {n} →
    P [ n ↦ Q ] [ n ↦ Q ] ≡ P [ n ↦ Q ]
  subst-idem ∅ = refl
  subst-idem (# x) {Qc = Qc} {n = n} with compare x n
  ... | less .x k = {!!}
  ... | equal .x = {!!}
  ... | greater .n k = {!!}
  subst-idem (α ∙ P) {Qc = Qc} = cong (_∙_ α) (subst-idem P {Qc = Qc})
  subst-idem (P ＋ Q) {Qc = Qc} = cong₂ _＋_ (subst-idem P {Qc = Qc}) (subst-idem Q {Qc = Qc})
  subst-idem (P ∣ Q) {Qc = Qc} = cong₂ _∣_ (subst-idem P {Qc = Qc}) (subst-idem Q {Qc = Qc})
  subst-idem (P ∖ α) {Qc = Qc} = cong (λ h → h ∖ α) (subst-idem P {Qc = Qc})
  subst-idem (P [ φ ]) {Qc = Qc} = cong (λ h → h [ φ ]) (subst-idem P {Qc = Qc})
  subst-idem (fix P) {Qc = Qc} = cong fix (subst-idem P {Qc = Qc})

  step-subst : ∀ {Q} (P P' : CCS) {n} {α} →
    P [ n ↦ Q ] ⟨ α ⟩⇒ P' →
    P ⟨ α ⟩⇒ (P' [ n  ↦ Q ])
  step-subst (# n) P' d = {!!}
  step-subst (α ∙ P) P' d = {!!}
  step-subst (P ＋ P₁) P' d = {!!}
  step-subst (P ∣ P₁) P' d = {!!}
  step-subst (P ∖ α) P' d = {!!}
  step-subst (P [ φ ]) P' d = {!!}

  fix-equiv-to : ∀ {α} {P P'} →
    (P ⟨ α ⟩fix⇒ P') → (P ⟨ α ⟩fix'⇒ P')
  fix-equiv-to (Step x) = Step' x
  fix-equiv-to (Fix {P = ∅} (Step ()))
  fix-equiv-to (Fix {P = # zero} (Fix (Fix d))) = {!!}
  fix-equiv-to (Fix {P = # suc n} d) = {!!}
  fix-equiv-to (Fix {P = α ∙ P} d) = {!!}
  fix-equiv-to (Fix {P = P ＋ P₁} d) = {!!}
  fix-equiv-to (Fix {P = P ∣ P₁} d) = {!!}
  fix-equiv-to (Fix {P = P ∖ x} d) = {!!}
  fix-equiv-to (Fix {P = P [ x ]} d) = {!!}
  fix-equiv-to (Fix {P = fix P} d) = {!!}

  fix-equiv-from : ∀ {α} {P P'} {Γ} →
    (P ⟨ α ⟩fix'⇒ P') → (P ⟨ α ⟩fix⇒ P')
  fix-equiv-from (Step' x) = Step x
  fix-equiv-from (Fix' {P = ∅} (Step' ()))
  fix-equiv-from (Fix' {P = # x} (Step' d)) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = α Syntax.∙ P} (Step' d)) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = P ＋ P₁} d) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = P ∣ P₁} d) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = P ∖ x} d) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = P [ x ]} d) = Fix (Step {!!})
  fix-equiv-from (Fix' {P = fix P} d) = {!!}
