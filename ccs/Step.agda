open import Action
open import Relation.Binary.Definitions using (DecidableEquality)
open import Level renaming (suc to lsuc)

module Step {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open import Syntax A {dec} {Action}

  record LTS (L : Set ℓ) : Set (lsuc ℓ) where
    field
      step : {n m : ℕ} → Proc n → L → Proc m → Set ℓ
