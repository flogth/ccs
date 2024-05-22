open import Action
open import Relation.Binary.Core using (Rel)

module Syntax {ℓ} (A : Set ℓ) (_≈_ : Rel A ℓ) {Action : Act A _≈_} where
  open Act Action
  open Action.Renaming A _≈_ Action
  open import Data.Nat public

  infix 6 _∣_
  infix 6 _＋_
  infix 5 _∙_

  data CCS : Set ℓ where
    ∅   : CCS
    `_  : ℕ → CCS
    _∙_ : Aτ → CCS → CCS
    _＋_ : CCS → CCS → CCS
    _∣_ : CCS → CCS → CCS
    _∖_ : CCS → A → CCS
    _[_] : CCS → Renaming → CCS
    fix : CCS → CCS

  -- de Bruijn machinery
  lift_by_above_ : CCS → ℕ → ℕ → CCS
  lift ∅ by n above i = ∅
  lift ` x by n above i with compare x i
  ... | less _ _ = ` x
  ... | equal _ = ` x
  ... | greater _ _ = ` (x + i)
  lift α ∙ P by n above i = α ∙ (lift P by n above i )
  lift P ＋ Q by n above i = (lift P by n above i) ＋ (lift Q by n above i)
  lift P ∣ Q by n above i = (lift P by n above i) ∣ (lift Q by n above i)
  lift P ∖ a by n above i = (lift P by n above i) ∖ a
  lift (P [ f ]) by n above i = (lift P by n above i) [ f ]
  lift fix P by n above i = fix (lift P by n above (suc i))

  _[_↦_] : CCS → ℕ → CCS → CCS
  ∅ [ n ↦ Q ] = ∅
  (` x) [ n ↦ R ] with compare x n
  ... | less _ _ = ` x
  ... | equal _ = lift R by x above zero
  ... | greater _ k = ` (n + k)
  (α ∙ P) [ n ↦ R ] = α ∙ (P [ n ↦ R ])
  (P ＋ Q) [ n ↦ R ] = (P [ n ↦ R ]) ＋ (Q [ n ↦ R ])
  (P ∣ Q) [ n ↦ R ] = (P [ n ↦ R ]) ∣ (Q [ n ↦ R ])
  (P ∖ a) [ n ↦ R ] = (P [ n ↦ R ]) ∖ a
  (P [ f ]) [ n ↦ R ] = (P [ n ↦ R ]) [ f ]
  fix P [ n ↦ R ] = fix (P [ n ↦ R ])
