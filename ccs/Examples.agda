{-# OPTIONS --guardedness #-}
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable
open import Data.Fin using (zero ; suc)
open import Function.Bundles
open import Data.Nat
import Data.Fin
open import Data.Product
open import Data.List

import Action

module Examples where

  data A : Set where
    ina : A
    outa : A
    inb : A
    outb : A

  Ainj : Injection (setoid A) (setoid ℕ)
  Ainj .Injection.to ina = 0
  Ainj .Injection.to outa = 1
  Ainj .Injection.to inb = 2
  Ainj .Injection.to outb = 3
  Ainj .Injection.cong refl = refl
  Ainj .Injection.injective {ina} {ina} _ = refl
  Ainj .Injection.injective {outa} {outa} _ = refl
  Ainj .Injection.injective {inb} {inb} _ = refl
  Ainj .Injection.injective {outb} {outb} _ = refl

  _≈A_ : DecidableEquality A
  _≈A_ = via-injection Ainj _≟_

  comp : A → A
  comp ina = outa
  comp outa = ina
  comp inb = outb
  comp outb = inb

  compp : ∀ (a : A) → comp (comp a) ≡ a
  compp ina = refl
  compp outa = refl
  compp inb = refl
  compp outb = refl

  open Action A _≈A_

  actA : Act
  Act.comp actA = comp
  Act.compp actA = compp

  open Action.Act actA
  open import Syntax A {_≈A_} {actA}
  open import Step.Standard A {_≈A_} {actA}

  foo : Proc 0
  foo = fix ((act ina) ∙ ∅ ＋ (act outa) ∙ (# zero))

  foostepl : foo ⟨ act ina ⟩fix⇒ ∅
  foostepl = Fix (Sumₗ Prefix)

  foostepr : foo ⟨ act outa ⟩fix⇒ foo
  foostepr = Fix (Sumᵣ Prefix)

  bar : Proc 1
  bar = (act ina) ∙ (# zero) ∣ (act outa) ∙ ∅

  barstep : bar ⟨ τ ⟩fix⇒ (# zero) ∣ ∅
  barstep = Sync Prefix Prefix

  open import Semantics A {_≈A_} {actA}

  _ : γ (0 , (act ina) ∙ ((act inb) ∙ ∅)) ≡ ((λ x → 0 , {!!}) , (node (((act ina) , λ x → {!!}) ∷ [])))
  _ = {!!}

  _ : γ (0 , fix (fix ((act ina) ∙ (# suc zero)))) ≡ ({!!} , (node ({!!} ∷ {!!})))
  _ = {!!}
