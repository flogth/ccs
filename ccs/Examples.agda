open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable
open import Data.Fin using (zero ; suc)

import Action

module Examples where

  data A : Set where
    ina : A
    outa : A
    inb : A
    outb : A

  dec : DecidableEquality A
  dec ina ina = yes refl
  dec ina outa = no (λ ())
  dec ina inb = no (λ ())
  dec ina outb = no (λ ())
  dec outa ina = no (λ ())
  dec outa outa = yes refl
  dec outa inb = no (λ ())
  dec outa outb = no (λ ())
  dec inb ina = no (λ ())
  dec inb outa = no (λ ())
  dec inb inb = yes refl
  dec inb outb = no (λ ())
  dec outb ina = no (λ ())
  dec outb outa = no (λ ())
  dec outb inb = no (λ ())
  dec outb outb = yes refl

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

  open Action A dec

  actA : Act
  Act.comp actA = comp
  Act.compp actA = compp

  open Action.Act actA
  open import Syntax A {dec} {actA}
  open import Step A {dec} {actA}

  foo : Proc 0
  foo = fix ((act ina) ∙ ∅ ＋ (act outa) ∙ (# zero))

  foostepl : foo ⟨ act ina ⟩fix⇒ ∅
  foostepl = Fix (Step (Sumₗ Prefix))

  foostepr : foo ⟨ act outa ⟩fix⇒ foo
  foostepr = Fix (Step (Sumᵣ Prefix))


  bar : Proc 1
  bar = (act ina) ∙ (# zero) ∣ (act outa) ∙ ∅

  barstep : bar ⟨ τ ⟩fix⇒ (# zero) ∣ ∅
  barstep = Step (Sync Prefix Prefix)
