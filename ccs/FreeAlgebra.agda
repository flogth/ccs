open import Action

open import Data.Vec hiding ([_])
open import Data.Product
open import Data.Nat
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable
open import Effect.Functor

module FreeAlgebra {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  import Syntax
  open Syntax A {dec} {Action}
  open Action.Renaming A dec Action

  data Sig (X : Set ℓ) : Set ℓ where
    dead : Sig X
    name : ℕ → Sig X
    prefix : Aτ → X → Sig X
    plus : X → X → Sig X
    par : X → X → Sig X
    restr : A → X → Sig X
    ren : Renaming → X → Sig X
    fix : X → Sig X

  SigF : RawFunctor Sig
  (SigF RawFunctor.<$> f) dead = dead
  (SigF RawFunctor.<$> f) (name x) = name x
  (SigF RawFunctor.<$> f) (prefix α P) = prefix α (f P)
  (SigF RawFunctor.<$> f) (plus P Q) = plus (f P) (f Q)
  (SigF RawFunctor.<$> f) (par P Q) = par (f P) (f Q)
  (SigF RawFunctor.<$> f) (restr a P) = restr a (f P)
  (SigF RawFunctor.<$> f) (ren φ P) = ren φ (f P)
  (SigF RawFunctor.<$> f) (fix P) = fix (f P)

  data Σ* (X : Set ℓ) : Set ℓ where
    var : X → Σ* X
    app : Sig (Σ* X) → Σ* X

  Σ*F : RawFunctor Σ*
  (Σ*F RawFunctor.<$> f) x = go f x
    where open RawFunctor SigF
          go : ∀ {A B} → (A → B) → (Σ* A) → (Σ* B)
          go f (var x) = var (f x)
          go f (app dead) = app dead
          go f (app (name x)) = app (name x)
          go f (app (prefix α P)) = app (prefix α (go f P))
          go f (app (plus P Q)) = app (plus (go f P) (go f Q))
          go f (app (par P Q)) = app (par (go f P) (go f Q))
          go f (app (restr a P)) = app (restr a (go f P))
          go f (app (ren φ P)) = app (ren φ (go f P))
          go f (app (fix P)) = app (fix (go f P))

  Σ*-alg : ∀ {X : Set ℓ} → Sig (Σ* X) → Σ* X
  Σ*-alg x = app x

  lift : ∀ {B X : Set ℓ} (b : Sig B → B) (h : X → B) → Σ* X → B
  lift-sig : ∀ {B X : Set ℓ} (b : Sig B → B) (h : X → B) (x : Sig (Σ* X)) → Sig B
  lift b h (var x) = h x
  lift b h (app x) = b (lift-sig b h x)
  lift-sig b h dead = dead
  lift-sig b h (name x) = name x
  lift-sig b h (prefix α P) = prefix α (lift b h P)
  lift-sig b h (plus P Q) = plus (lift b h P) (lift b h Q)
  lift-sig b h (par P Q) = par (lift b h P) (lift b h Q)
  lift-sig b h (restr a P) = restr a (lift b h P)
  lift-sig b h (ren φ P) = ren φ (lift b h P)
  lift-sig b h (fix P) = fix (lift b h P)
