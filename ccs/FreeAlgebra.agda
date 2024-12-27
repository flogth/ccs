open import Action

open import Data.Vec
open import Data.Product
open import Data.Nat
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable

module FreeAlgebra {ℓ} (A : Set ℓ) {dec : DecidableEquality A} {Action : Act A dec} where
  open Act Action
  import Syntax
  open Syntax A {dec} {Action}
  open Action.Renaming A dec Action

  data Signature : Set ℓ where
    dead : Signature
    name : ℕ → Signature
    prefix : Aτ → Signature
    plus : Signature
    par : Signature
    restr : A → Signature
    ren : Renaming → Signature
    fix : Signature

  ar : Signature → ℕ
  ar dead = 0
  ar (name _) = 0
  ar (prefix _) = 1
  ar plus = 2
  ar par = 2
  ar (restr _) = 1
  ar (ren _) = 1
  ar fix = 1

  Sig : ∀ (X : Set ℓ) → Set ℓ
  Sig X = Σ Signature λ f → Vec X (ar f)

  data Σ* (X : Set ℓ) : Set ℓ where
    var : X → Σ* X
    app : (f : Signature) → Vec (Σ* X) (ar f) → Σ* X

  Σ*-alg : ∀ {X : Set ℓ} → Sig (Σ* X) → Σ* X
  Σ*-alg (f , args) = app f args

  lift : ∀ {B X : Set ℓ} (b : Sig B → B) (h : X → B) → Σ* X → B
  lift-vec : ∀ {B X : Set ℓ} (b : Sig B → B) (h : X → B) (f : Signature) → (args : Vec (Σ* X) (ar f)) → Vec B (ar f)
  lift b h (var x) = h x
  lift b h (app f x) = b (f , lift-vec b h f x)

  lift-vec b h dead args = []
  lift-vec b h (name x) args = []
  lift-vec b h (prefix α) (x ∷ args) = lift b h x ∷ []
  lift-vec b h plus (x ∷ y ∷ []) = lift b h x ∷ lift b h y ∷ []
  lift-vec b h par (x ∷ y ∷ []) = lift b h x ∷ lift b h y ∷ []
  lift-vec b h (restr α) (x ∷ args) = lift b h x ∷ []
  lift-vec b h (ren φ) (x ∷ args) = lift b h x ∷ []
  lift-vec b h fix (x ∷ args) = lift b h x ∷ []
