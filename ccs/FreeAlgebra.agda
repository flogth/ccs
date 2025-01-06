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

  SigF : RawFunctor Sig
  (SigF RawFunctor.<$> f) (s , args) = s , Data.Vec.map f args

  -- ι : Sig (∀ {n} → Proc n) → ∀ {n} → Proc n
  -- ι (dead , _) = ∅
  -- ι (name x , _) = # {!!}
  -- ι (prefix α , P ∷ []) = α ∙ P
  -- ι (plus , P ∷ Q ∷ []) = P ＋ Q
  -- ι (par , P ∷ Q ∷ []) = P ∣ Q
  -- ι (restr β , P ∷ []) = P ∖ β
  -- ι (ren φ , P ∷ []) = P [ φ ]
  -- ι (fix , P ∷ []) = fix P

  data Σ* (X : Set ℓ) : Set ℓ where
    var : X → Σ* X
    app : (f : Signature) → Vec (Σ* X) (ar f) → Σ* X

  Σ*F : RawFunctor Σ*
  (Σ*F RawFunctor.<$> f) x = go f x
    where go : ∀ {A B} → (A → B) → (Σ* A) → (Σ* B)
          go f (var x) = var (f x)
          go f (app dead []) = app dead []
          go f (app (name x) []) = app (name x) []
          go f (app (prefix α) (P ∷ [])) = app (prefix α) (go f P ∷ [])
          go f (app plus (P ∷ Q ∷ [])) = app plus (go f P ∷ go f Q ∷ [])
          go f (app par (P ∷ Q ∷ [])) = app par (go f P ∷ go f Q ∷ [])
          go f (app (restr β) (P ∷ [])) = app (restr β) (go f P ∷ [])
          go f (app (ren φ) (P ∷ [])) = app (ren φ) (go f P ∷ [])
          go f (app fix (P ∷ [])) = app fix (go f P ∷ [])

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
