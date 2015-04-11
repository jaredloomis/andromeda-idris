{-# OPTIONS --type-in-type #-}
module Front where

open import Agda.Primitive

open import Data.Unit
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Integer hiding (_⊔_)
open import Data.Float
open import Data.Char

open import Data.List
open import Data.Vec

open import Data.Product

open import Core

-----------
-- Types --
-----------

Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n

data Sampler : ℕ → Set where

data SamplerCube : Set where

data Scalar : Set → Set where
    void  : Scalar ⊤

    bool  : Scalar Bool
    int   : Scalar ℤ
    uint  : Scalar ℕ
    float : Scalar Float

----------
-- Type --
----------

mutual
  data Type : Set → Set where
      scalar : {A : Set} → Scalar A → Type A

      sampler     : (n : ℕ) → Type (Sampler n)
      samplerCube : Type SamplerCube

      _vec⟦_⟧    : {A : Set} →
          Scalar A → (n : ℕ) → Type (Vec A n)
      _mat⟦_⟧⟦_⟧ : {A : Set} →
          Scalar A → (n : ℕ) → (m : ℕ) → Type (Mat A n m)
      _array⟦_⟧  : {A : Set} →
          Type A → {- Expr ℕ -} ℕ → Type (List A)

      _××_ : {A B : Set} →
          Type A → Type B → Type (A × B)
      _~>_ : {A B : Set} →
          Type A → Type B → Type (A → B)

      -- Unneeded/Unused/Erased type
      □  : {A : Set} → Type A

----------
-- Expr --
----------

  data V : Set → Set where
      MkV : {A : Set} →
          Type A → Name → V A

  data Lit : Set → Set where
      LitFlt   : Float → Lit Float
      LitBool  : Bool  → Lit Bool
      LitInt   : ℤ     → Lit ℤ
      LitUInt  : ℕ     → Lit ℕ

      LitCode  : {A : Set} → Code → Lit A

      PreUnOp  : {A B   : Set} → Name → Lit (A → B)
      PostUnOp : {A B   : Set} → Name → Lit (A → B)
      BinOp    : {A B C : Set} → Name → Lit (A → B → C)

      Pair     : {A B : Set} → Lit (A → B → A × B)

  infixl 2 _∙$_
  data Expr : Set → Set where
      Var     : {A : Set} →
          Name → Expr A
--          V A → Expr A
      Literal : {A : Set} →
          Lit A → Expr A
--      Λ_ : {A B : Set} →
--          (Expr A → Expr B) → Expr (A → B)
      Λ_⇝_    : {A B : Set} →
          V A → Expr B → Expr (A → B)
      _∙$_    : {A B : Set} →
          Expr (A → B) → Expr A → Expr B
