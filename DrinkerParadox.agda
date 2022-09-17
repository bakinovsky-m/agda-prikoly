{-# OPTIONS --safe #-}

open import Level
open import Axiom.ExcludedMiddle
open import Data.Product
open import Relation.Unary
open import Relation.Nullary
open import Data.Empty
open import Agda.Builtin.Sigma
open import Function.Base

module DrinkerParadox (em : ∀ {ℓ : Level} → ExcludedMiddle ℓ) where

ex-falso : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
ex-falso = λ ()

paradox : ∀ {ℓ : Level} {A : Set ℓ} {drinks : Pred A ℓ} →
  (e : A) →
  ∃[ x ] (drinks x -> ∀ {y : A} -> drinks y)
paradox {ℓ} {A} {drinks} e
  with em {P = Σ A (λ k → (¬ (drinks k)))}
... | yes (z , nz) = z , λ dz → ex-falso (nz dz)
... | no nnz = e , λ de {x} → case (em {P = drinks x})  of λ where
                                (yes dx) → dx
                                (no nx) → ex-falso (nnz (x , nx))
