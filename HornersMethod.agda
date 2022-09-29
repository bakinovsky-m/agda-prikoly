{-# OPTIONS --safe #-}
module HornersMethod where
module Preloaded where

    open import Data.Nat
    open import Data.List

    eval-poly : ℕ → List ℕ → ℕ
    eval-poly x [] = 0
    eval-poly x (an ∷ cf) = eval-poly x cf + an * x ^ length cf

    horner-loop : ℕ → ℕ → List ℕ → ℕ
    horner-loop acc x [] = acc
    horner-loop acc x (an ∷ cf) = horner-loop (acc * x + an) x cf

    horner : ℕ → List ℕ → ℕ
    horner x cf = horner-loop 0 x cf

open Preloaded
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open Data.Nat.Solver.+-*-Solver
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

lemma1 : ∀ {acc1 acc2} {x} {cf} → horner-loop (acc1 + acc2) x cf ≡ acc1 * x ^ length cf + horner-loop acc2 x cf
lemma1 {zero} {acc2} {x} {cf} = refl
lemma1 {suc acc1} {acc2} {x} {[]} rewrite *-identityʳ acc1 = refl
lemma1 {suc acc1} {acc2} {x} {c ∷ cf} =
  begin
  horner-loop (x + (acc1 + acc2) * x + c) x cf
    ≡⟨ cong (λ k → horner-loop k x cf) (solve 4 (λ x acc1 acc2 c → x :+ (acc1 :+ acc2) :* x :+ c := x :+ acc1 :* x :+ (acc2 :* x :+ c)) refl x acc1 acc2 c) ⟩
  horner-loop (x + acc1 * x + (acc2 * x + c)) x cf
    ≡⟨ lemma1 {acc1 = (x + acc1 * x)} {acc2 = (acc2 * x + c)} {x} {cf} ⟩
  (x + acc1 * x) * x ^ length cf + horner-loop (acc2 * x + c) x cf
    ≡⟨
    cong (_+ horner-loop (acc2 * x + c) x cf) (solve 3 (λ x xl acc1 → (x :+ acc1 :* x) :* xl := x :* xl :+ acc1 :* (x :* xl)) refl x (x ^ length cf) acc1 )
    ⟩
  x * (x ^ length cf) + acc1 * (x * (x ^ length cf)) + horner-loop (acc2 * x + c) x cf
  ∎

horner-correct : ∀ x cf → eval-poly x cf ≡ horner x cf
horner-correct x [] = refl
horner-correct x (c ∷ []) = solve 2 (λ x' c' → c' :* con 1 := con 0 :* x' :+ c') refl x c
horner-correct x (c₁ ∷ c₂ ∷ cs) =
  begin
  eval-poly x cs + c₂ * (x ^ length cs) + c₁ * (x * (x ^ length cs))
  ≡⟨ solve 5 (λ ep c₁ c₂ x xl → ep :+ c₂ :* xl :+ c₁ :* (x :* xl) := (c₁ :* x) :* xl :+ (c₂ :* xl :+ ep)) refl (eval-poly x cs) c₁ c₂ x (x ^ length cs) ⟩
  (c₁ * x) * x ^ length cs + (c₂ * (x ^ length cs) + eval-poly x cs)
        ≡⟨
        cong ((c₁ * x) * x ^ length cs +_) (
          begin
          c₂ * (x ^ length cs) + eval-poly x cs
                ≡⟨ cong (c₂ * (x ^ length cs) +_) (horner-correct x cs) ⟩
          c₂ * (x ^ length cs) + horner-loop 0 x cs
                ≡⟨ sym (lemma1 {c₂} {0} {x} {cs}) ⟩
          horner-loop (c₂ + 0) x cs
                ≡⟨ cong (λ k → horner-loop k x cs) (+-identityʳ c₂) ⟩
          horner-loop c₂ x cs
          ∎
        )
        ⟩
  (c₁ * x) * x ^ length cs + horner-loop c₂ x cs
        ≡⟨ sym (lemma1 {c₁ * x} {c₂} {x} {cs} ) ⟩
  horner-loop (c₁ * x + c₂) x cs
        ≡⟨ cong (λ k → horner-loop ((k + c₁) * x + c₂) x cs) ( sym (*-zeroˡ x)) ⟩
  horner-loop ((0 * x + c₁) * x + c₂) x cs
  ∎
