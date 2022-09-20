{-# OPTIONS --safe #-}
module SumEq where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

module Preloaded where

    open import Data.Nat

    sumSimple : (ℕ → ℕ) → ℕ → ℕ
    sumSimple f zero = f zero
    sumSimple f (suc n) = f (suc n) + sumSimple f n

    sumAux : ℕ → (ℕ → ℕ) → ℕ → ℕ
    sumAux acc f zero = f zero + acc
    sumAux acc f (suc n) = sumAux (f (suc n) + acc) f n

    sumTail : (ℕ → ℕ) → ℕ → ℕ
    sumTail = sumAux zero

open Preloaded

lemma : (f : ℕ → ℕ) → (n acc1 acc2 : ℕ) → sumAux (acc1 + acc2) f n ≡ acc1 + sumAux acc2 f n
lemma f zero acc1 acc2 =
  begin
    f zero + (acc1 + acc2)
    ≡⟨ sym (+-assoc (f zero) acc1 acc2) ⟩
    f zero + acc1 + acc2
    ≡⟨ cong (λ k → k + acc2) (+-comm (f zero) acc1) ⟩
    acc1 + f zero + acc2
    ≡⟨ +-assoc acc1 (f zero) acc2 ⟩
    acc1 + (f zero + acc2)
  ∎
lemma f (suc n) acc1 acc2 =
  begin
    sumAux (f (suc n) + (acc1 + acc2)) f n
    ≡⟨ cong (λ k → sumAux (k) f n) (sym (+-assoc (f (suc n)) acc1 acc2)) ⟩
    sumAux (f (suc n) + acc1 + acc2) f n
    ≡⟨ cong (λ k → sumAux (k + acc2) f n) (+-comm (f (suc n)) acc1) ⟩
    sumAux (acc1 + f (suc n) + acc2) f n
    ≡⟨ cong (λ k → sumAux k f n) (+-assoc acc1 (f (suc n)) acc2) ⟩
    sumAux (acc1 + (f (suc n) + acc2)) f n
    ≡⟨ lemma f n acc1 (f (suc n) + acc2) ⟩
    acc1 + sumAux (f (suc n) + acc2) f n
  ∎

sumEq : (f : ℕ → ℕ) → (n : ℕ) → sumTail f n ≡ sumSimple f n
sumEq f zero rewrite +-identityʳ (f zero) = refl
sumEq f (suc n) rewrite lemma f n (f (suc n)) zero
 = (cong (f (suc n) +_) (sumEq f n))
