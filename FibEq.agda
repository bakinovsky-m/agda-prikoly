{-# OPTIONS --safe #-}
module FibEq where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

module Preloaded where
    fibAux : ℕ -> ℕ -> ℕ -> ℕ
    fibAux a b 0 = a
    fibAux a b (suc n) = fibAux b (a + b) n
    fib2 : ℕ -> ℕ
    fib2 = fibAux 0 1

    fib : ℕ -> ℕ
    fib 0 = 0
    fib 1 = 1
    fib (suc (suc n)) = fib (suc n) + fib n

open Preloaded

fibAuxEq : (n m : ℕ) → fib (n + m) ≡ fibAux (fib n) (fib (suc n)) m
fibAuxEq n zero rewrite +-identityʳ n = refl
fibAuxEq n (suc m) =
  begin
    fib (n + suc m)
    ≡⟨ cong (λ x → fib x) (+-suc n m) ⟩
    fib (suc n + m)
    ≡⟨ fibAuxEq (suc n) m ⟩
    fibAux (fib (suc n)) (fib (suc (suc n))) m
    ≡⟨⟩
    fibAux (fib (suc n)) (fib (suc n) + fib n) m
    ≡⟨ cong (λ x → fibAux (fib (suc n)) x m) (+-comm (fib (suc n)) (fib n)) ⟩
    fibAux (fib (suc n)) (fib n + fib (suc n)) m
  ∎

fibAuxBase : (n : ℕ) → fib n ≡ fibAux 0 1 n
fibAuxBase n = fibAuxEq zero n

fibEq : (n : ℕ) -> fib2 n ≡ fib n
fibEq n =
  begin
    fib2 n
    ≡⟨⟩
    fibAux 0 1 n
    ≡⟨ sym (fibAuxBase n) ⟩
    fib n
  ∎
