{-# OPTIONS --safe #-}
module TrivialLang where

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Data.Nat.Properties
open import Data.List.Properties

module Preloaded where

    open import Data.Nat public
    open import Data.List public

    data Expr : Set where
        const : ℕ → Expr
        plus : Expr → Expr → Expr

    eval-expr : Expr → ℕ
    eval-expr (const n) = n
    eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

    eval-expr-tail' : Expr → ℕ → ℕ
    eval-expr-tail' (const n) acc = n + acc
    eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

    eval-expr-tail : Expr → ℕ
    eval-expr-tail e = eval-expr-tail' e 0

    eval-expr-cont' : {A : Set} → Expr → (ℕ → A) → A
    eval-expr-cont' (const n) k = k n
    eval-expr-cont' (plus e1 e2) k = eval-expr-cont' e2 λ n2 →
                                    eval-expr-cont' e1 λ n1 → k (n1 + n2)

    eval-expr-cont : Expr → ℕ
    eval-expr-cont e = eval-expr-cont' e (λ n → n)

    data Instr : Set where
        push : ℕ → Instr
        add : Instr

    Prog = List Instr

    Stack = List ℕ

    run : Prog → Stack → Stack
    run [] s = s
    run (push n ∷ p) s = run p (n ∷ s)
    run (add ∷ p) (a1 ∷ a2 ∷ s) = run p (a1 + a2 ∷ s)
    run (add ∷ p) s = run p s

    compile : Expr → Prog
    compile (const n) = push n ∷ []
    compile (plus e1 e2) = compile e1 ++ compile e2 ++ add ∷ []

-- -}

open Preloaded

-- Task 1 - 1. Prove that eval-expr-tail is equivalent to eval-expr.

eval-expr-tail-correct : ∀ e → eval-expr-tail e ≡ eval-expr e
eval-expr-tail-correct (const x) = +-identityʳ x
eval-expr-tail-correct (plus e1 e2) =
  begin
  eval-expr-tail (plus e1 e2)
  ≡⟨⟩
  eval-expr-tail' (plus e1 e2) 0
  ≡⟨⟩
  eval-expr-tail' e2 (eval-expr-tail' e1 0)
  ≡⟨ lemma e2 (eval-expr-tail' e1 zero) ⟩
  eval-expr-tail' e1 0 + eval-expr-tail' e2 0
  ≡⟨ cong (λ k → k + eval-expr-tail' e2 0) (eval-expr-tail-correct e1) ⟩
  eval-expr e1 + eval-expr-tail' e2 0
  ≡⟨ cong (λ k → eval-expr e1 + k) (eval-expr-tail-correct e2) ⟩
  eval-expr e1 + eval-expr e2
  ∎
  where
  lemma : ∀ e acc → eval-expr-tail' e acc ≡ acc + eval-expr-tail' e 0
  lemma (const x) acc rewrite +-identityʳ x | +-comm x acc = refl
  lemma (plus e1 e2) acc =
    begin
    eval-expr-tail' e2 (eval-expr-tail' e1 acc)
    ≡⟨ lemma e2 (eval-expr-tail' e1 acc) ⟩
    (eval-expr-tail' e1 acc) + eval-expr-tail' e2 0
    ≡⟨ cong (λ k → k + eval-expr-tail' e2 0) (lemma e1 acc) ⟩
    acc + eval-expr-tail' e1 0 + eval-expr-tail' e2 0
    ≡⟨ +-assoc acc (eval-expr-tail' e1 zero) (eval-expr-tail' e2 zero) ⟩
    acc + (eval-expr-tail' e1 0 + eval-expr-tail' e2 0)
    ≡⟨
    cong (acc +_) (
      begin
      eval-expr-tail' e1 0 + eval-expr-tail' e2 0
      ≡˘⟨ lemma e2 (eval-expr-tail' e1 zero) ⟩
      eval-expr-tail' e2 (eval-expr-tail' e1 0)
      ∎
    )
    ⟩
    acc + (eval-expr-tail' e2 (eval-expr-tail' e1 0))
    ≡⟨⟩
    acc + eval-expr-tail' e2 (eval-expr-tail' e1 0)
    ∎

-- Task 1 - 2. Prove that eval-expr-cont is equivalent to eval-expr.

eval-expr-cont-correct : ∀ e → eval-expr-cont e ≡ eval-expr e
eval-expr-cont-correct (const x) = refl
eval-expr-cont-correct (plus e1 e2) =
  begin
  eval-expr-cont (plus e1 e2)
  ≡⟨⟩
  eval-expr-cont' e2 (λ n2 → eval-expr-cont' e1 (λ n1 → (n1 + n2)))
  ≡⟨ lemma e2 (λ z → eval-expr-cont' e1 (λ z₁ → z₁ + z)) ⟩
  (λ n2 → eval-expr-cont' e1 (λ n1 → (n1 + n2))) (eval-expr-cont' e2 (λ n → n))
  ≡⟨ lemma e1 (λ z → z + eval-expr-cont' e2 (λ z₁ → z₁)) ⟩
  (λ n2 → (λ n1 → (n1 + n2)) (eval-expr-cont' e1 (λ n → n)) ) (eval-expr-cont' e2 (λ n → n))
  ≡⟨⟩
  eval-expr-cont' e1 (λ n → n) + eval-expr-cont' e2 (λ n → n)
  ≡⟨ cong (λ k → eval-expr-cont' e1 (λ n → n) + k) (eval-expr-cont-correct e2) ⟩
  eval-expr-cont' e1 (λ n → n) + eval-expr e2
  ≡⟨ cong (λ k → k + eval-expr e2) (eval-expr-cont-correct e1) ⟩
  eval-expr e1 + eval-expr e2
  ∎
  where
  lemma : ∀ e {A} → (accf : ℕ → A) → eval-expr-cont' e accf ≡ accf (eval-expr-cont' e (λ n → n))
  lemma (const x) accf = refl
  lemma (plus e e₁) accf =
    begin
    eval-expr-cont' e₁ (λ n2 → eval-expr-cont' e (λ n1 → accf (n1 + n2)))
      ≡⟨ lemma e₁          (λ n2 → eval-expr-cont' e (λ n1 → accf (n1 + n2))) ⟩
    (λ n2 → eval-expr-cont' e (λ n1 → accf (n1 + n2))) (eval-expr-cont' e₁ (λ n → n))
      ≡⟨ lemma e (λ z → accf (z + eval-expr-cont' e₁ (λ z₁ → z₁))) ⟩
    (λ n2 → (λ n1 → accf (n1 + n2)) (eval-expr-cont' e (λ n1 → n1))) (eval-expr-cont' e₁ (λ n → n))
      ≡⟨⟩
    (λ n2 → accf ( (λ n1 → n1 + n2) (eval-expr-cont' e (λ n → n)))) (eval-expr-cont' e₁ (λ n → n))
      ≡⟨⟩
    accf (eval-expr-cont' e (λ n → n) + eval-expr-cont' e₁ (λ n → n))
      ≡⟨⟩
    accf ((λ n1 → n1 + eval-expr-cont' e₁ (λ n → n)) (eval-expr-cont' e (λ n → n)))
      ≡˘⟨ cong accf (lemma e λ z → z + eval-expr-cont' e₁ (λ z₁ → z₁)) ⟩
    accf (eval-expr-cont' e (λ n1 → n1 + eval-expr-cont' e₁ (λ n → n)))
      ≡⟨⟩
    (λ n2 → accf (eval-expr-cont' e (λ n1 → n1 + n2))) (eval-expr-cont' e₁ (λ n → n))
      ≡⟨⟩
    accf ((λ n2 → eval-expr-cont' e (λ n1 → n1 + n2)) (eval-expr-cont' e₁ (λ n → n)))
      ≡˘⟨ cong accf (lemma e₁ (λ z → eval-expr-cont' e (λ z₁ → z₁ + z))) ⟩
    accf (eval-expr-cont' e₁ (λ n2 → eval-expr-cont' e (λ n1 → n1 + n2)))
    ∎

-- Task 2. Prove that you get the expected result when you compile and run the program.

compile-correct : ∀ e → run (compile e) [] ≡ eval-expr e ∷ []
compile-correct (const x) = refl
compile-correct (plus e1 e2)
  =
  begin
  run (compile e1 ++ compile e2 ++ add ∷ []) []
    ≡⟨ lemma e1 (compile e2 ++ add ∷ []) [] ⟩
  run (compile e2 ++ add ∷ []) (eval-expr e1 ∷ [])
    ≡⟨ lemma e2 (add ∷ []) (eval-expr e1 ∷ []) ⟩
  run (add ∷ []) (eval-expr e2 ∷ eval-expr e1 ∷ [])
    ≡⟨⟩
  run [] (eval-expr e2 + eval-expr e1 ∷ [])
    ≡⟨⟩
  eval-expr e2 + eval-expr e1 ∷ []
    ≡⟨ cong (_∷ []) (+-comm (eval-expr e2) (eval-expr e1)) ⟩
  eval-expr e1 + eval-expr e2 ∷ []
  ∎
  where
  4list-assoc : {A : Set} → {a b c d : List A} → (a ++ b ++ c) ++ d ≡ a ++ b ++ c ++ d
  4list-assoc {A} {a} {b} {c} {d} =
    begin
    (a ++ b ++ c) ++ d
    ≡⟨⟩
    (a ++ (b ++ c)) ++ d
    ≡⟨ ++-assoc a (b ++ c) d ⟩
    a ++ ((b ++ c) ++ d)
    ≡⟨ cong (a ++_) (++-assoc b c d) ⟩
    a ++ (b ++ (c ++ d))
    ∎
  lemma : ∀ e x l → run (compile e ++ x) l ≡ run x (eval-expr e ∷ l)
  lemma (const x₁) x l = refl
  lemma (plus e e₁) x l =
    begin
    run ((compile e ++ compile e₁ ++ add ∷ []) ++ x) l
      ≡⟨ cong (λ k → run k l) (4list-assoc {a = compile e} {b = compile e₁} {c = add ∷ []} {d = x}) ⟩
    run (compile e ++ compile e₁ ++ add ∷ [] ++ x) l
      ≡⟨ lemma e (compile e₁ ++ add ∷ x) l ⟩
    run (compile e₁ ++ add ∷ [] ++ x) (eval-expr e ∷ l)
      ≡⟨ lemma e₁ (add ∷ x) (eval-expr e ∷ l) ⟩
    run (add ∷ [] ++ x) (eval-expr e₁ ∷ eval-expr e ∷ l)
      ≡⟨⟩
    run x (eval-expr e₁ + eval-expr e ∷ l)
      ≡⟨ cong (λ k → run x (k ∷ l)) (+-comm (eval-expr e₁) (eval-expr e))  ⟩
    run x (eval-expr e + eval-expr e₁ ∷ l)
    ∎
