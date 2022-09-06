--https://www.codewars.com/kata/5c8b332197eb04000887fd63
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; step-≡; _∎; _≡⟨⟩_)
open import Data.Nat.Base
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-assoc)
open import Data.Nat.Solver
open Data.Nat.Solver.+-*-Solver

arith-sum : ℕ → ℕ
arith-sum zero = zero
arith-sum n'@(suc n) = n' + arith-sum n

arith-formula : ℕ → ℕ
arith-formula n = ⌊ n * (n + 1) /2⌋

n+1=suc_n : {n : ℕ} → n + 1 ≡ suc n
n+1=suc_n {zero} = refl
n+1=suc_n {suc n} = cong suc ( n+1=suc_n {n})

l2 : {n m : ℕ} → n * (m + 1) ≡ (n * m) + n
l2 {zero} {m} = refl
l2 {suc n} {m} =
  begin
  m + 1 + n * (m + 1)
  ≡⟨ cong (λ x → m + 1 + x) (l2 {n} {m}) ⟩
  m + 1 + (n * m + n)
  ≡⟨ +-comm (m + 1) (n * m + n) ⟩
  (n * m + n) + (m + 1)
  ≡⟨ refl ⟩
  n * m + n + (m + 1)
  ≡⟨ +-assoc (n * m) n (m + 1) ⟩
  n * m + (n + (m + 1))
  ≡⟨ cong (λ x → n * m + x) (sym (+-assoc n m 1)) ⟩
  n * m + (n + m + 1)
  ≡⟨ cong (λ x → n * m + (x + 1)) (+-comm n m) ⟩
  n * m + (m + n + 1)
  ≡⟨ cong (λ x → x) (sym (+-assoc (n * m) (m + n) 1)) ⟩
  n * m + (m + n) + 1
  ≡⟨ cong (λ x → x + 1) (sym (+-assoc (n * m) m n)) ⟩
  n * m + m + n + 1
  ≡⟨ cong (λ x →  x + n + 1) (sym (+-comm m (n * m))) ⟩
  m + n * m + n + 1
  ≡⟨ +-assoc (m + n * m) n 1 ⟩
  m + n * m + (n + 1)
  ≡⟨ cong (λ x → m + n * m + x) (n+1=suc_n {n}) ⟩
  m + n * m + suc n
  ∎
  where
    lemma3 : {a b c d : ℕ} → a + b + c + d ≡ a + (b + c) + d
    lemma3 {a} {b} {c} {d} =  cong (λ x →  x + d) (+-assoc  a  b  c)

arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq zero = refl
arith-eq (suc zero) = refl
arith-eq n'@(suc n) = --{!!}
  begin
  arith-formula (suc n)
    ≡⟨ refl ⟩
  ⌊ suc n * (suc n + 1) /2⌋
    ≡⟨ cong (λ x → ⌊ suc n * x /2⌋) n+1=suc_n ⟩
  ⌊ suc n * (suc (suc n)) /2⌋
    ≡⟨ cong (λ x → ⌊ x /2⌋) (lemma1 {suc n}) ⟩
  ⌊ suc n + suc n * suc n /2⌋
    ≡⟨ cong (λ x → ⌊ suc n + x /2⌋ ) (lemma2 {n}) ⟩
  ⌊ suc n + suc (n * n + 2 * n) /2⌋
    ≡⟨ cong (λ x → ⌊ x /2⌋) (lemma3) ⟩
  ⌊ suc ( suc (n + (n * n + 2 * n))) /2⌋
    ≡⟨ refl ⟩
  suc ⌊ n + (n * n + 2 * n) /2⌋
    ≡⟨
    cong suc (
    begin
    ⌊ n + (n * n + 2 * n) /2⌋
      ≡⟨ cong (λ x → ⌊ x /2⌋) (sym (+-assoc n (n * n) (n + (n + zero)))) ⟩
    ⌊ n + n * n + 2 * n /2⌋
      ≡⟨ cong (λ x → ⌊ x /2⌋) (solve 1 (λ n → n :+ n :* n :+ con 2 :* n := con 2 :* n :+ (n :+ n :* n)) refl n) ⟩
    ⌊ 2 * n + (n + n * n) /2⌋
      ≡⟨ lemma5 {n} ⟩
    n + ⌊ (n + n * n) /2⌋
      ≡⟨
        cong (n +_) (
        begin
        ⌊ n + n * n /2⌋
        ≡⟨ lemma6 {n} ⟩
        arith-sum n
        ∎
        )
      ⟩
    n + arith-sum n
    ∎
    )
    ⟩
  suc n + arith-sum n
  ∎
  where

  lemma1 : {a b : ℕ} → a * (suc b) ≡ a + a * b
  lemma1 {zero} {b} = refl
  lemma1 {suc a} {b} = cong suc (
    begin
    b + a * suc b
    ≡⟨ cong (λ x → b + a * x) (sym n+1=suc_n) ⟩
    b + a * (b + 1)
    ≡⟨ cong (λ x → b + x) (l2 {a} {b}) ⟩
    b + (a * b + a)
    ≡⟨ cong (λ x → b + x) (+-comm (a * b) a) ⟩
    b + (a + (a * b))
    ≡⟨ sym (+-assoc b a (a * b)) ⟩
    (b + a) + (a * b)
    ≡⟨ cong (λ x → x + a * b) (+-comm b a) ⟩
    a + b + a * b
    ≡⟨ +-assoc a b (a * b) ⟩
    a + (b + a * b)
    ∎
    )
  lemma2 : {n : ℕ} → suc n * suc n ≡ suc (n * n + 2 * n)
  lemma2 {zero} = refl
  lemma2 {suc n}
    rewrite +-assoc n (n * suc n) (suc (n + suc (n + zero))) =
    cong suc (cong suc (
    cong (n +_) (
    begin
    suc (suc (n + n * suc (suc n)))
    ≡⟨ cong (λ x → suc (suc (n + x))) (lemma1 {n}) ⟩
    suc (suc (n + (n + n * suc n)))
    ≡⟨ cong (λ x → suc (suc (n + (n + n * x)))) ll2 ⟩
    suc (suc (n + (n + n * (n + 1))))
    ≡⟨ cong (λ x → suc (suc (n + (n + (x))))) (l2 {n}) ⟩
    suc (suc (n + (n + (n * n + n))))
    ≡⟨ refl ⟩
    suc (suc n + (n + (n * n + n)))
    ≡⟨ refl ⟩
    suc (suc n) + (n + (n * n + n))
    ≡⟨ cong (λ x → suc x + (n + (n * n + n))) (ll2 {n}) ⟩
    suc (n + 1 + (n + (n * n + n)))
    ≡⟨ cong (λ x → x + 1 + (n + (n * n + n))) (ll2 {n}) ⟩
    n + 1 + 1 + (n + (n * n + n))
    ≡⟨ solve 1 (λ n → n :+ con 1 :+ con 1 :+ (n :+ (n :* n :+ n))
                      := (n :+ n :* n) :+ (n :+ con 1 :+ (n :+ con 1))) refl n ⟩
    (n + n * n) + (n + 1 + (n + 1))
    ≡⟨ cong (λ x → (n + n * n) + (n + 1 + x)) (sym (ll2 {n})) ⟩
    (n + n * n) + (n + 1 + suc n)
    ≡⟨ cong (λ x → (n + n * n) + (x + suc n)) (sym (ll2 {n})) ⟩
    (n + n * n) + (suc n + suc n)
    ≡⟨ refl ⟩
    (n + n * n) + suc (n + suc n)
    ≡⟨  cong (λ x → x + suc (n + suc n)) (sym (lemma1 {n})) ⟩
    n * suc n + suc (n + suc n)
    ≡⟨ cong (λ x → n * suc n + suc (n + suc x) ) (sym ll1) ⟩
    n * suc n + suc (n + suc (n + zero))
    ∎
    )
    )
    )
    where
      ll1 : {n' : ℕ} → n' + zero ≡ n'
      ll1 {zero} = refl
      ll1 {suc n'} = cong suc (ll1 {n'})
      ll2 : {a : ℕ} → suc a ≡ a + 1
      ll2 {zero} = refl
      ll2 {suc a} = cong suc ll2
  lemma3 : {n m : ℕ} → suc n + suc m ≡ suc (suc (n + m))
  lemma3 {zero} {m} = refl
  lemma3 {suc n} {m} = cong suc ( cong suc n+suc_m≡suc_n+m)
    where
    n+suc_m≡suc_n+m : {n m : ℕ} →  n + suc m ≡ suc (n + m)
    n+suc_m≡suc_n+m {zero} {m} = refl
    n+suc_m≡suc_n+m {suc n} {m} = cong suc n+suc_m≡suc_n+m

  n+n=2*n : ∀ {n} → n + n ≡ 2 * n
  n+n=2*n {zero} = refl
  n+n=2*n {suc n} rewrite (+-identityʳ n) = cong suc refl

  lemma4 : {n : ℕ} → ⌊ 2 * n /2⌋ ≡ n
  lemma4 {zero} = refl
  lemma4 {suc n} = --{!!}
    begin
    ⌊ suc (n + suc (n + zero)) /2⌋
    ≡⟨ cong (λ x → ⌊ suc n + suc x /2⌋) (+-identityʳ n ) ⟩
    ⌊ suc (n + suc n) /2⌋
    ≡⟨ cong (λ x → ⌊ x /2⌋) lemma3 ⟩
    ⌊ suc ( suc (n + n)) /2⌋
    ≡⟨ refl ⟩
    suc ⌊ n + n /2⌋
    ≡⟨
      cong suc (
        begin
        ⌊ n + n /2⌋
        ≡⟨ cong (λ x → ⌊ x /2⌋) (n+n=2*n {n}) ⟩
        ⌊ 2 * n /2⌋
        ≡⟨ lemma4 ⟩
        n
        ∎
      )
    ⟩
    suc n
    ∎
  lemma5 : {n m : ℕ} → ⌊ 2 * n + m /2⌋ ≡ n + ⌊ m /2⌋
  lemma5 {zero} {m} = refl
  lemma5 {suc n} {m} rewrite (+-identityʳ n) =
    begin
    ⌊ suc (n + suc n + m) /2⌋
    ≡⟨ refl ⟩
    ⌊ suc (n + suc n) + m /2⌋
    ≡⟨ cong (λ x → ⌊ x + m /2⌋) lemma3 ⟩
    ⌊ suc (suc (n + n)) + m /2⌋
    ≡⟨ refl ⟩
    suc ⌊ (n + n) + m /2⌋
    ≡⟨
      cong suc (
      begin
      ⌊ n + n + m /2⌋
      ≡⟨ cong (λ x → ⌊ x + m /2⌋ ) (n+n=2*n {n} )⟩
      ⌊ 2 * n + m /2⌋
      ≡⟨ lemma5 {n} {m} ⟩
      n + ⌊ m /2⌋
      ∎
      )
    ⟩
    suc (n + ⌊ m /2⌋)
    ∎

  lemma6 : {n : ℕ} → ⌊ n + n * n /2⌋ ≡ arith-sum n
  lemma6 {zero} = refl
  lemma6 {suc n} =
    begin
    ⌊ suc (n + suc (n + n * suc n)) /2⌋
    ≡⟨ cong (λ x → ⌊ x /2⌋ ) (lemma3 {n}) ⟩
    ⌊ suc ( suc (n + (n + n * suc n))) /2⌋
    ≡⟨ refl ⟩
    suc ⌊ n + (n + n * suc n) /2⌋
    ≡⟨
      cong suc (
      begin
      ⌊ n + (n + n * suc n) /2⌋
      ≡⟨ cong (λ x → ⌊ n + (n + n * x) /2⌋) (sym (n+1=suc_n)) ⟩
      ⌊ n + (n + n * (n + 1)) /2⌋
      ≡⟨ cong (λ x → ⌊ x /2⌋)
        (solve 1 (λ n →
          n :+ (n :+ n :* (n :+ con 1)) :=
          con 2 :* n :+ n :* (n :+ con 1)
         )
         refl n) ⟩
      ⌊ 2 * n + n * (n + 1) /2⌋
      ≡⟨ lemma5 {n} ⟩
      n + ⌊ n * (n + 1) /2⌋
      ≡⟨
      cong (n +_) (
        begin
        ⌊ n * (n + 1) /2⌋
        ≡⟨ cong (λ x → ⌊ x /2⌋ ) (l2 {n}) ⟩
        ⌊ n * n + n /2⌋
        ≡⟨ cong (λ x → ⌊ x /2⌋) (+-comm (n * n) n) ⟩
        ⌊ n + n * n /2⌋
        ≡⟨ lemma6 {n} ⟩
        arith-sum n
        ∎
      )
      ⟩
      n + arith-sum n
      ∎
      )
    ⟩
    suc (n + arith-sum n)
    ∎
