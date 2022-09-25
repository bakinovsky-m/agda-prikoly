{-# OPTIONS --safe #-}
module Iso-properties where
module Iso where

    open import Relation.Binary.PropositionalEquality public
    open import Data.Nat public

    record _⇔_ (A B : Set) : Set where
        constructor Bijection
        field
            A→B : A → B
            B→A : B → A
            A→B→A : ∀ (a : A) → B→A (A→B a) ≡ a
            B→A→B : ∀ (b : B) → A→B (B→A b) ≡ b
open Iso
open _⇔_

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Data.Nat.Properties

-- Task 0 : Example of _⇔_ in finite sets
-- Task 0-1. Find a bijection between Bool and Bit. (provided for you as an example)
data Bool : Set where
  true false : Bool
  
data Bit : Set where
  0b 1b : Bit

Bool→Bit : Bool → Bit
Bool→Bit false = 0b
Bool→Bit true = 1b

Bit→Bool : Bit → Bool
Bit→Bool 0b = false
Bit→Bool 1b = true

Bool→Bit→Bool : ∀ (b : Bool) → Bit→Bool (Bool→Bit b) ≡ b
Bool→Bit→Bool true = refl
Bool→Bit→Bool false = refl

Bit→Bool→Bit : ∀ (b : Bit) → Bool→Bit (Bit→Bool b) ≡ b
Bit→Bool→Bit 0b = refl
Bit→Bool→Bit 1b = refl

Bool⇔Bit : Bool ⇔ Bit
Bool⇔Bit = Bijection Bool→Bit Bit→Bool Bool→Bit→Bool Bit→Bool→Bit

--------------------------------------------------------------------
-- Task 1 : General properties of ⇔
-- Task 1-1. Prove that any set has the same cardinality as itself.
⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = Bijection (λ z → z) (λ z → z) (λ a → refl) (λ b → refl)

-- Task 1-2. Prove that _⇔_ relation is symmetric.
⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym (Bijection A→B B→A A→B→A B→A→B) = Bijection B→A A→B B→A→B A→B→A

-- Task 1-3. Prove that _⇔_ relation is transitive.
⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans (Bijection A→B B→A A→B→A B→A→B) (Bijection B→C C→B B→C→B C→B→C) = Bijection (λ z → B→C (A→B z)) (λ z → B→A (C→B z)) (λ a →
  begin
  B→A (C→B (B→C (A→B a)))
  ≡⟨ cong (λ k → B→A (k)) (B→C→B (A→B a)) ⟩
  B→A (A→B a)
  ≡⟨ A→B→A a ⟩
  a
  ∎
  )
  (λ b →
  begin
  B→C (A→B (B→A (C→B b)))
  ≡⟨ cong (λ k → B→C k) (B→A→B (C→B b)) ⟩
  B→C (C→B b)
  ≡⟨ C→B→C b ⟩
  b
  ∎
  )

-- Task 1-4. Prove the following statement:
--   Given two functions A→B and B→A, if A→B→A is satisfied and B→A is injective, A ⇔ B.
bijection-alt :
  ∀ {A B : Set} →
  (A→B : A → B) →
  (B→A : B → A) →
  (∀ a → B→A (A→B a) ≡ a) →
  (∀ b b' → B→A b ≡ B→A b' → b ≡ b') →
  A ⇔ B
bijection-alt A→B B→A A→B→A B→A-inj = Bijection A→B B→A A→B→A
                                        (λ b → B→A-inj (A→B (B→A b)) b (A→B→A (B→A b)))

--------------------------------------------------------------------
-- Task 2 : ⇔-relations between ℕ and various supersets of ℕ

-- ℕ+1 : A set having one more element than ℕ.
-- {- Preloaded code
data ℕ+1 : Set where
  null : ℕ+1
  nat : ℕ → ℕ+1
-- -}

-- Task 2-1. Prove that ℕ has the same cardinality as ℕ+1.
ℕ⇔ℕ+1 : ℕ ⇔ ℕ+1
ℕ⇔ℕ+1 = record {
  A→B = λ {
    zero → null;
    (suc n) → nat n
    };
  B→A = λ {
    null → zero;
    (nat (zero)) → 1;
    (nat (suc x)) → suc (suc x)
    };
  A→B→A = λ {
    zero → refl;
    (suc zero) → refl;
    (suc (suc n)) → refl
    };
  B→A→B =
  λ {
    null → refl;
    (nat zero) → refl;
    (nat (suc zero)) → refl;
    (nat (suc (suc x))) → refl
    }
  }

-- ℕ+ℕ : A set having size(ℕ) more elements than ℕ.
-- {- Preloaded code
data ℕ+ℕ : Set where
  left : ℕ → ℕ+ℕ
  right : ℕ → ℕ+ℕ
-- -}

data isEven : ℕ → Set where
  Z-is-even : isEven zero
  SS-is-even : {n : ℕ} → isEven n → isEven (suc (suc n))
data isOdd : ℕ → Set where
  SZ-is-odd : isOdd 1
  SS-is-odd : {n : ℕ} → isOdd n → isOdd (suc (suc n))

if_then_else : ∀{ℓ}{A : Set ℓ} → Bool → A → A → A 
if_then_else true x _ = x
if_then_else false _ y = y

even : (n : ℕ) → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

even-is-isEven : {n : ℕ} → (p : even n ≡ true) → isEven n
even-is-isEven {zero} p = Z-is-even
even-is-isEven {suc (suc n)} p = SS-is-even (even-is-isEven p)

not-even-is-isOdd : {n : ℕ} → (p : even n ≡ false) → isOdd n
not-even-is-isOdd {suc zero} p = SZ-is-odd
not-even-is-isOdd {suc (suc n)} p = SS-is-odd (not-even-is-isOdd p)

even-to-isSmth : (n : ℕ) → Set
even-to-isSmth n = if (even n) then (isEven n) else (isOdd n)

double-is-even : {n : ℕ} → even (n + n) ≡ true
double-is-even {zero} = refl
double-is-even {suc n} =
  begin
  even (suc (n + suc n))
  ≡⟨ cong (λ x → even (suc x) ) (+-comm n (suc n)) ⟩
  even (suc (suc n + n))
  ≡⟨ double-is-even {n} ⟩
  true
  ∎

n+sucm≡sucn+m : {n m : ℕ} → n + suc m ≡ suc n + m
n+sucm≡sucn+m {zero} {m} = refl
n+sucm≡sucn+m {suc n} {m} = cong suc n+sucm≡sucn+m

suc-double-is-not-even : {n : ℕ} → even (n + suc n) ≡ false
suc-double-is-not-even {zero} = refl
suc-double-is-not-even {suc n} =
  begin
    even (suc n + suc (suc n))
    ≡⟨ lemma1 {n} ⟩
    even (n + suc n)
    ≡⟨ suc-double-is-not-even {n} ⟩
    false
  ∎
  where
  lemma1 : {n m : ℕ} → even (suc n + suc m) ≡ even (n + m)
  lemma1 {zero} {m} = refl
  lemma1 {suc n} {m} =
    begin
      even (n + suc m)
      ≡⟨ cong (λ k → even k) (n+sucm≡sucn+m {n} {m}) ⟩
      even (suc n + m)
    ∎

-- Task 2-2. Prove that ℕ has the same cardinality as ℕ+ℕ.
b→a : ℕ+ℕ → ℕ
b→a (left x) = x + x
b→a (right x) = suc (x + x)
left-case : {n : ℕ} → (p : isEven n) → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
left-case {zero} p = refl
left-case {suc .(suc n)} (SS-is-even {n} p) = cong suc (
    begin
    ⌊ n /2⌋ + suc ⌊ n /2⌋
    ≡⟨ n+sucm≡sucn+m ⟩
    suc ⌊ n /2⌋ + ⌊ n /2⌋
    ≡⟨
    cong suc (
    begin
    ⌊ n /2⌋ + ⌊ n /2⌋
    ≡⟨ left-case p ⟩
    n
    ∎
    )
    ⟩
    suc n
    ∎
    )
right-case : {n : ℕ} → (p : isOdd (suc n)) → suc (⌊ n /2⌋ + ⌊ n /2⌋) ≡ suc n
right-case {zero} p = refl
right-case {suc n} (SS-is-odd p) = cong suc (left-case (suceven-is-odd p))
    where
    suceven-is-odd : {n : ℕ} → (p : isOdd n) → isEven (suc n)
    suceven-is-odd {suc .0} SZ-is-odd = SS-is-even Z-is-even
    suceven-is-odd {suc .(suc _)} (SS-is-odd p) = SS-is-even (suceven-is-odd p)
lemma : {x : ℕ} → b→a (if (even (suc x)) then (left ⌊ suc x /2⌋) else (right ⌊ x /2⌋)) ≡ suc x
lemma {x} with even (suc x) | inspect even (suc x)
...       | true | [ q ] = let p = even-is-isEven {suc x} q in left-case p
...       | false | [ q ] = let p = not-even-is-isOdd {suc x} q in right-case p

ℕ⇔ℕ+ℕ : ℕ ⇔ ℕ+ℕ
ℕ⇔ℕ+ℕ = record {
  A→B = λ {
    zero → left 0;
    (suc x) → if (even (suc x)) then (left ⌊ suc x /2⌋) else (right ⌊ x /2⌋)
  };
  B→A = b→a;
  A→B→A = λ {
    zero → refl;
    (suc x) → lemma
  };
  B→A→B = λ {
    (left zero) → refl;
    (left (suc n)) →
      begin
      if even (suc n + suc n) then left ⌊ suc (n + suc n) /2⌋
                                else (right ⌊ n + suc n /2⌋)
      ≡⟨ cong (λ k → if k then left ⌊ suc (n + suc n) /2⌋ else (right ⌊ n + suc n /2⌋)) (double-is-even {suc n}) ⟩
      if true then left ⌊ suc (n + suc n) /2⌋ else (right ⌊ n + suc n /2⌋)
      ≡⟨⟩
      left ⌊ suc (n + suc n) /2⌋
      ≡⟨ cong (λ k → left k) lemma1 ⟩
      left (suc n)
      ∎;
    (right zero) → refl;
    (right (suc n)) →
      begin
      if even (n + suc n) then left (suc ⌊ n + suc n /2⌋) else (right ⌊ suc (n + suc n) /2⌋)
      ≡⟨ cong (λ k → if k then left (suc ⌊ n + suc n /2⌋) else (right ⌊ suc (n + suc n) /2⌋)) (suc-double-is-not-even {n}) ⟩
      if false then left (suc ⌊ n + suc n /2⌋) else (right ⌊ suc (n + suc n) /2⌋)
      ≡⟨⟩
      right ⌊ suc (n + suc n) /2⌋
      ≡⟨ cong (λ k → right k)
        (
          begin
          ⌊ suc (n + suc n) /2⌋
          ≡⟨ cong (λ k → ⌊ k /2⌋) (n+sucm≡sucn+m {suc n}) ⟩
          ⌊ suc (suc n + n) /2⌋
          ≡⟨⟩
          ⌊ suc (suc (n + n)) /2⌋
          ≡⟨⟩
          suc ⌊ n + n /2⌋
          ≡⟨ cong suc lemma1 ⟩
          suc n
          ∎
        )
      ⟩
      right (suc n)
      ∎
    }
  }
  where
  lemma1 : {n : ℕ} → ⌊ n + n /2⌋ ≡ n
  lemma1 {zero} = refl
  lemma1 {suc n} =
    begin
    ⌊ suc (n + suc n) /2⌋
    ≡⟨ cong (λ k → ⌊ suc k /2⌋) (+-comm n (suc n)) ⟩
    suc ⌊ (n + n) /2⌋
    ≡⟨ cong suc lemma1 ⟩
    suc n
    ∎
