{-# OPTIONS --prop #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

open import Level using (Level; _⊔_; suc; 0ℓ)

private
 variable
  a b l : Level
  A : Set a
  B : Set b

REL : Set a -> Set b -> (l : Level) -> Set (a ⊔ b ⊔ suc l)
REL A B l = A → B → Set l

Rel : Set a → (l : Level) → Set (a ⊔ suc l)
Rel A l = REL A A l

data ℕ : Set where
 Z : ℕ
 S : ℕ → ℕ

data _≥_ : Rel ℕ 0ℓ where
 n≥z : {n : ℕ} → n ≥ Z
 s≥s : {m n : ℕ} → (m≥n : m ≥ n) → S m ≥ S n

_+_ : ℕ → ℕ → ℕ
_+_ Z a = a
_+_ (S a) b = S (a + b)

_*_ : ℕ → ℕ → ℕ
_*_ Z a = Z
_*_ (S a) b = b + (a * b)

Z*a=Z : (a : ℕ) → Z * a ≡ Z
Z*a=Z Z = refl
Z*a=Z (S a) = Z*a=Z a


a*Z=Z : (a : ℕ) → a * Z ≡ Z
a*Z=Z Z = refl
a*Z=Z (S a) = a*Z=Z a

-- data Bot : Prop where
-- record Top  : Prop where
--  constructor tt

-- _≥_ : ℕ → ℕ → Prop
-- S x ≥ S y = x ≥ y
-- Z ≥ S _ = Bot
-- _ ≥ Z = Top


-- mul-is-monotonic : {a b c : ℕ} -> a ≥ b -> (a * c) ≥ (b * c)
-- mul-is-monotonic {Z} {Z} {c} p = tt
-- mul-is-monotonic {S a} {Z} {Z} p rewrite a*Z=Z a = tt
-- mul-is-monotonic {S a} {Z} {S c} p rewrite Z*a=Z (S c)= tt
-- mul-is-monotonic {S a} {S b} {Z} p rewrite a*Z=Z (S a) rewrite a*Z=Z (S b)= tt
-- mul-is-monotonic {S a} {S b} {S c} p = mul-is-monotonic a b c p

-- mul-is-monotonic {a} {b} {Z} p rewrite a*Z=Z a rewrite a*Z=Z b = tt
-- mul-is-monotonic {a} {Z} {S c} p = {!!}
-- mul-is-monotonic {a} {S b} {S c} p = {!!}
-- mul-is-monotonic {a} {b} {S c} p = {!mul-is-monotonic a b c p!}

mul-is-monotonic : {a b c : ℕ} -> a ≥ b -> (a * c) ≥ (b * c)
mul-is-monotonic p = {!!}
