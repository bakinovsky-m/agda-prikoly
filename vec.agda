module vec where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

data ℕ : Set where
 zero : ℕ
 suc  : ℕ → ℕ
infixl 6 suc
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
_+_ zero a = a
_+_ (suc a) b = suc (a + b)
infixl 5 _+_


+assoc-proof : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+assoc-proof zero y z = refl
+assoc-proof (suc x) y z = cong suc (+assoc-proof x y z)

+zero-right : ∀ (a : ℕ) → a + zero ≡ a
+zero-right zero = refl
+zero-right (suc a) = cong suc (+zero-right a)

+1-is-suc : ∀(a : ℕ) → a + 1 ≡ suc a
+1-is-suc zero = refl
+1-is-suc (suc a) =
  begin
  suc a + 1   ≡⟨⟩
  suc (a + 1) ≡⟨ cong suc (+1-is-suc a) ⟩
  suc (suc a)
  ∎

a+sucb=suca+b : ∀(a b : ℕ) → a + suc b ≡ suc (a + b)
a+sucb=suca+b zero b = refl
a+sucb=suca+b (suc a) b = cong suc (a+sucb=suca+b a b)

+commutes : ∀(a b : ℕ) -> a + b ≡ b + a
+commutes a zero = +zero-right a
+commutes a (suc b) =
  begin
  a + suc b   ≡⟨ a+sucb=suca+b a b ⟩
  suc (a + b) ≡⟨ cong suc (+commutes a b) ⟩
  suc (b + a)
  ∎

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
infixr 5 _::_

data Fin : ℕ → Set where
 zero : {n : ℕ} -> Fin (suc n)
 suc  : {n : ℕ} (i : Fin n) -> Fin (suc n)

a : ℕ
a = suc (suc zero)

b : Fin a
b = (suc zero)
