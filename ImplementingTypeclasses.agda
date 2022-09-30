{-# OPTIONS --safe #-}

module ImplementingTypeclasses where

open import Data.Char
open import Data.String hiding (length)
open import Data.List
open import Data.Integer as I
open import Data.Nat as N
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool as B
open import Relation.Nullary hiding (does)

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
 field
   eq : (x : A) → (y : A) → Bool

open Eq ⦃ ... ⦄ public

-- _===_ : A → A → Bool
_===_ : ∀ {ℓ} {A : Set ℓ} → ⦃ Eq A ⦄ → A → A → Bool
x === y = eq x y

-- _=/=_ : A → A → Bool
_=/=_ : ∀ {ℓ} {A : Set ℓ} → ⦃ Eq A ⦄ → A → A → Bool
x =/= y = not (eq x y) 

does : {P : Set} → Dec P → Bool
does (yes _) = true
does (no _)  = false

instance
 eqℤ : Eq ℤ
 eq ⦃ eqℤ ⦄ x y = does (x I.≟ y)
 eqℕ : Eq ℕ
 eq ⦃ eqℕ ⦄ x y = does (x N.≟ y)
 eqChar : Eq Char
 eq ⦃ eqChar ⦄ x y = does (x Data.Char.≟ y)
 eqBool : Eq Bool
 eq ⦃ eqBool ⦄ x y = does (x B.≟ y)
 eqString : Eq String
 eq ⦃ eqString ⦄ x y = does (x Data.String.≟ y)
 eqList : ∀ {a} {A : Set a} → ⦃ Eq A ⦄ → Eq (List A)
 eq ⦃ eqList ⦄ [] [] = true
 eq ⦃ eqList ⦄ (x ∷ xs) (y ∷ ys) = (eq x y) B.∧ (eq xs ys)
 eq ⦃ eqList ⦄ _ _ = false

module Test where
    open import Data.Bool using (true; false)
    open import Relation.Binary.PropositionalEquality

    _ : (1 === 1) ≡ true
    _ = refl

    _ : (1 =/= 1) ≡ false
    _ = refl

    _ : (1 === 2) ≡ false
    _ = refl

    _ : ((1 ∷ 2 ∷ []) === (1 ∷ 2 ∷ [])) ≡ true
    _ = refl

    _ : ((1 ∷ 2 ∷ []) === (1 ∷ 2 ∷ 3 ∷ [])) ≡ false
    _ = refl
