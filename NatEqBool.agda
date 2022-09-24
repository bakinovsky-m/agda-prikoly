{-# OPTIONS --safe #-}
module NatEqBool where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty

bool : {a b c : Bool} → a ≡ b ⊎ b ≡ c ⊎ c ≡ a
bool {false} {false} {c} = inj₁ refl
bool {false} {true} {false} = inj₂ (inj₂ refl)
bool {false} {true} {true} = inj₂ (inj₁ refl)
bool {true} {false} {false} = inj₂ (inj₁ refl)
bool {true} {false} {true} = inj₂ (inj₂ refl)
bool {true} {true} {c} = inj₁ refl

nat : {a b c : ℕ} → (eq : ℕ ≡ Bool) → (a ≡ b ⊎ b ≡ c ⊎ c ≡ a)
nat eq rewrite eq = bool

noteq : (eq : ℕ ≡ Bool) → ⊥
noteq eq with nat {0} {1} {2} eq
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())

is-ℕ-Bool : ℕ ≡ Bool ⊎ ℕ ≢ Bool
is-ℕ-Bool = inj₂ (noteq)
