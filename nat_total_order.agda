{-# OPTIONS -Wall #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Primitive using (lsuc; _⊔_)
open import Data.Bool using (true; false; Bool)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

record Poset (a : Set) : Set where
 infix 20 _≤_
 field
  _≤_ : a -> a -> Bool
  reflectivity : (x : a) -> x ≤ x ≡ true
  antisymmetry : (x y : a) -> (x ≤ y ≡ true) -> (y ≤ x ≡ true) -> x ≡ y
  transitivity : (x y z : a) -> (p1 : x ≤ y ≡ true) -> (p2 : y ≤ z ≡ true) -> x ≤ z ≡ true
open Poset {{...}} public

nat≤ : ℕ -> ℕ -> Bool
nat≤ zero x = true
nat≤ (suc x) zero = false
nat≤ (suc x) (suc y) = nat≤ x y

natrefl : (x : ℕ) -> nat≤ x x ≡ true
natrefl zero = refl
natrefl (suc x) = natrefl x

nattrans : (x y z : ℕ) -> (p1 : nat≤ x y ≡ true) -> (p2 : nat≤ y z ≡ true) -> nat≤ x z ≡ true
nattrans zero y z p1 p2 = refl
nattrans (suc x) (suc y) (suc z) p1 p2 = nattrans x y z p1 p2

natass : (x y : ℕ) -> (p1 : nat≤ x y ≡ true) -> (p2 : nat≤ y x ≡ true) -> x ≡ y 
natass zero zero p1 p2 = refl
natass (suc x) (suc y) p1 p2 = lemma x y (natass x y p1 p2)
 where
    lemma : (x y : ℕ) -> (p : x ≡ y) -> suc x ≡ suc y
    lemma zero zero p = refl
    lemma (suc x) (suc .x) refl = refl

instance
 PosetNat : Poset ℕ
 PosetNat = record {_≤_ = nat≤; reflectivity = natrefl; antisymmetry = natass; transitivity = nattrans}

record TotalOrder (A : Set) {{_ : Poset A}} : Set1 where
 field
  strongConnected : (x y : A) -> (x ≤ y ≡ true) ⊎ (y ≤ x ≡ true)

natStrong : (x y : ℕ) -> (x ≤ y ≡ true) ⊎ (y ≤ x ≡ true)
natStrong zero y = inj₁ refl
natStrong (suc x) zero = inj₂ refl
natStrong (suc x) (suc y) = natStrong x y 

instance
 TotalOrderNat : TotalOrder ℕ
 TotalOrderNat = record {strongConnected = natStrong}
