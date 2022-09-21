{-# OPTIONS --safe #-}
module MagicIsCommutative where

open import Relation.Binary.PropositionalEquality

record IsMagical {A : Set} (_∙_ : A → A → A) : Set where
  field
    left         : ∀ x y → (x ∙ y) ∙ y  ≡  x
    right        : ∀ x y → y ∙ (y ∙ x)  ≡  x

record IsCommuntative {A : Set} (_∙_ : A → A → A) : Set where
  field
    comm         : ∀ x y → x ∙ y  ≡ y ∙ x

open IsMagical
open IsCommuntative

magic-is-commutative : {A : Set} (_∙_ : A → A → A) → IsMagical _∙_ → IsCommuntative _∙_
magic-is-commutative {A} _∙_ record { left = left ; right = right } =
  record {comm = λ x y →
  let
  p1 = l1' {x} (erefl y)
  p2 = l2' p1
  p3 = l3' p2
  p4 = l4' p3
  p5 = l5' p4
  in
  p5
         }

         where
         ∙-injʳ : {x y z : A} (p : x ∙ z ≡ y ∙ z) → x ≡ y
         ∙-injʳ {x} {y} {z} p = elim (cong (_∙ z) p)
           where
           elim : {x y z : A} (p : ((x ∙ z) ∙ z) ≡ ((y ∙ z) ∙ z)) → x ≡ y
           elim {x} {y} {z} p with ((x ∙ z) ∙ z) | left x z | ((y ∙ z) ∙ z) | left y z
           ...                     | .x | refl | .y | refl = p
         ∙-injˡ : {x y z : A} (p : z ∙ x ≡ z ∙ y) → x ≡ y
         ∙-injˡ {x} {y} {z} p = elim (cong (z ∙_) p)
           where
           elim : {x y z : A} (p : (z ∙ (z ∙ x)) ≡ (z ∙ (z ∙ y))) → x ≡ y
           elim {x} {y} {z} p with (z ∙ (z ∙ x)) | right x z | (z ∙ (z ∙ y)) | right y z
           ...                     | .x | refl | .y | refl = p
         l1' : {x y : A} (p : y ≡ y) → (y ∙ (x ∙ y)) ∙ (x ∙ y) ≡ y
         l1' {x} {y} p = left y (x ∙ y)
         l2' : {x y : A} (p : (y ∙ (x ∙ y)) ∙ (x ∙ y) ≡ y) → (y ∙ (x ∙ y)) ∙ (x ∙ y) ≡ x ∙ (x ∙ y)
         l2' {x} {y} p rewrite right y x = p
         l3' : {x y : A} (p : (y ∙ (x ∙ y)) ∙ (x ∙ y) ≡ x ∙ (x ∙ y)) → y ∙ (x ∙ y) ≡ x
         l3' {x} {y} p = ∙-injʳ {z = x ∙ y} p
         l4' : {x y : A} (p : y ∙ (x ∙ y) ≡ x) → y ∙ (x ∙ y) ≡ y ∙ (y ∙ x)
         l4' {x} {y} p rewrite (right x y) = p
         l5' : {x y : A} (p : y ∙ (x ∙ y) ≡ y ∙ (y ∙ x)) → x ∙ y ≡ y ∙ x
         l5' {x} {y} p = ∙-injˡ {z = y} p
