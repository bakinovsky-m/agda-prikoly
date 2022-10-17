-- {-# OPTIONS --safe --show-implicit #-}
{-# OPTIONS --safe #-}

module VerifiedMax where

module Preloaded where

  open import Data.List
  open import Data.Integer
  
  list-max-ℤ : List ℤ → ℤ
  list-max-ℤ xs = foldr _⊔_ (+ 0) xs
open Preloaded

open import Data.Integer
open import Data.Integer.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Binary


lemma1 : ∀ {x} → (l : List ℤ) → x ∈ l → x ≤ list-max-ℤ l
lemma1 .(_ ∷ _) (here {x} {xs} px) rewrite px = i≤i⊔j x (list-max-ℤ xs)
lemma1 .(_ ∷ _) (there {y} {ys} x∈ys) = i≤j⇒i≤k⊔j y (lemma1 ys x∈ys)

lemma2 : (l : List ℤ) → let m = list-max-ℤ l in m ∈ l ⊎ m ≡ + 0
lemma2 [] = inj₂ refl
lemma2 l@(x ∷ xs) with lemma2 xs
lemma2 l@(x ∷ xs) | inj₁ m∈xs with <-cmp x (list-max-ℤ xs)
...  | tri< x<m _ _ rewrite i≤j⇒i⊔j≡j (<⇒≤ x<m) = inj₁ (there m∈xs)
...  | tri≈ _ x≡m _ rewrite x≡m | ⊔-idem (list-max-ℤ xs) = inj₁ (there m∈xs)
...  | tri> _ _ m<x rewrite ⊔-comm (x) (list-max-ℤ xs) = inj₁ (here (i≤j⇒i⊔j≡j (<⇒≤ m<x)))
lemma2 l@(x ∷ xs) | inj₂ m≡0 with <-cmp x (list-max-ℤ xs)
... | tri< x<m _ _ rewrite m≡0 = inj₂ (i≤j⇒i⊔j≡j (<⇒≤ x<m))
... | tri≈ _ x≡0 _ rewrite x≡0 | m≡0 = inj₂ refl
... | tri> _ _ m<x with <-cmp x 0ℤ
... | tri< x<0 ¬b ¬c rewrite m≡0 = inj₂ (i≤j⇒i⊔j≡j (<⇒≤ x<0))
... | tri≈ ¬a x≡0 ¬c rewrite m≡0 | x≡0 | ⊔-idem x = inj₂ refl
... | tri> ¬a ¬b 0<x rewrite m≡0 | ⊔-comm x +0 = inj₁ (here (i≤j⇒i⊔j≡j (<⇒≤ m<x)))

list-max-ℤ-spec : ∀ (l : List ℤ) → let m = list-max-ℤ l in
                    (∀ x → x ∈ l → x ≤ m) × (m ∈ l ⊎ m ≡ + 0)
proj₁ (list-max-ℤ-spec l) x x∈l = lemma1 l x∈l
proj₂ (list-max-ℤ-spec l) = lemma2 l
