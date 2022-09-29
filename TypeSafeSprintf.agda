{-# OPTIONS --safe #-}
module TypeSafeSprintf where

open import Data.Char
open import Data.Integer
-- open import Data.Integer renaming (show to showℤ)
open import Data.Integer.Show renaming (show to showℤ)
open import Data.Float renaming (show to showF)
open import Data.String
open import Data.List hiding (_++_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_)

data ValidFormat : Set₁ where
  lit : Char → ValidFormat
  var : (A : Set) → (f : A → String) → ValidFormat

data Format : Set₁ where
  valid : List ValidFormat → Format
  invalid : Format

parse : String → Format
parse s = parse' (toList s) []
  where
  parse' : List Char → List ValidFormat → Format
  parse' ('%' ∷ 'd' ∷ s) l = parse' s (var ℤ showℤ ∷ l)
  parse' ('%' ∷ 'f' ∷ s) l = parse' s (var Float showF ∷ l)
  parse' ('%' ∷ 'c' ∷ s) l = parse' s (var Char (λ c → fromList [ c ] ) ∷ l)
  parse' ('%' ∷ '%' ∷ s) l = parse' s (lit '%' ∷ l)
  parse' ('%' ∷ c ∷ s) l = invalid
  parse' (x ∷ xs) l = parse' xs (lit x ∷ l)
  parse' [] l = valid (reverse l)

Args : Format → Set
Args (valid []) = String
Args (valid (lit x ∷ xs)) = Args (valid xs)
Args (valid (var A f ∷ xs)) = A → Args (valid xs)
Args invalid = ⊥ → String

FormatArgs : String → Set
FormatArgs f = Args (parse f)

sprintf : (s : String) → FormatArgs s
sprintf s = sp "" (parse s)
  where
  sp : String → (f : Format) → Args f
  sp acc (valid []) = acc
  sp acc (valid (lit x ∷ xs)) = sp (acc ++ fromList [ x ]) (valid xs)
  sp acc (valid (var A f ∷ xs)) = λ qwe → sp (acc ++ f qwe) (valid xs)
  sp acc invalid = λ _ → ""

module Test where
  open import Relation.Binary.PropositionalEquality renaming (_≡_ to _`shouldBe`_)

  -- Should accept no arg when no fmt
  -- _ : sprintf "" `shouldBe` "
  _ : sprintf "" ≡ ""
  _ = refl

  -- -- Should format integers/char/float/%
  _ : sprintf "%d %f" -[1+ 3 ] 666.6 `shouldBe` "-4 666.6"
  _ = refl
  
  _ : sprintf "%d %f %c" -[1+ 3 ] 666.6 'q' `shouldBe` "-4 666.6 q"
  _ = refl
