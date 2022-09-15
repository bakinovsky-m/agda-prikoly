Rel : Set → Set₁
Rel A = A -> A -> Set

Op : Set → Set
Op A = A → A → A

Reflective : {A : Set} → Rel A → Set
Reflective {A} rel = {a : A} → rel a a

Symmetric : {A : Set} → Rel A → Set
Symmetric {A} rel  = {a b : A} → rel a b → rel b a

Transitive : {A : Set} -> Rel A -> Set
Transitive {A} rel = {a b c : A} → rel a b → rel b c → rel a c

Associative : {A : Set} → Rel A → Op A → Set
Associative {A} _≡_ _∘_ = {a b c : A} → (a ∘ (b ∘ c)) ≡ ((a ∘ b) ∘ c)

record <_,_> (A : Set) (B : Set) : Set where
  field
    fst : A
    snd : B

IdL : {A : Set} → Rel A → Op A → A → Set
IdL {A} _≡_ _∘_ ε = {a : A} → (ε ∘ a) ≡ a
IdR : {A : Set} → Rel A → Op A → A → Set
IdR {A} _≡_ _∘_ ε = {a : A} → (a ∘ ε) ≡ a
Id  : {A : Set} → Rel A → Op A → A → Set
Id {A} _≡_ _∘_ e = < IdL _≡_ _∘_ e , IdR _≡_ _∘_ e >

InverseL : {A : Set} → Rel A → Op A → A → Set
InverseL {A} _≡_ _∘_ ε = {a : A} → {exists a⁻¹ : A} → (a ∘ a⁻¹) ≡ ε
InverseR : {A : Set} → Rel A → Op A → A → Set
InverseR {A} _≡_ _∘_ ε = {a : A} → {exists a⁻¹ : A} → (a⁻¹ ∘ a) ≡ ε
Inverse : {A : Set} → Rel A → Op A → A → Set
Inverse {A} _≡_ _∘_ ε = < InverseL _≡_ _∘_ ε , InverseR _≡_ _∘_ ε >

record IsEquiv {A : Set} (_≡_ : Rel A) : Set where
  field
    reflective : Reflective _≡_
    symmetric  : Symmetric  _≡_
    transitive : Transitive _≡_

record IsSemigroup {A : Set} (_≡_ : Rel A) (_∘_ : Op A) : Set where
  field
    isEquiv     : IsEquiv _≡_
    associative : Associative _≡_ _∘_

record IsMonoid {A : Set} (_≡_ : Rel A) (_∘_ : Op A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _≡_ _∘_
    identity    : Id _≡_ _∘_ ε

record IsGroup {A : Set} (_≡_ : Rel A) (_∘_ : Op A) (ε : A) : Set where
  field
    isMonoid : IsMonoid _≡_ _∘_ ε
    inverse  : Inverse _≡_ _∘_ ε

data ℕ : Set where
 Z : ℕ
 S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
Z + n = n
(S m) + n = S (m + n)
infixl 2 _+_

data _ℕ≡_ : ℕ → ℕ → Set where
  ℕrefl : {a : ℕ} →  a ℕ≡ a
infix 1 _ℕ≡_
ℕ-cong    : {n m : ℕ} → n ℕ≡ m → (S n) ℕ≡ (S m)
ℕ-cong ℕrefl = ℕrefl

module ℕ-Reasoning where
  trans : ∀ {x y z : ℕ}
    → x ℕ≡ y
    → y ℕ≡ z
      -----
    → x ℕ≡ z
  trans ℕrefl x₁ = x₁
  infix  1 begin_
  -- infixr 2 _≡⟨⟩_
  infixr 2 _≡⟨_⟩_
  infix  3 _chtd
  begin_ : {x y : ℕ} → x ℕ≡ y → x ℕ≡ y
  begin_ x = x
  -- _≡⟨⟩_  : (x : ℕ) {y : ℕ} →  x ℕ≡ y → x ℕ≡ y
  -- x ≡⟨⟩ x≡y = x≡y
  _≡⟨_⟩_  : (x : ℕ) → {y z : ℕ} → x ℕ≡ y → y ℕ≡ z → x ℕ≡ z
  x ≡⟨ y ⟩ z = trans y z
  _chtd : (x : ℕ) → x ℕ≡ x
  x chtd = ℕrefl
open ℕ-Reasoning

ℕ≡-isRefl : Reflective _ℕ≡_
ℕ≡-isRefl = ℕrefl

ℕ≡-isSym : Symmetric _ℕ≡_
ℕ≡-isSym ℕrefl = ℕrefl

ℕ≡-isTrans : Transitive _ℕ≡_
ℕ≡-isTrans ℕrefl x₁ = x₁

ℕ≡-isEquiv : IsEquiv _ℕ≡_
IsEquiv.reflective ℕ≡-isEquiv = ℕ≡-isRefl
IsEquiv.symmetric ℕ≡-isEquiv = ℕ≡-isSym
IsEquiv.transitive ℕ≡-isEquiv = ℕ≡-isTrans

ℕ-sym : {x y : ℕ} → x ℕ≡ y → y ℕ≡ x
ℕ-sym p = ℕ≡-isSym p

right-Z-reduction : {a : ℕ} → (a + Z) ℕ≡ a
right-Z-reduction {Z} = ℕrefl
right-Z-reduction {S x} = ℕ-cong right-Z-reduction

lemma2 : {a' : ℕ} → ((a' + Z) + Z) ℕ≡ (a' + Z)
lemma2 {Z} = ℕrefl
lemma2 {S a'} =  ℕ-cong lemma2

lemma3 : {a b : ℕ} → (a + b) ℕ≡ (a + Z) + b
lemma3 {Z} {b} = ℕrefl
lemma3 {S a} {Z} =  ℕ-sym lemma2
lemma3 {S a} {S b} with a + Z | right-Z-reduction {a}
...                   | x     | ℕrefl = ℕ-cong ℕrefl

+-isAssoc : Associative _ℕ≡_ _+_
+-isAssoc {Z} {b} {c} = ℕrefl
+-isAssoc {S a} {Z} {Z} = ℕ-cong  ( ℕ-sym lemma2)
+-isAssoc {S a} {Z} {S c} with a + Z | right-Z-reduction {a}
...                          | _     | ℕrefl = ℕ-cong ℕrefl
+-isAssoc {S a} {S b} {Z} with (b + Z) | right-Z-reduction {b} | ((a + S b) + Z) | right-Z-reduction {a + S b}
...                           | _ | ℕrefl | _ | ℕrefl = ℕ-cong ℕrefl
+-isAssoc {S a} {S b} {S c} = ℕ-cong ( +-isAssoc {a} )

ℕ+-isSemigroup : IsSemigroup _ℕ≡_ _+_
IsSemigroup.isEquiv ℕ+-isSemigroup = ℕ≡-isEquiv
IsSemigroup.associative ℕ+-isSemigroup {a} {b} {c} = +-isAssoc {a}

ℕ-have-identity : Id _ℕ≡_ _+_ Z
<_,_>.fst ℕ-have-identity = ℕrefl
<_,_>.snd ℕ-have-identity = right-Z-reduction

ℕ+-isMonoid : IsMonoid _ℕ≡_ _+_ Z
IsMonoid.isSemigroup ℕ+-isMonoid = ℕ+-isSemigroup
IsMonoid.identity ℕ+-isMonoid = ℕ-have-identity
