{-# OPTIONS --safe #-}

module SL2N-unique where
module Matrix where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  
  -- 2x2 non-negative matrix [[a b] [c d]]
  record Mat : Set where
    constructor mat
    field
      a b c d : ℕ
  open Mat
  
  -- Equality on all four elements gives equality of mat
  congMat : ∀ {a b c d a' b' c' d'} → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → mat a b c d ≡ mat a' b' c' d'
  congMat refl refl refl refl = refl
  
  -- A data type for 2x2 matrix of ℕ with determinant 1
  data SL2N : Set where
    I : SL2N -- [[1 0] [0 1]]
    top+ : SL2N → SL2N -- [[a b] [c d]] → [[a+c b+d] [c d]]
    bot+ : SL2N → SL2N -- [[a b] [c d]] → [[a b] [a+c b+d]]
  
  -- Evaluate an SL2N into a Mat
  eval : SL2N → Mat
  eval I = mat 1 0 0 1
  eval (top+ m) with eval m
  ... | mat a b c d = mat (a + c) (b + d) c d
  eval (bot+ m) with eval m
  ... | mat a b c d = mat a b (a + c) (b + d)

open Matrix
open Mat

open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-identityˡ; suc-injective; +-cancelʳ-≡; +-cancelˡ-≡)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong; _≢_; refl; inspect; [_]; sym)
open Eq.≡-Reasoning
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Empty using (⊥; ⊥-elim)

mat≡→elements≡ : ∀ {a b c d a' b' c' d'} → mat a b c d ≡ mat a' b' c' d' → (a ≡ a') × (b ≡ b') × (c ≡ c') × (d ≡ d')
mat≡→elements≡ refl = record {fst = refl; snd = record {fst = refl; snd = record {fst = refl; snd = refl}}}

n+1≢0 : {n m : ℕ} → (p : m ≡ 1) → n + m ≢ 0
n+1≢0 {zero} {zero} () x
n+1≢0 {zero} {suc m} p ()
1+n≢0 : {n m : ℕ} → (p : m ≡ 1) → m + n ≢ 0
1+n≢0 {zero} {zero} () x
1+n≢0 {zero} {suc m} p ()
x+y≡0→x≡0 : ∀{x y} → x + y ≡ 0 → x ≡ 0
x+y≡0→x≡0 {zero} {y} eq = refl
x+y≡0→y≡0 : ∀{x y} → x + y ≡ 0 → y ≡ 0
x+y≡0→y≡0 {zero} {y} eq = eq

x≡y→x≡y+0 : {x y : ℕ} → x ≡ y → x ≡ y + 0 
x≡y→x≡y+0 {zero} {zero} _ = refl
x≡y→x≡y+0 {suc x} {suc y} qeq = cong suc (x≡y→x≡y+0 (suc-injective qeq))

mata≢0 : {n : SL2N} → a (eval n) ≢ 0
mata≢0 {top+ n} x with eval n | eval (top+ n) | inspect eval n | inspect eval (top+ n)
... | mat a' b' c' d' | mat .(a' + c') .(b' + d') _ _ | [ refl ] | [ refl ] = mata≢0 {n} (l1 x)
  where
    l1 : {x y : ℕ} → x + y ≡ 0 → x ≡ 0
    l1 {zero} {y} eq = refl
mata≢0 {bot+ n} x with eval n | eval (bot+ n) | inspect eval n | inspect eval (bot+ n)
... | mat a' b' c' d' | mat _ _ .(a' + c') .(b' + d') | [ refl ] | [ refl ] = mata≢0 {n} x
matd≢0 : {n : SL2N} → d (eval n) ≢ 0
matd≢0 {top+ n} x with eval n | eval (top+ n) | inspect eval n | inspect eval (top+ n)
... | mat a' b' c' d' | mat .(a' + c') .(b' + d') _ _ | [ refl ] | [ refl ] = matd≢0 {n} x
matd≢0 {bot+ n} x with eval n | eval (bot+ n) | inspect eval n | inspect eval (bot+ n)
... | mat a' b' c' d' | mat _ _ .(a' + c') .(b' + d') | [ refl ] | [ refl ] = matd≢0 {n} (l1 x)
  where
  l1 : {x y : ℕ} → x + y ≡ 0 → y ≡ 0
  l1 {zero} eq = eq

evalI≢evaltop+ : {n : SL2N} → eval I ≢ eval (top+ n)
evalI≢evaltop+ {n} eq with eval n
... | mat a b c d with eval (top+ n)
...               | mat a' b' c' d' =
  let
  q = mat≡→elements≡ eq
  0≡b+d = proj₁ (proj₂ q)
  1≡d   = proj₂ (proj₂ (proj₂ q))
  in n+1≢0 (sym 1≡d) (sym 0≡b+d)
evaltop+≢evalI : {n : SL2N} → eval (top+ n) ≢ eval I
evaltop+≢evalI {n} x = evalI≢evaltop+ {n} (sym x)
evalI≢evalbot+ : {n : SL2N} → eval I ≢ eval (bot+ n)
evalI≢evalbot+ {n} eq with eval n
... | mat a b c d with eval (top+ n)
...               | mat a' b' c' d' =
  let
  q = mat≡→elements≡ eq
  (1≡a , (_ , (0≡a+c , _))) = q
  in 1+n≢0 (sym 1≡a) (sym 0≡a+c)
evalbot+≢evalI : {n : SL2N} → eval (bot+ n) ≢ eval I
evalbot+≢evalI {n} x = evalI≢evalbot+ {n} (sym x)

evaltop+≢evalbot+ : {n m : SL2N} → eval (top+ n) ≢ eval (bot+ m)
evaltop+≢evalbot+ {n} {m} eq with eval n
                                 | eval m
                                 | eval (top+ n)
                                 | eval (bot+ m)
                                 | inspect eval n
                                 | inspect eval m
                                 | inspect eval (top+ n)
                                 | inspect eval (bot+ m)
... | mat a₁ b₁ c₁ d₁ | mat a₂ b₂ c₂ d₂ | mat .(a₁ + c₁) .(b₁ + d₁) _ _ | mat _ _ .(a₂ + c₂) .(b₂ + d₂) | [ refl ] | [ refl ] | [ refl ] | [ refl ] =
  let
  (p1 , p2 , p3 , p4) = mat≡→elements≡ eq
  p5 = l1 {a (eval n)} p1 p3
  p6 = sym (l2 {c (eval n)} {a (eval n)} p5)
  p7 = x+y≡0→x≡0 {a (eval n)} p6
  p8 = mata≢0 {n} p7
  in
  p8
  where
    l1 : ∀{a b c d e} → a + b ≡ c → d ≡ c + e → d ≡ a + b + e
    l1 {a} {b} {c} {d} {e} eq1 eq2 rewrite eq1 = eq2
    l21 : ∀{x y} → x ≡ y → x + 0 ≡ y
    l21 {zero} {y} eq = eq
    l21 {suc x} {y} eq rewrite +-identityʳ x = eq
    l2 : ∀{x y z} → x ≡ y + x + z → 0 ≡ y + z
    l2 {zero} {y} {z} eq rewrite +-identityʳ y = eq
    {-
    is not accepted by codewars (they have agda 2.6.0, which doesn't have irrefutable with's yet)
    l2 {suc x} {y} {z} eq rewrite +-comm y (suc x)
                          with eq1 ← l21 eq
                          with eq2 ← suc-injective eq1
                          rewrite +-assoc x y z
                          with eq3 ← +-cancelˡ-≡ x eq2
                          = eq3
    -}
    l2 {suc x} {y} {z} eq rewrite +-comm y (suc x) with suc-injective (l21 eq)
    ... | eq1 rewrite +-assoc x y z = +-cancelˡ-≡ x eq1



a+b≡c+d→b≡d→a≡c : {a b c d : ℕ} → a + b ≡ c + d → b ≡ d → (a ≡ c)
a+b≡c+d→b≡d→a≡c {a₁} {b₁} {c₁} {.b₁} x refl = +-cancelʳ-≡ a₁ c₁ x
a+b≡c+d→a≡c→b≡d : {a b c d : ℕ} → a + b ≡ c + d → a ≡ c → (b ≡ d)
a+b≡c+d→a≡c→b≡d {a₁} {b₁} {.a₁} {d₁} x refl = +-cancelˡ-≡ a₁ x

-- Prove that eval is injective, i.e. for any 2x2 matrix in the set SL2N, the representation is unique.
eval-injective : (m n : SL2N) → (eq : eval m ≡ eval n) → m ≡ n
eval-injective I I eq = refl
eval-injective I (top+ n) eq = ⊥-elim (evalI≢evaltop+ {n} eq)
eval-injective I (bot+ n) eq = ⊥-elim (evalI≢evalbot+ {n} eq)
eval-injective (top+ m) I eq = ⊥-elim (evaltop+≢evalI {m} eq)
eval-injective (top+ m) (top+ n) eq with eval m
                                       | eval n
                                       | eval (top+ m)
                                       | eval (top+ n)
                                       | inspect eval m
                                       | inspect eval n
                                       | inspect eval (top+ m)
                                       | inspect eval (top+ n)
... | mat a' b' c' d' | mat a'' b'' c'' d'' | mat .(a' + c') .(b' + d') _ _ | mat .(a'' + c'') .(b'' + d'') _ _ | [ refl ] | [ refl ] | [ refl ] | [ refl ] =
  let
  q = mat≡→elements≡ eq
  (a+c≡ , b+d≡ , c≡ , d≡) = q
  a≡ = a+b≡c+d→b≡d→a≡c a+c≡ c≡
  b≡ = a+b≡c+d→b≡d→a≡c b+d≡ d≡
  in
  cong top+ (eval-injective m n (congMat a≡ b≡ c≡ d≡))
eval-injective (top+ m) (bot+ n) eq = ⊥-elim (evaltop+≢evalbot+ {m} {n} eq)
eval-injective (bot+ m) I eq = ⊥-elim (evalbot+≢evalI {m} eq)
eval-injective (bot+ m) (top+ n) eq = ⊥-elim (evaltop+≢evalbot+ {n} {m} (sym eq))
eval-injective (bot+ m) (bot+ n) eq with eval m
                                       | eval n
                                       | eval (bot+ m)
                                       | eval (bot+ n)
                                       | inspect eval m
                                       | inspect eval n
                                       | inspect eval (bot+ m)
                                       | inspect eval (bot+ n)
... | mat a' b' c' d' | mat a'' b'' c'' d'' | mat _ _ .(a' + c') .(b' + d') | mat _ _ .(a'' + c'') .(b'' + d'') | [ refl ] | [ refl ] | [ refl ] | [ refl ] =
  let
  q = mat≡→elements≡ eq
  (a≡ , b≡ , a+c≡ , b+d≡) = q
  c≡ = a+b≡c+d→a≡c→b≡d a+c≡ a≡
  d≡ = a+b≡c+d→a≡c→b≡d b+d≡ b≡
  in
  cong bot+ (eval-injective m n (congMat a≡ b≡ c≡ d≡))
