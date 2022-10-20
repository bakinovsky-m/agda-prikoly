{-# OPTIONS --safe #-}
module LambdaCalculusTypeChecker1 where

open import Data.String hiding (show)
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.List hiding (_++_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Show

-- {- Preloaded
module LambdaCalculus where
  open import Data.Product
  open import Data.List
  open import Function
  
  Name = Nat
  
  infixr 7 _=>_
  data Type : Set where
    nat  : Type
    _=>_ : Type -> Type -> Type
  private variable a b c d : Type
  
  Ctx = List (Name × Type)
  variable Γ : Ctx
  
  infix 4 _∈_
  data _∈_ {A : Set} (a : A) : List A -> Set where
    emm : (as : List A) -> a ∈ a ∷ as
    hmm : ∀ {as c} -> (a ∈ as) -> a ∈ c ∷ as
  
  module Untyped where
    data Term : Set where
      var : Name -> Term
      lit : Nat  -> Term
      suc : Term
      app : Term -> Term -> Term
      lam : Name -> Type -> Term -> Term
  
  module Typed where
    data Term (Γ : Ctx) : Type -> Set where
      var : ∀ {a} (x : Name) (i : (x , a) ∈ Γ) -> Term Γ a
      lit : (n : Nat) -> Term Γ nat
      suc : Term Γ (nat => nat)
      app : Term Γ (a => b) -> Term Γ a -> Term Γ b
      lam : (x : Name) (a : Type) -> Term ((x , a) ∷ Γ) b
          -> Term Γ (a => b)
  
  module Erase where
    open Typed public
    open Untyped renaming (Term to Expr) public
  
    eraseType : Term Γ a -> Expr
    eraseType (var x _) = var x
    eraseType (lit n) = lit n
    eraseType suc = suc
    eraseType (app f x) = app (eraseType f) $ eraseType x
    eraseType (lam x t e) = lam x t $ eraseType e
  
  TypeError = String
  TCM : Set -> Set
  TCM A = TypeError ⊎ A
  
  data Success (Γ : Ctx) : Untyped.Term -> Set where
    ok : ∀ a (v : Typed.Term Γ a) -> Success Γ (Erase.eraseType v)

-- -}

open LambdaCalculus

module TypeCheck where
  open Erase
  open import Data.Product
  open import Function
  open import Data.Nat
  open import Data.Bool

  -- old stdlib patches
  -- ,-injectiveʳ : ∀ {l1 l2} {A : Set l1} → {B : Set l2} → {a c : A} {b d : B} → (a , b) ≡ (c , d) → b ≡ d
  -- ,-injectiveʳ refl = refl

  _type≡ᵇ_ : Type → Type → Bool
  nat type≡ᵇ nat = true
  (x => x₁) type≡ᵇ (y => y₁) = (x type≡ᵇ y) ∧ (x₁ type≡ᵇ y₁)
  _ type≡ᵇ _ = false

  type≡ᵇ-to-≡ : (x y : Type) → x type≡ᵇ y ≡ true → x ≡ y
  type≡ᵇ-to-≡ nat nat eq = refl
  type≡ᵇ-to-≡ (x => x₁) (y => y₁) eq =
    let
    q₁ , q₂ = lemma {x type≡ᵇ y} eq
    q₁' = type≡ᵇ-to-≡ x y q₁
    q₂' = type≡ᵇ-to-≡ x₁ y₁ q₂
    in
    subst (λ k → x => x₁ ≡ k => y₁) q₁' (subst (λ k → x => x₁ ≡ x => k) q₂' refl) 
    where
    lemma : {a b : Bool} → a ∧ b ≡ true → a ≡ true × b ≡ true
    lemma {true} eq = refl , eq


  a∈x∷l→a≡x⊎a∈l : {A : Set} → {a : A} → ∀{x l} → a ∈ x ∷ l → a ≡ x ⊎ a ∈ l 
  a∈x∷l→a≡x⊎a∈l {_} {a} {.a} {[]} (emm .[]) = inj₁ refl
  a∈x∷l→a≡x⊎a∈l {_} {a} {.a} {x₁ ∷ l} (emm .(x₁ ∷ l)) = inj₁ refl
  a∈x∷l→a≡x⊎a∈l {_} {a} {x} {x₁ ∷ l} (hmm q) = inj₂ q

  _ℕ∈?_ : (x : ℕ) → (l : List ℕ) → Dec (x ∈ l)
  x ℕ∈? [] = no (λ ())
  x ℕ∈? (x₁ ∷ l) with x Data.Nat.≟ x₁
  ... | yes z rewrite z = yes (emm l)
  ... | no z with x ℕ∈? l
  ...   | yes zz = yes (hmm zz)
  ...   | no  zz = no (λ x₂ → case a∈x∷l→a≡x⊎a∈l x₂ of λ {
    (inj₁ zzz) → z zzz;
    (inj₂ zzz) → zz zzz
    })

  find-type : (x : ℕ) → (l : List (Name × Type)) → (x∈l : x ∈ (Data.List.map proj₁ l))
            → Type
  find-type x l x∈l with x∈l
  find-type .(proj₁ x₁) (x₁ ∷ l) x∈l | emm .(Data.List.map proj₁ l) = proj₂ x₁
  find-type x (x₁ ∷ l) x∈l | hmm z = find-type x l z
  find-type-lemma : (x : ℕ) → (l : List (Name × Type)) →
    (x∈l : x ∈ Data.List.map proj₁ l) → (x , find-type x l x∈l) ∈ l
  find-type-lemma .(proj₁ x₁) (x₁ ∷ l) (emm .(Data.List.map proj₁ l)) = emm l
  find-type-lemma x (x₁ ∷ l) (hmm x∈l) = hmm (find-type-lemma x l x∈l)

  typeCheck : (Γ : Ctx) (e : Expr) -> TCM (Success Γ e)
  -- typeCheck Γ (var x) = {!!}
  typeCheck Γ (var x) with x ℕ∈? Data.List.map proj₁ Γ
  ... | yes z = inj₂ (ok (find-type x Γ z) (var x (find-type-lemma x Γ z)))
  ... | no z = inj₁ ("Variable out of scope: " ++ show x)
  typeCheck Γ (lit x) = inj₂ (ok nat (lit x))
  typeCheck Γ suc = inj₂ (ok (nat => nat) suc)
  typeCheck Γ (app term term₁) with typeCheck Γ term | typeCheck Γ term₁
  ... | inj₁ x | _      = inj₁ x
  ... | _      | inj₁ x = inj₁ x
  ... | inj₂ (ok nat v) | inj₂ (ok a₁ v₁) = inj₁ "Nat is not a function!"
  ... | inj₂ (ok (a => a₂) v) | inj₂ (ok a₁ v₁) with a type≡ᵇ a₁ | inspect (a type≡ᵇ_) a₁
  ...   | false | _  = inj₁ "Argument type mismatch!"
  ...   | true | zz with inspect (Expr.app term) term₁

  typeCheck Γ (app _ .(eraseType v₁)) | inj₂ (ok (a => a₂) v)
                                      | inj₂ (ok a₁ v₁)
                                      | true
                                      | [ eq ]
                                      | [ refl ]
                                      rewrite type≡ᵇ-to-≡ a a₁ eq =
                                        inj₂ (ok a₂ (app v v₁))

  typeCheck Γ (lam x x_type term) with typeCheck ((x , x_type) ∷ Γ) term
  ... | inj₁ x₁ = inj₁ x₁
  ... | inj₂ y with Expr.lam x x_type term | inspect (Expr.lam x x_type) term
  typeCheck Γ (lam x x_type .(eraseType v)) | inj₂ (ok a v) | .(lam x x_type (eraseType v)) | [ refl ] = inj₂ (ok (x_type => a) (lam x x_type v))

module Test where
  open TypeCheck
  open Untyped renaming (Term to Expr)
  open Typed
  open import Data.Empty
  open import Data.Product

  qwe : 1 ∈ [] → ⊥
  qwe = λ ()
  asd : 1 ∈ (2 ∷ 1 ∷ [])
  asd = hmm (emm [])
  ass : 1 ∈ (1 ∷ 2 ∷ [])
  ass = emm (2 ∷ [])
  qq : 1 ∈ (1 ∷ 1 ∷ [])
  qq = emm (1 ∷ [])
  -- qq = hmm (emm [])

  -- 233
  litTest : typeCheck [] (lit 233) ≡ inj₂ (ok nat (Erase.lit 233))
  litTest = refl

  emptyΓVarTest : typeCheck [] (var 0) ≡ inj₁ "Variable out of scope: 0"
  emptyΓVarTest = refl

  varTest1 : typeCheck ((0 , nat) ∷ []) (var 0) ≡ inj₂ (ok nat (var 0 (emm [])))
  varTest1 = refl
  varTest2 : typeCheck ((123 , nat) ∷ (0 , nat) ∷ []) (var 0) ≡ inj₂ (ok nat (var 0 (hmm (emm []))))
  varTest2 = refl

  -- λ x . x
  idFunc : typeCheck [] (lam 233 nat (var 233))
         ≡ inj₂ (ok (nat => nat)
                (Erase.lam 233 nat (Erase.var 233 (emm []))))
  idFunc = refl

  _ : Term [] nat
  _ = (lit 123)
  _ : Term [] nat 
  _ = app (lam 0 nat (lit 123)) (lit 321)
  _ : Term [] (nat => nat => nat)
  _ = lam 0 nat (lam 1 nat (lit 123))
  _ : Term [] ((nat => nat) => nat)
  _ = lam 0 (nat => nat) (lit zero) --(lit 123)
  _ : Term [] nat
  _ = lit 123
  _ : Term ((0 , nat) ∷ []) nat
  _ = var 0 (emm [])
  _ : Term [] (nat => nat)
  _ = lam 0 nat (var 0 (emm []))
  _ : Term [] ((nat => nat) => nat => nat)
  _ = let w1 = hmm (emm []); w2 = (emm ((123 , (nat => nat)) ∷ [])) in
      lam 123 (nat => nat) (
          lam 321 nat (
              app (var 123 w1) (var 321 w2)
              )
          )
