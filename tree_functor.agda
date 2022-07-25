open import Agda.Primitive using (lsuc; _⊔_; Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

data Maybe a : Set where
  Nothing : Maybe a
  Just    : a -> Maybe a

data Tree a : Set where
  Nil  : Tree a
  Node : Tree a → a → Tree a → Tree a

id : {l : Level} -> {a : Set l} → a -> a
id x = x

_∘_ : {A B C : Set} → (g : B → C) → (f : A → B) → (a : A) → C
g ∘ f = λ x → g (f x)

record Functor (F : Set -> Set) : Set1 where
  field
    _<$>_ : {A B : Set} -> (A -> B) -> F A -> F B
    idLaw : {A : Set} → {a : F A} → (id <$> a) ≡ a
    composeLaw :
      {A B C : Set} →
      {a : F A} →
      {f : A → B} →
      {g : B → C} →
      g <$> (f <$> a) ≡ (g ∘ f) <$> a

treeFmap : {a b : Set} → (a -> b) → Tree a → Tree b
treeFmap f Nil = Nil
treeFmap f (Node t x t₁) = Node (treeFmap f t) (f x) (treeFmap f t₁)

treeIdLaw : {A : Set} → {a : Tree A} → (treeFmap id a) ≡ a
treeIdLaw {A} {Nil} = refl
treeIdLaw {A} {Node Nil x Nil} = refl
treeIdLaw {A} {Node Nil x r} =
  begin
    Node Nil (id x) (treeFmap id r)
  ≡⟨⟩
    Node Nil x (treeFmap id r)
  ≡⟨ cong (Node Nil x) treeIdLaw ⟩
  refl
treeIdLaw {A} {Node (Node left x₁ left₁) x right} = 
  begin
    Node (Node (treeFmap id left) (id x₁) (treeFmap id left₁)) (id x) (treeFmap id right)
  ≡⟨ refl ⟩
    Node (Node (treeFmap id left) x₁ (treeFmap id left₁)) x (treeFmap id right)
  ≡⟨ cong (Node (Node (treeFmap id left) x₁ (treeFmap id left₁)) x) treeIdLaw ⟩
    Node (Node (treeFmap id left) x₁ (treeFmap id left₁)) x right
  ≡⟨ cong (λ y → Node y x right) (cong (λ y → Node y x₁ (treeFmap id left₁)) treeIdLaw) ⟩
  Node (Node left x₁ (treeFmap id left₁)) x right
  ≡⟨ cong (λ y → Node y x right) (cong (Node left x₁) treeIdLaw) ⟩
  Node (Node left x₁ left₁) x right
  ∎

treeComposeLaw : {A B C : Set} →
                 {t : Tree A} →
                 {f : A → B} →
                 {g : B → C} →
                 treeFmap g (treeFmap f t) ≡ treeFmap (g ∘ f) t
treeComposeLaw {A} {B} {C} {Nil} {f} {g} = refl
treeComposeLaw {A} {B} {C} {Node t x t₁} {f} {g} =
  begin
  Node (treeFmap g (treeFmap f t)) (g (f x)) (treeFmap g (treeFmap f t₁))
  ≡⟨ refl ⟩
  Node (treeFmap g (treeFmap f t)) ((g ∘ f) x) (treeFmap g (treeFmap f t₁))
  ≡⟨ cong (λ left → Node left ((g ∘ f) x) (treeFmap g (treeFmap f t₁)))
        treeComposeLaw ⟩
  Node (treeFmap (g ∘ f) t) ((g ∘ f) x) (treeFmap g (treeFmap f t₁))
  ≡⟨ cong (λ right → Node (treeFmap (g ∘ f) t) ((g ∘ f) x) right) treeComposeLaw ⟩
  Node (treeFmap (g ∘ f) t) ((g ∘ f) x) (treeFmap (g ∘ f) t₁)
  ∎

-- !!!!!!!!!!!!!!!!!
treeIsFunctor : Functor Tree
treeIsFunctor = record { _<$>_ = treeFmap; idLaw = treeIdLaw; composeLaw = treeComposeLaw}
-- !!!!!!!!!!!!!!!!!







data List (A : Set) : Set where
  LNil : List A
  _::_ : (a : A) -> List A -> List A
listFmap : {A B : Set} → (f : A → B) → List A → List B
listFmap f LNil = LNil
listFmap f (a :: x) = f a :: listFmap f x

listIdLaw : {A : Set} → {a : List A} → listFmap id a ≡ a
listIdLaw {A} {LNil} = refl
listIdLaw {A} {x :: xs} = {!!}
