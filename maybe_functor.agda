import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

data Maybe (A : Set) : Set where
 Nothing : Maybe A
 Just : A -> Maybe A

maybe-map : {A B : Set} -> (A -> B) ->  Maybe A -> Maybe B
maybe-map f Nothing = Nothing
maybe-map f (Just x) = Just (f x)

maybe-map-id : {A : Set}
             → (x : Maybe A)
             → (g : A -> A)
             → ((g : A -> A) -> (x : A) -> g x ≡ x)
             → maybe-map g x ≡ x
maybe-map-id Nothing _ _ = refl
maybe-map-id (Just x) g p = cong Just (p g x)

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

maybe-map-compose : {A B C : Set}
                  → (f : B → C)
                  → (g : A → B)
                  → (x : Maybe A)
                  → maybe-map f (maybe-map g x) ≡ (maybe-map f ∘ maybe-map g) x
maybe-map-compose f g Nothing = refl
maybe-map-compose f g (Just x) = refl
