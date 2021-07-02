module category where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

record Category : Set₁ where
 field
  obj : Set
  _=>_ : (A B : obj) -> Set
  _∘_ : ∀ {A B C} → (A => B) → B => C → A => C

data ThreeSet : Set where
 One   : ThreeSet
 Two   : ThreeSet
 Three : ThreeSet

-- id : ThreeSet → ThreeSet
-- id a = a

+1 : ThreeSet -> ThreeSet
+1 One = Two
+1 Two = Three
+1 Three = One

data ThreeSetMor : (a b : ThreeSet) -> Set where
 id-mor : {x : ThreeSet} → ThreeSetMor x x
 +1-mor-1-2 : ThreeSetMor One Two
 +1-mor-1-3 : ThreeSetMor One Three
 +1-mor-2-3 : ThreeSetMor Two Three
 +1-mor-2-1 : ThreeSetMor Two One
 +1-mor-3-1 : ThreeSetMor Three One
 +1-mor-3-2 : ThreeSetMor Three Two

comp : {a b c : ThreeSet} -> ThreeSetMor a b -> ThreeSetMor b c -> ThreeSetMor a c
comp id-mor id-mor = id-mor
comp id-mor +1-mor-1-2 = +1-mor-1-2
comp id-mor +1-mor-1-3 = +1-mor-1-3
comp id-mor +1-mor-2-3 = +1-mor-2-3
comp id-mor +1-mor-2-1 = +1-mor-2-1
comp id-mor +1-mor-3-1 = +1-mor-3-1
comp id-mor +1-mor-3-2 = +1-mor-3-2
comp +1-mor-1-2 id-mor = +1-mor-1-2
comp +1-mor-1-2 +1-mor-2-3 = +1-mor-1-3
comp +1-mor-1-2 +1-mor-2-1 = id-mor
comp +1-mor-1-3 id-mor = +1-mor-1-3
comp +1-mor-1-3 +1-mor-3-1 = id-mor
comp +1-mor-1-3 +1-mor-3-2 = +1-mor-1-2
comp +1-mor-2-3 id-mor = +1-mor-2-3
comp +1-mor-2-3 +1-mor-3-1 = +1-mor-2-1
comp +1-mor-2-3 +1-mor-3-2 = id-mor
comp +1-mor-2-1 id-mor = +1-mor-2-1
comp +1-mor-2-1 +1-mor-1-2 = id-mor
comp +1-mor-2-1 +1-mor-1-3 = +1-mor-2-3
comp +1-mor-3-1 id-mor = +1-mor-3-1
comp +1-mor-3-1 +1-mor-1-2 = +1-mor-3-2
comp +1-mor-3-1 +1-mor-1-3 = id-mor
comp +1-mor-3-2 id-mor = +1-mor-3-2
comp +1-mor-3-2 +1-mor-2-3 = id-mor
comp +1-mor-3-2 +1-mor-2-1 = +1-mor-3-1

three-set-cat : Category
three-set-cat = record {obj = ThreeSet; _=>_ = ThreeSetMor; _∘_ = comp}
