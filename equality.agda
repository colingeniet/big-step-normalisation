{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (primIMin to _∧_;
                                             primIMax to _∨_;
                                             primINeg to 1-_;
                                             primComp to comp;
                                             primHComp to hcomp;
                                             primTransp to transp)
open import Agda.Builtin.Cubical.Path public


infix 8 _⁻¹
infixr 6 _∙_

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} _ = x

_⁻¹ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
(p ⁻¹) i = p (1- i)

_∙_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ {j (i = i0) → x ; j (i = i1) → q j}) (p i)

-- Non dependent path lifting.
ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f p i = f (p i)

-- Transport.
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → A ≡ B → A → B
p * x = comp (λ i → p i) i0 (λ {j ()}) x

-- Transport through a family.
tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P p x = (ap P p) * x

-- Equality through equality of types.
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡[ p ]≡ y = PathP (λ i → p i) x y

-- Dependent path lifting.
apd : ∀ {l m} {A : Set l} {P : A → Set m} (f : (x : A) → P x) {x y : A} →
        (p : x ≡ y) → f x ≡[ ap P p ]≡ f y
apd f p i = f (p i)
