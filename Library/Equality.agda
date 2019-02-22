{-# OPTIONS --safe --without-K #-}

module Library.Equality where

{-
  Equality reasoning, definitions and basic lemmas.
-}

open import Agda.Primitive
open import Agda.Builtin.Equality public


-- Symmetry
infix 8 _⁻¹
_⁻¹ : ∀ {l} {A : Set l} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

-- Transitivity
infixr 6 _∙_
_∙_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

-- Congruence
ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f refl = refl

-- Dependent paths
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡[ refl ]≡ y = x ≡ y

-- Congruence for dependente paths
apd : ∀ {l m} {A : Set l} {B : A → Set m} (f : (x : A) → B x)
        {x y : A} (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd f refl = refl

-- Transport
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → A ≡ B → A → B
refl * x = x

-- Filling of transport
_*fill_ : ∀ {l} {A B : Set l} (p : A ≡ B) (x : A) →
            x ≡[ p ]≡ p * x
refl *fill px = refl

-- Transport through a dependent family
tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P p x = (ap P p) * x

trfill : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A}
           (p : x ≡ y) (px : P x) → px ≡[ ap P p ]≡ tr P p px
trfill P p x = (ap P p) *fill x

-- and with a dependent path
trd : ∀ {l m n} {A : Set l} {B : A → Set m} (P : {x : A} → B x → Set n)
        {a b : A} {p : a ≡ b} {x : B a} {y : B b} →
        x ≡[ ap B p ]≡ y → P x → P y
trd P {p = refl} refl x = x
