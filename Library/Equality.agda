{-# OPTIONS --safe --cubical #-}

module Library.Equality where

{-
  Equality reasoning, definitions and basic lemmas.
-}

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (primIMin to _∧_;
            primIMax to _∨_;
            primINeg to 1-_;
            primComp to comp;
            primHComp to hcomp;
            primTransp to transp;
            itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path public


-- Dependent paths
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
_≡[_]≡_ {l} {A} x P y = PathP (λ i → P i) x y

-- Reflexivity
refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} _ = x

-- Symmetry
infix 8 _⁻¹
_⁻¹ : ∀ {l} {A : I → Set l} {x : A i0} {y : A i1} →
        PathP A x y → PathP (λ i → A (1- i)) y x
(p ⁻¹) i = p (1- i)

-- Congruence
apd : ∀ {l m} {A : I → Set l} {B : {i : I} → A i → Set m}
       (f : {i : I} (a : A i) → B a) {x : A i0} {y : A i1} →
       (p : PathP A x y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)

ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       (p : x ≡ y) → f x ≡ f y
ap f = apd f

ap2 : ∀ {l m n} {A : Set l} {B : Set m} {C : Set n} (f : A → B → C)
        {x y : A} {u v : B} → (p : x ≡ y) (q : u ≡ v) → f x u ≡ f y v
ap2 f p q i = f (p i) (q i)

-- Transport
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → A ≡ B → A → B
p * x = transp (λ i → p i) i0 x

trd : ∀ {l m} {A : I → Set l} (P : {i : I} → A i → Set m) {x : A i0} {y : A i1} →
        PathP A x y → P x → P y
trd P p x = (apd P p) * x

tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P = trd P

-- Filling of transport
_*fill_ : ∀ {l} {A B : Set l} (p : A ≡ B) (x : A) →
            x ≡[ p ]≡ p * x
(p *fill x) i = transp (λ j → p (i ∧ j)) (1- i) x

trdfill : ∀ {l m} {A : I → Set l} (P : {i : I} → A i → Set m) {x : A i0} {y : A i1} →
            (p : PathP A x y) (px : P x) → PathP (λ i → P (p i)) px (trd P p px)
trdfill P p x = (apd P p) *fill x

trfill : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A}
           (p : x ≡ y) (px : P x) → px ≡[ ap P p ]≡ tr P p px
trfill P = trdfill P


-- Transitivity
infixr 6 _∙_ _d∙_
_∙_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q = tr (λ w → x ≡ w) q p

_d∙_ : ∀ {a} {A : I → Set a} {x : A i0} {y z : A i1} →
         PathP A x y → y ≡ z → PathP A x z
_d∙_ {A = A} {x = x} p q = tr (λ w → PathP A x w) q p

_∙d_ : ∀ {a} {A : I → Set a} {x y : A i0} {z : A i1} →
         x ≡ y → PathP A y z → PathP A x z
_∙d_ {A = A} {z = z} p q = ((q ⁻¹) d∙ (p ⁻¹)) ⁻¹

_d∙d_ : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C}
          {x : A} {y : B} {z : C} → x ≡[ P ]≡ y → y ≡[ Q ]≡ z →
          x ≡[ P ∙ Q ]≡ z
_d∙d_ {A = A} {P = P} {Q} {x} p q =
  trd (λ {i} w → x ≡[ trfill (λ D → A ≡ D) Q P i ]≡ w) q p




isProp : ∀ {l} → Set l → Set l
isProp A = (x y : A) → x ≡ y

isSet : ∀ {l} → Set l → Set l
isSet A = {x y : A} → isProp (x ≡ y)

PropisSet : ∀ {l} {A : Set l} → isProp A → isSet A
PropisSet isprop {x} {y} p q j i =
  hcomp (λ k → λ {(i = i0) → isprop x x k;
                  (i = i1) → isprop x y k;
                  (j = i0) → isprop x (p i) k;
                  (j = i1) → isprop x (q i) k})
        x

isPropisProp : ∀ {l} {A : Set l} → isProp (isProp A)
isPropisProp P Q i x y = PropisSet P (P x y) (Q x y) i

isPropisSet : ∀ {l} {A : Set l} → isProp (isSet A)
isPropisSet P Q i {x} {y} = isPropisProp (P {x} {y}) (Q {x} {y}) i


{-
test0 : ∀ {l m} {A : Set l} {B : A → Set m} →
          ({x : A} → isProp (B x)) →
          {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
          x ≡[ ap B p ]≡ y
test0 {B = B} H p x y = trfill B p x d∙ H (tr B p x) y

test1 : ∀ {l m} {A : Set l} {B : A → Set m} →
          ({x : A} → isSet (B x)) →
          {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
          isProp (x ≡[ ap B p ]≡ y)
test1 H p x y r s = {!!}

test2 : ∀ {l m} {A : Set l} {B : A → Set m} →
          ({x : A} → isSet (B x)) →
          {a b : A} {p q : a ≡ b} (α : p ≡ q)
          {x : B a} {y : B b} (r : x ≡[ ap B p ]≡ y) (s : x ≡[ ap B q ]≡ y) →
          r ≡[ ap (λ p → x ≡[ ap B p ]≡ y) α ]≡ s
test2 {B = B} H {a} {b} {p} {q} α {x} {y} r s =
  {!test {A = a ≡ b} {B = λ p → x ≡[ ap B p ]≡ y} !}
-}
