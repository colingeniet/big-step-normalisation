{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (primIMin to _∧_;
                                             primIMax to _∨_;
                                             primINeg to 1-_;
                                             primComp to comp;
                                             primHComp to hcomp;
                                             primTransp to transp)
open import Agda.Builtin.Cubical.Path public



refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} _ = x

infix 8 _⁻¹
_⁻¹ : ∀ {a} {A : I → Set a} {x : A i0} {y : A i1} →
        PathP A x y → PathP (λ i → A (1- i)) y x
(p ⁻¹) i = p (1- i)

partial : ∀ {l} {A : Set l} {x y : A} (p : x ≡ y) (i : I) → x ≡ p i
partial p i j = p (i ∧ j)

partial0 : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} {i : I} → partial p i0 ≡ refl
partial0 = refl

partial1 : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} {i : I} → partial p i1 ≡ p
partial1 = refl


-- Equality through equality of types.
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡[ p ]≡ y = PathP (λ i → p i) x y


-- Path lifting
-- Fully dependent
apd : ∀ {l m} {A : I → Set l} {B : {i : I} → A i → Set m}
       (f : {i : I} (a : A i) → B a) {x : A i0} {y : A i1} →
       (p : PathP A x y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)

-- Not dependent.
ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f = apd f

-- Dependent, but not too much.
ap≡[]≡ : ∀ {l m n} {J : Set l} {A : J → Set m} {B : {j : J} → A j → Set n}
           (f : {j : J} (x : A j) → B x) {j1 j2 : J} {P : j1 ≡ j2}
           {x : A j1} {y : A j2} (p : x ≡[ ap A P ]≡ y) →
           f x ≡[ apd (λ {i} j → B (p i)) P ]≡ f y
ap≡[]≡ f p i = f (p i)


-- Transport.
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → PathP (λ i → Set l) A B → A → B
p * x = comp (λ i → p i) i0 (λ j → λ {()}) x

-- Transport through a family.
trd : ∀ {l m} {A : I → Set l} (P : {i : I} → A i → Set m) {x : A i0} {y : A i1} →
        PathP A x y → P x → P y
trd P p x = (apd P p) * x

tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P = trd P

-- Composition (transitivity) of paths.
infixr 6 _∙_ _d∙_ _∙d_
_∙_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q = tr (λ w → x ≡ w) q p

_d∙_ : ∀ {a} {A : I → Set a} {x : A i0} {y z : A i1} →
         PathP A x y → y ≡ z → PathP A x z
_d∙_ {A = A} {x = x} p q = tr (λ w → PathP A x w) q p

_∙d_ : ∀ {a} {A : I → Set a} {x y : A i0} {z : A i1} →
         x ≡ y → PathP A y z → PathP A x z
_∙d_ {A = A} {z = z} p q = ((q ⁻¹) d∙ (p ⁻¹)) ⁻¹

-- Fundamental equalities for transport, aka filling.
_*fill_ : ∀ {l} {A B : Set l} (p : A ≡ B) (x : A) →
            x ≡[ p ]≡ (p * x)
(p *fill x) i = comp (λ j → p (i ∧ j)) (1- i) (λ j → λ {(i = i0) → x}) x

trdfill : ∀ {l m} {A : I → Set l} (P : {i : I} → A i → Set m) {x : A i0} {y : A i1} →
            (p : PathP A x y) (px : P x) → PathP (λ i → P (p i)) px (trd P p px)
trdfill P p px = (apd P p) *fill px

trfill : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A}
           (p : x ≡ y) (px : P x) → px ≡[ ap P p ]≡ tr P p px
trfill P p px = (ap P p) *fill px


-- Composition of paths above paths.
infixr 6 _d∙d_
_d∙d_ : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C} {x : A} {y : B} {z : C} →
         x ≡[ P ]≡ y → y ≡[ Q ]≡ z → x ≡[ P ∙ Q ]≡ z
_d∙d_ {A = A} {P = P} {Q = Q}{x = x} p q =
  trd (λ {i} w → x ≡[ trfill (λ D → A ≡ D) Q P i  ]≡ w) q p

