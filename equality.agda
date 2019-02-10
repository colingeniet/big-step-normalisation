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

partial : ∀ {l} {A : Set l} {x y : A} (p : x ≡ y) (i : I) → x ≡ p i
partial p i j = p (i ∧ j)

partial0 : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} {i : I} → partial p i0 ≡ refl
partial0 = refl

partial1 : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} {i : I} → partial p i1 ≡ p
partial1 = refl

-- Path lifting
apd : ∀ {l m} {A : I → Set l} {B : {i : I} → A i → Set m}
       (f : {i : I} (a : A i) → B a) {x : A i0} {y : A i1} →
       (p : PathP A x y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)

ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f = apd f

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
        

-- Equality through equality of types.
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡[ p ]≡ y = PathP (λ i → p i) x y


-- Fundamental equalities for transport, aka filling.
_*fill_ : ∀ {l} {A B : Set l} (p : A ≡ B) (x : A) →
            x ≡[ p ]≡ (p * x)
(p *fill x) i = comp (λ j → p (i ∧ j)) (1- i) (λ j → λ {(i = i0) → x}) x

trfill : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} (p : x ≡ y) (px : P x) →
           px ≡[ ap P p ]≡ tr P p px
trfill P p px = (ap P p) *fill px
