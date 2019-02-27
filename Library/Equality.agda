{-# OPTIONS --safe --cubical #-}

module Library.Equality where

{-
  Equality definitions.
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

⁻¹⁻¹ : ∀ {l} {A : I → Set l} {x : A i0} {y : A i1} {p : PathP A x y} →
         p ⁻¹ ⁻¹ ≡ p
⁻¹⁻¹ = refl

refl⁻¹ : ∀ {l} {A : Set l} {x : A} → refl {x = x} ⁻¹ ≡ refl
refl⁻¹ = refl

-- Transitivity
infixr 6 _∙_ _d∙_ _∙d_ _d∙d_
_∙_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ j → λ {(i = i0) → x; (i = i1) → q j}) (p i)


-- Transitivity laws.

{-
  The filling of the squared used to prove transitivity of paths.
  It looks like:
  
  j^
   |->i
  
      p∙q
     _____
    |     |
  x |     | q
    |_____|
       p
-}
private
  transitivity-square : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                          I → I → A
  transitivity-square {x = x} p q i j =
    hcomp (λ k → λ {(i = i0) → x;
                    (i = i1) → q (j ∧ k);
                    (j = i0) → p i})
          (p i)

{-
  Yet another usefull square.
  It looks like:

  j^
   |->i
  
       q
     _____
    |     |
  p |     | q
    |_____|
       p
-}
private
  diagonal-square : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                      I → I → A
  diagonal-square {x = x} {y} p q i j =
    hcomp (λ k → λ {(i = i0) → p j;
                    (j = i0) → p i;
                    (i = i1) → q (j ∧ k);
                    (j = i1) → q (i ∧ k)})
          (p (i ∨ j))

-- Refl is neutral for transitivity.
∙refl : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} →
          p ∙ refl ≡ p
∙refl {p = p} i j = transitivity-square p refl j (1- i)

refl∙ : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} →
          refl ∙ p ≡ p
refl∙ {x = x} {p = p} j i =
  hcomp (λ k → λ {(i = i0) → x;
                  (i = i1) → p k;
                  (j = i1) → p (i ∧ k)})
        x

-- Symmetry is an inverse for transitivity.
-∙-⁻¹ : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ∙ p ⁻¹ ≡ refl
-∙-⁻¹ {x = x} {p = p} j i =
  hcomp (λ k → λ {(j = i1) → x;
                  (i = i0) → x;
                  (i = i1) → p (1- j ∧ 1- k)})
        (p (1- j ∧ i))

-⁻¹∙- : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ⁻¹ ∙ p ≡ refl
-⁻¹∙- = -∙-⁻¹


{-
  This squares is a face of the cube used to prove associativity.
  It is somewhat similar to the transitivity-square above, but the link is not
  obvious to me.
  It looks like this:
  j^
   |->i
  
       z
     _____
    |     |
  q |     | p∙q
    |_____|
      p⁻¹
-}
private
  assoc-cube-back : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                      I → I → A
  assoc-cube-back p q i j =
    hcomp (λ k → λ {(i = i0) → q (j ∧ k);
                    (j = i0) → p (1- i);
                    (j = i1) → q k})
          (p (1- i ∨ j))

-- Associativity.
∙∙ : ∀ {l} {A : Set l} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
       (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙∙ {x = x} {p = p} {q} {r} j i =
  hcomp (λ k → λ {(i = i0) → x;
                  (i = i1) → assoc-cube-back q r j k})
        (transitivity-square p q i (1- j))

-- Inverse of composition.
∙⁻¹ : ∀ {l} {A : Set l} {x y z : A} {p : x ≡ y} {q : y ≡ z} →
        (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
∙⁻¹ {p = p} {q} j i =
  hcomp (λ k → λ {(i = i0) → q (j ∨ k);
                  (i = i1) → p (j ∧ 1- k)})
        (diagonal-square p q (1- i) j)


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


-- Transitivity for dependent paths.
_d∙d_ : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C}
          {x : A} {y : B} {z : C} → x ≡[ P ]≡ y → y ≡[ Q ]≡ z →
          x ≡[ P ∙ Q ]≡ z
_d∙d_ {A = A} {P = P} {Q} {x} p q i =
   comp (λ j → transitivity-square P Q i j) _
        (λ j → λ {(i = i0) → x; (i = i1) → q j}) (p i)

_d∙_ : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y z : B} →
         x ≡[ P ]≡ y → y ≡ z → x ≡[ P ]≡ z
_d∙_ {P = P} p q = tr (λ P → _ ≡[ P ]≡ _) (∙refl {p = P}) (p d∙d q)

_∙d_ : ∀ {l} {A B : Set l} {P : A ≡ B} {x y : A} {z : B} →
         x ≡ y → y ≡[ P ]≡ z → x ≡[ P ]≡ z
_∙d_ {P = P} p q = tr (λ P → _ ≡[ P ]≡ _) (refl∙ {p = P}) (p d∙d q)



{-
-- An alternative definition of dependent paths.
_≡*_*≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡* P *≡ y = (P * x) ≡ y

-- Isomorphism between the two notions of dependent paths.
≡[]≡to≡**≡ : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} →
                x ≡[ P ]≡ y → x ≡* P *≡ y
≡[]≡to≡**≡ {P = P} {x} {y} p = tr (λ Q → P * x ≡[ Q ]≡ y)
                                  (-⁻¹∙- {p = P})
                                  ((P *fill x ⁻¹) d∙d p)

≡**≡to≡[]≡ : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} →
                x ≡* P *≡ y → x ≡[ P ]≡ y
≡**≡to≡[]≡ {P = P} {x} p = (P *fill x) d∙ p

≡[]≡to≡**≡-iso : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B}
                   {p : x ≡[ P ]≡ y} → ≡**≡to≡[]≡ (≡[]≡to≡**≡ p) ≡ p
≡[]≡to≡**≡-iso = {!!}

≡**≡to≡[]≡-iso : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B}
                   {p : x ≡* P *≡ y} → ≡[]≡to≡**≡ (≡**≡to≡[]≡ {P = P} p) ≡ p
≡**≡to≡[]≡-iso {P = P} {x} {y} {p} = {!(P *fill x ⁻¹) d∙d (P *fill x) d∙ p!}
-}