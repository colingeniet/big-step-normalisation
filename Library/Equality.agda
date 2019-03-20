{-# OPTIONS --safe --cubical #-}

module Library.Equality where

{-
  Equality definitions.
-}

open import Agda.Primitive
open import Agda.Primitive.Cubical public
  renaming (primIMin to _∧_;
            primIMax to _∨_;
            primINeg to 1-_;
            primComp to comp;
            primHComp to hcomp;
            primTransp to transp;
            itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming (Sub to _[_↦_];
            primSubOut to ouc)



hfill : ∀ {l} {A : Set l} {φ : I} (u : ∀ i → Partial φ A)
          (u0 : A [ φ ↦ u i0 ]) → I → A
hfill {φ = φ} u u0 i = hcomp (λ j → λ {(φ = i1) → u (i ∧ j) 1=1;
                                       (i = i0) → ouc u0})
                             (ouc u0)

fill : ∀ {l} (A : I → Set l) (φ : I) (u : ∀ i → Partial φ (A i))
             (u0 : A i0 [ φ ↦ u i0 ]) (i : I) → A i
fill A φ u u0 i = comp (λ j → A (i ∧ j)) _
                       (λ j → λ {(φ = i1) → u (i ∧ j) 1=1;
                                 (i = i0) → ouc u0 })
                       (ouc u0)


-- Reflexivity
refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} _ = x


J : ∀ {l m} {A : Set l} {x : A} (P : {y : A} → x ≡ y → Set m) →
      P refl → {y : A} (p : x ≡ y) → P p
J P c p = transp (λ i → P (λ k → p (i ∧ k))) i0 c

-- Downside of paths : this equality is not definitional.
J≡ : ∀ {l m} {A : Set l} {x : A} (P : {y : A} → x ≡ y → Set m) →
       (c : P refl) → J P c refl ≡ c
J≡ P c i = transp (λ _ → P refl) i c


-- Dependent paths
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
_≡[_]≡_ {l} {A} x P y = PathP (λ i → P i) x y

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
transitivity-square : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                        I → I → A
transitivity-square {x = x} p q i =
  hfill (λ j → λ {(i = i0) → x; (i = i1) → q j}) (inc (p i))

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
diagonal-square : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                    I → I → A
diagonal-square p q i j =
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



ap∙ : ∀ {l m} {A : Set l} {B : Set m} {f : A → B}
        {x y z : A} {p : x ≡ y} {q : y ≡ z} →
        ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap∙ {f = f} {x} {y} {z} {p} {q} j i =
  hcomp (λ k → λ {(i = i0) → f x;
                  (i = i1) → f (q k);
                  (j = i0) → f (transitivity-square p q i k);
                  (j = i1) → transitivity-square (ap f p) (ap f q) i k})
        (f (p i))


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


-- Transitivity laws for dependent paths. All those equalities lie over the
-- corresponding equalities for non-dependent paths.
private
  transitivity-square-d : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C}
                            {x : A} {y : B} {z : C}
                            (p : x ≡[ P ]≡ y) (q : y ≡[ Q ]≡ z) →
                            (i j : I) → transitivity-square P Q i j
  transitivity-square-d {P = P} {Q} {x} p q i =
    fill (λ j → transitivity-square P Q i j) _
         (λ j → λ {(i = i0) → x; (i = i1) → q j}) (inc (p i))

  diagonal-square-d : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C}
                        {x : A} {y : B} {z : C}
                        (p : x ≡[ P ]≡ y) (q : y ≡[ Q ]≡ z) →
                        (i j : I) → diagonal-square P Q i j
  diagonal-square-d {P = P} {Q} p q i j =
    comp (hfill (λ k → λ {(i = i0) → P j;
                          (j = i0) → P i;
                          (i = i1) → Q (j ∧ k);
                          (j = i1) → Q (i ∧ k)})
                (inc (P (i ∨ j)))) _
         (λ k → λ {(i = i0) → p j;
                   (j = i0) → p i;
                   (i = i1) → q (j ∧ k);
                   (j = i1) → q (i ∧ k)})
         (p (i ∨ j))


d∙refl : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} {p : x ≡[ P ]≡ y} →
           p d∙d refl ≡[ ap (λ P → x ≡[ P ]≡ y) ∙refl ]≡ p
d∙refl {p = p} i j = transitivity-square-d p refl j (1- i)


refl∙d : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} {p : x ≡[ P ]≡ y} →
           refl d∙d p ≡[ ap (λ P → x ≡[ P ]≡ y) refl∙ ]≡ p
refl∙d {A = A} {P = P} {x = x} {p = p} j i =
  comp (hfill (λ k → λ {(i = i0) → A;
                        (i = i1) → P k;
                        (j = i1) → P (i ∧ k)})
              (inc A)) _
       (λ k → λ {(i = i0) → x;
                 (i = i1) → p k;
                 (j = i1) → p (i ∧ k)})
       x


-d∙d-⁻¹ : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} {p : x ≡[ P ]≡ y} →
            p d∙d p ⁻¹ ≡[ ap (λ P → x ≡[ P ]≡ x) -∙-⁻¹ ]≡ refl
-d∙d-⁻¹ {A = A} {P = P} {x = x} {p = p} j i =
  comp (hfill (λ k → λ {(j = i1) → A;
                        (i = i0) → A;
                        (i = i1) → P (1- j ∧ 1- k)})
              (inc (P (1- j ∧ i)))) _
       (λ k → λ {(j = i1) → x;
                 (i = i0) → x;
                 (i = i1) → p (1- j ∧ 1- k)})
       (p (1- j ∧ i))

-⁻¹d∙d- : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} {p : x ≡[ P ]≡ y} →
            p ⁻¹ d∙d p ≡[ ap (λ P → y ≡[ P ]≡ y) -⁻¹∙- ]≡ refl
-⁻¹d∙d- = -d∙d-⁻¹


private
  assoc-cube-back-d : ∀ {l} {A B C : Set l} {P : A ≡ B} {Q : B ≡ C}
                        {x : A} {y : B} {z : C} (p : x ≡[ P ]≡ y) (q : y ≡[ Q ]≡ z) →
                        (i j : I) → assoc-cube-back P Q i j
  assoc-cube-back-d {P = P} {Q} p q i j =
    comp (hfill (λ k → λ {(i = i0) → Q (j ∧ k);
                          (j = i0) → P (1- i);
                          (j = i1) → Q k})
                (inc (P (1- i ∨ j)))) _
         (λ k → λ {(i = i0) → q (j ∧ k);
                   (j = i0) → p (1- i);
                   (j = i1) → q k})
         (p (1- i ∨ j))

-- Associativity.
∙∙d : ∀ {l} {A B C D : Set l} {P : A ≡ B} {Q : B ≡ C} {R : C ≡ D}
        {x : A} {y : B} {z : C} {w : D} {p : x ≡[ P ]≡ y}
        {q : y ≡[ Q ]≡ z} {r : z ≡[ R ]≡ w} →
        (p d∙d q) d∙d r ≡[ ap (λ P → x ≡[ P ]≡ w) ∙∙ ]≡ p d∙d (q d∙d r)
∙∙d {A = A} {P = P} {Q} {R} {x = x} {p = p} {q} {r} j i =
  comp (hfill (λ k → λ {(i = i0) → A;
                        (i = i1) → assoc-cube-back Q R j k})
              (inc (transitivity-square P Q i (1- j)))) _
       (λ k → λ {(i = i0) → x;
                 (i = i1) → assoc-cube-back-d q r j k})
       (transitivity-square-d p q i (1- j))




-- Heterogeneous equality.
-- It is important that the dependent path lies over a path in the indexing
-- family A, and not just over a path in the universe, because this allows
-- to forget the underlying path whenever A is a set.
infix 5 _≅_
infix 4 _,≅_
record _≅_ {l m} {A : Set l} {B : A → Set m} {a b : A} (x : B a) (y : B b) : Set (l ⊔ m) where
  constructor _,≅_
  field
    fst : a ≡ b
    snd : x ≡[ ap B fst ]≡ y

open _≅_ public


-- The downside is that most of the time, B needs to be specified.
≅-syntax = _≅_
infix 5 ≅-syntax
syntax ≅-syntax {B = B} x y = x ≅⟨ B ⟩ y


refl≅ : ∀ {l m} {A : Set l} {B : A → Set m} {a : A} {x : B a} → x ≅⟨ B ⟩ x
refl≅ = refl ,≅ refl

_≅⁻¹ : ∀ {l m} {A : Set l} {B : A → Set m} {a b : A} {x : B a} {y : B b} →
       x ≅⟨ B ⟩ y → y ≅⟨ B ⟩ x
(p ,≅ q) ≅⁻¹ = p ⁻¹ ,≅ q ⁻¹

infixr 6 _∙≅_
_∙≅_ : ∀ {l m} {A : Set l} {B : A → Set m} {a b c : A}
         {x : B a} {y : B b} {z : B c} →
         x ≅⟨ B ⟩ y → y ≅⟨ B ⟩ z → x ≅⟨ B ⟩ z
_∙≅_ {B = B} {x = x} {z = z} (p ,≅ q) (r ,≅ s) =
  p ∙ r ,≅
  tr (λ P → x ≡[ P ]≡ z)
     (ap∙ {f = B} ⁻¹)
     (q d∙d s)


≡-to-≅ : ∀ {l m} {A : Set l} {B : A → Set m} {a : A} {x y : B a} →
           x ≡ y → x ≅⟨ B ⟩ y
≡-to-≅ p = refl ,≅ p

≡[]-to-≅ : ∀ {l m} {A : Set l} {B : A → Set m} {a b : A} {x : B a} {y : B b}
             {P : a ≡ b} → x ≡[ ap B P ]≡ y → x ≅⟨ B ⟩ y
≡[]-to-≅ {P = P} p = P ,≅ p
