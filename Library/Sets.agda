{-# OPTIONS --safe --cubical #-}

{-
  Mere propositions and sets.
-}

module Library.Sets where

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (primIMin to _∧_;
            primIMax to _∨_;
            primINeg to 1-_;
            primComp to comp;
            primHComp to hcomp;
            primTransp to transp;
            itIsOne to 1=1)
open import Library.Equality


-- Definitions.
isProp : ∀ {l} → Set l → Set l
isProp A = (x y : A) → x ≡ y

isSet : ∀ {l} → Set l → Set l
isSet A = {x y : A} → isProp (x ≡ y)


-- In a mere proposition, any two points can be joined by a path
-- which furthermore coincides with an arbitrary partial path.
isPropPartial : ∀ {l} {A : Set l} → isProp A →
                   (x y : A) {φ : I} (p : Partial φ (x ≡ y)) →
                   (x ≡ y) [ φ ↦ p ]
isPropPartial H x y {φ} p = inc λ i →
  hcomp (λ j → λ {(i = i0) → H x x j;
                  (i = i1) → H y y j;
                  (φ = i1) → H (H x y i) (p 1=1 i) j})
        (H x y i)

isSetPartial : ∀ {l} {A : Set l} → isSet A →
                 {x y : A} (p q : x ≡ y) {φ : I} (α : Partial φ (p ≡ q)) →
                 (p ≡ q) [ φ ↦ α ]
isSetPartial H = isPropPartial H


-- A proposition is a set.
PropisSet : ∀ {l} {A : Set l} → isProp A → isSet A
PropisSet H {x} {y} p q i j =
  ouc (isPropPartial H (p j) (q j) (λ {(j = i0) → refl; (j = i1) → refl})) i


-- The proposition and set predicates are themselves propositions.
isPropisProp : ∀ {l} {A : Set l} → isProp (isProp A)
isPropisProp P Q i x y = PropisSet P (P x y) (Q x y) i

isPropisSet : ∀ {l} {A : Set l} → isProp (isSet A)
isPropisSet P Q i {x} {y} = isPropisProp (P {x} {y}) (Q {x} {y}) i



-- A dependent path which lies over some p : x ≡ y in a set can
-- be transformed into a path over any other q : x ≡ y.
change-underlying : ∀ {l m} {A : Set l} {B : A → Set m} →
                      isSet A →
                      {a b : A} {p q : a ≡ b} {x : B a} {y : B b} →
                      x ≡[ ap B p ]≡ y → x ≡[ ap B q ]≡ y
change-underlying {B = B} H {p = p} {q} {x} {y} r =
  tr (λ P → x ≡[ ap B P ]≡ y) (H p q) r

-- As a special case of the previous lemma, a path which lies over a loop
-- in a set can be made non-dependent
make-non-dependent : ∀ {l m} {A : Set l} {B : A → Set m} →
                      isSet A →
                      {a : A} {p : a ≡ a} {x y : B a} →
                      x ≡[ ap B p ]≡ y → x ≡ y
make-non-dependent {B = B} H r = change-underlying {B = B} H r

-- Those two lemmas work well together with heterogeneous equality.
≅-to-≡[] : ∀ {l m} {A : Set l} {B : A → Set m} →
             isSet A →
             {a b : A} {x : B a} {y : B b} →
             x ≅[ B ] y → {P : a ≡ b} → x ≡[ ap B P ]≡ y
≅-to-≡[] {B = B} H p = change-underlying {B = B} H (snd p)

≅-to-≡ : ∀ {l m} {A : Set l} {B : A → Set m} →
           isSet A →
           {a : A} {x y : B a} → x ≅[ B ] y → x ≡ y
≅-to-≡ {B = B} H p = make-non-dependent {B = B} H (snd p)



-- If B is a proposition indexed by A, then B is also a proposition up to
-- dependent paths, that is if a ≡ b : A, then any two elements of B a and
-- B b are equal.
isPropDependent : ∀ {l m} {A : Set l} {B : A → Set m} →
                     ({x : A} → isProp (B x)) →
                     {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
                     x ≡[ ap B p ]≡ y
isPropDependent {B = B} H p x y = trfill B p x d∙ H _ y

-- Similar lemma, but with I as indexing set.
isPropPath : ∀ {l} {B : I → Set l} →
                ({i : I} → isProp (B i)) →
                (x : B i0) (y : B i1) →
                PathP B x y
isPropPath {B = B} H x y = (λ k → B k) *fill x d∙ H _ y


-- Similar result for sets.
isSetPath : ∀ {l} {B : I → Set l} →
              ({i : I} → isSet (B i)) →
              {x : B i0} {y : B i1} (p q : PathP B x y) →
              p ≡ q
isSetPath {B = B} H {x} {y} p q j i =
  -- The idea is to split the dependent paths in two:
  let -- The first part is a dependent path, but is the same for both p and q
      t : (i : I) → B i
      t = fill B i0 (λ k ()) (inc x)
      -- The second part is non-dependent, and allows to use the hypothesis that
      -- B is a set.
      -- The definition is almost like the composition of r⁻¹ and t,
      -- but we ensure that the underlying path is constant.
      side-square : PathP B x y → (i j : I) → B (1- i ∨ j)
      side-square r i = fill (λ j → B (1- i ∨ j)) _
                             (λ j → λ {(i = i0) → y;
                                       (i = i1) → t j})
                             (inc (r (1- i)))
      side-edge : PathP B x y → I → B i1
      side-edge r i = side-square r i i1
  in comp (λ k → B (1- k ∨ i)) _
          (λ k → λ {(i = i0) → t (1- k);
                    (i = i1) → y;
                    (j = i0) → side-square p (1- i) (1- k);
                    (j = i1) → side-square q (1- i) (1- k)})
          (H (λ k → side-edge p (1- k))
             (λ k → side-edge q (1- k))
             j i)

-- This version assumes a common underlying path.
isSetDependent : ∀ {l m} {A : Set l} {B : A → Set m} →
                    ({x : A} → isSet (B x)) →
                    {a b : A} {p : a ≡ b} {x : B a} {y : B b} →
                    isProp (x ≡[ ap B p ]≡ y)
isSetDependent {B = B} H {a} {b} {p} {x} {y} r s j i =
  isSetPath {B = λ i → B (p i)} H r s j i

-- This version assumes that the indexing type is a set.
isSetDependent2 :
  ∀ {l m} {A : Set l} {B : A → Set m} →
    (HA : isSet A) → ({x : A} → isSet (B x)) →
    {a b : A} {p q : a ≡ b} {x : B a} {y : B b}
    (r : x ≡[ ap B p ]≡ y) (s : x ≡[ ap B q ]≡ y) →
    r ≡[ ap (λ p → x ≡[ ap B p ]≡ y) (HA p q) ]≡ s
isSetDependent2 {B = B} HA HB {p = p} {q} {x} {y} r s =
  trfill (λ p → x ≡[ ap B p ]≡ y) (HA p q) r
  d∙ isSetDependent {B = B} HB (tr (λ p → x ≡[ ap B p ]≡ y) (HA p q) r) s


{- Fill a square in a set given all edges
       s
    b_____d
    |     |
  p |     | q
    |_____|
    a  r  c
-}
isSetFillDependentSquare :
  ∀ {l} {A : I → I → Set l} → (∀ {i j} → isSet (A i j)) →
    {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
    (p : a ≡[ (λ j → A i0 j) ]≡ b) (q : c ≡[ (λ j → A i1 j) ]≡ d)
    (r : a ≡[ (λ i → A i i0) ]≡ c) (s : b ≡[ (λ i → A i i1) ]≡ d) →
    (i j : I) → (A i j) [ (i ∨ j ∨ 1- i ∨ 1- j) ↦
                          (λ {(i = i0) → p j; (i = i1) → q j;
                              (j = i0) → r i; (j = i1) → s i}) ]
isSetFillDependentSquare {A = A} H p q r s i j =
  let base : (i j : I) → A i j
      base i = fill (A i) _
                    (λ {j (i = i0) → p j;
                        j (i = i1) → q j})
                    (inc (r i))
  in inc (comp (λ _ → A i j) _
                (λ k → λ {(i = i0) → p j;
                          (i = i1) → q j;
                          (j = i0) → r i;
                          (j = i1) → isSetPath H (λ i → base i i1) s k i})
                (base i j))


square-filler : ∀ {l} {A : Set l} {a b c d : A}
                  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) →
                  Setω
square-filler {A = A} p q r s = (i j : I) →
  A [ (i ∨ j ∨ 1- i ∨ 1- j) ↦
      (λ {(i = i0) → p j; (i = i1) → q j;
          (j = i0) → r i; (j = i1) → s i}) ]

-- In a set, it is always possible to fill a square as above.
isSetFillSquare : ∀ {l} {A : Set l} → isSet A → {a b c d : A}
                      (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) →
                      square-filler p q r s
isSetFillSquare {A = A} H p q r s i j =
  inc (hcomp (λ k → λ {(i = i0) → p (j ∨ 1- k);
                       (i = i1) → q j;
                       (j = i0) → transitivity-square (r ⁻¹) p (1- i) (1- k);
                       (j = i1) → H ((r ⁻¹ ∙ p) ⁻¹ ∙ q) s k i})
             (transitivity-square ((r ⁻¹ ∙ p) ⁻¹) q i j))


-- Furthermore, the square can be filled by extending a partial square.
isSetFillPartialSquare : ∀ {l} {A : Set l} → isSet A →
  {a b c d : A} (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) →
  {φ : I} (u : (IsOne φ) → square-filler p q r s) → (i j : I) →
  A [ i ∨ 1- i ∨ j ∨ 1- j ∨ φ ↦
    (λ {(i = i0) → p j; (i = i1) → q j;
        (j = i0) → r i; (j = i1) → s i;
        (φ = i1) → ouc (u 1=1 i j)}) ]
isSetFillPartialSquare H p q r s {φ} u i j =
  inc (hcomp (λ k → λ {(i = i0) → p j; (i = i1) → q j;
                       (j = i0) → H r r k i; (j = i1) → H s s k i;
                       (φ = i1) → H (λ i → ouc (isSetFillSquare H p q r s i j))
                                    (λ i → ouc (u 1=1 i j)) k i})
             (ouc (isSetFillSquare H p q r s i j)))



isProp⇒ : ∀ {l m} {A : Set l} {B : A → Set m} →
            ({x : A} → isProp (B x)) → isProp ((x : A) → B x)
isProp⇒ {A = A} {B} H f g i x = H (f x) (g x) i

isSet⇒ : ∀ {l m} {A : Set l} {B : A → Set m} →
           ({x : A} → isSet (B x)) → isSet ((x : A) → B x)
isSet⇒ {A = A} {B} H {f} {g} p q i j x =
  let px = λ k → p k x
      qx = λ k → q k x
  in H px qx i j
