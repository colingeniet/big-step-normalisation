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

-- A proposition is a set.
PropisSet : ∀ {l} {A : Set l} → isProp A → isSet A
PropisSet isprop {x} {y} p q j i =
  hcomp (λ k → λ {(i = i0) → isprop x x k;
                  (i = i1) → isprop x y k;
                  (j = i0) → isprop x (p i) k;
                  (j = i1) → isprop x (q i) k})
        x

-- The proposition and set predicates are themselves propositions.
isPropisProp : ∀ {l} {A : Set l} → isProp (isProp A)
isPropisProp P Q i x y = PropisSet P (P x y) (Q x y) i

isPropisSet : ∀ {l} {A : Set l} → isProp (isSet A)
isPropisSet P Q i {x} {y} = isPropisProp (P {x} {y}) (Q {x} {y}) i



-- If B is a proposition indexed by A, then B is also a proposition up to
-- dependent paths, that is if a ≡ b : A, then any two elements of B a and
-- B b are equal.
isprop-dependent : ∀ {l m} {A : Set l} {B : A → Set m} →
                     ({x : A} → isProp (B x)) →
                     {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
                     x ≡[ ap B p ]≡ y
isprop-dependent {B = B} H p x y = trfill B p x d∙ H (tr B p x) y

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

-- Those two lemmas are work well together with heterogeneous equality.
≅-to-≡[] : ∀ {l m} {A : Set l} {B : A → Set m} →
             isSet A →
             {a b : A} {x : B a} {y : B b} →
             x ≅⟨ B ⟩ y → {P : a ≡ b} → x ≡[ ap B P ]≡ y
≅-to-≡[] {B = B} H p = change-underlying {B = B} H (snd p)

≅-to-≡ : ∀ {l m} {A : Set l} {B : A → Set m} →
           isSet A →
           {a : A} {x y : B a} → x ≅⟨ B ⟩ y → x ≡ y
≅-to-≡ {B = B} H p = make-non-dependent {B = B} H (snd p)


{-
test1 : ∀ {l m} {A : Set l} {B : A → Set m} →
          isSet A →
          ({x : A} → isSet (B x)) →
          {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
          isProp (x ≡[ ap B p ]≡ y)
test1 {B = B} HA HB {a} {b} p x y r s =
  let rs = r d∙d s ⁻¹ in
  let rs' = tr (λ P → x ≡[ P ]≡ x) -∙-⁻¹ rs in
  let rs≡rs' = trfill (λ P → x ≡[ P ]≡ x) -∙-⁻¹ rs in
  let rs'≡refl = HB rs' refl in
  let rs≡refl = rs≡rs' d∙ rs'≡refl in
  let r≡s = d∙refl ⁻¹
            d∙d apd (λ s → r d∙d s)  -⁻¹d∙d- ⁻¹
            d∙d ∙∙d ⁻¹
            d∙d apd (λ p → p d∙d s) rs≡refl
            d∙d refl∙d
  in
  {!!}

test2 : ∀ {l m} {A : Set l} {B : A → Set m} →
          (HA : isSet A) →
          ({x : A} → isSet (B x)) →
          {a b : A} {p q : a ≡ b}
          {x : B a} {y : B b} (r : x ≡[ ap B p ]≡ y) (s : x ≡[ ap B q ]≡ y) →
          r ≡[ ap (λ p → x ≡[ ap B p ]≡ y) (HA p q) ]≡ s
test2 {B = B} HA HB {p = p} {q} {x} {y} r s =
  trfill (λ p → x ≡[ ap B p ]≡ y) (HA p q) r
  d∙ test1 HA HB q x y (tr (λ p → x ≡[ ap B p ]≡ y) (HA p q) r) s
-}
