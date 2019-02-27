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



isprop-dependent : ∀ {l m} {A : Set l} {B : A → Set m} →
                     ({x : A} → isProp (B x)) →
                     {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
                     x ≡[ ap B p ]≡ y
isprop-dependent {B = B} H p x y = trfill B p x d∙ H (tr B p x) y

{-
test1 : ∀ {l m} {A : Set l} {B : A → Set m} →
          ({x : A} → isSet (B x)) →
          {a b : A} (p : a ≡ b) (x : B a) (y : B b) →
          isProp (x ≡[ ap B p ]≡ y)
test1 {B = B} H p x y r s = {!!}

test2 : ∀ {l m} {A : Set l} {B : A → Set m} →
          ({x : A} → isSet (B x)) →
          {a b : A} {p q : a ≡ b} (α : p ≡ q)
          {x : B a} {y : B b} (r : x ≡[ ap B p ]≡ y) (s : x ≡[ ap B q ]≡ y) →
          r ≡[ ap (λ p → x ≡[ ap B p ]≡ y) α ]≡ s
test2 {B = B} H {p = p} {q} α {x} {y} r s =
  trfill (λ p → x ≡[ ap B p ]≡ y) α r
  d∙ test1 H q x y (tr (λ p → x ≡[ ap B p ]≡ y) α r) s
-}

