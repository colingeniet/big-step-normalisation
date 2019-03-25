{-# OPTIONS --safe --cubical #-}

module Library.Maybe where

open import Agda.Primitive
open import Library.Equality
open import Library.Negation
open import Library.NotEqual


data Maybe {l} (A : Set l) : Set l where
  yes : A → Maybe A
  no : Maybe A


maybe-lift : ∀ {l m} {A : Set l} {B : Set m} →
               (A → B) → Maybe A → Maybe B
maybe-lift _ no = no
maybe-lift f (yes x) = yes (f x)

maybe-bind : ∀ {l m} {A : Set l} {B : Set m} →
               (A → Maybe B) → Maybe A → Maybe B
maybe-bind _ no = no
maybe-bind f (yes x) = f x


yes-injective : ∀ {l} {A : I → Set l} {x : A i0} {y : A i1} →
                  PathP (λ i → Maybe (A i)) (yes x) (yes y) → PathP A x y
yes-injective {A = A} {x} p i =
  yes-elim (p i) partial
  where partial : PathP (λ j → Maybe (A (i ∧ j))) (yes x) (p i)
        partial j = p (i ∧ j)
        yes-elim : ∀ {i} (z : Maybe (A i)) → PathP (λ j → Maybe (A (i ∧ j))) (yes x) z → (A i)
        yes-elim (yes z) _ = z
        yes-elim no p = ⊥-elim (⊤≢⊥ (apd (λ {(yes _) → ⊤; no → ⊥}) p))
