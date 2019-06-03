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


yes-injective : ∀ {l} {A : Set l} {x y : A} → yes x ≡ yes y → x ≡ y
yes-injective {A = A} {x} p i =
  yes-elim (p i) partial
  where partial : yes x ≡ p i
        partial j = p (i ∧ j)
        yes-elim : (z : Maybe A) → yes x ≡ z → A
        yes-elim (yes z) _ = z
        yes-elim no p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊤; no → ⊥}) p))

yes-injective-dependent : ∀ {l} {A B : Set l} {P : A ≡ B} {x : A} {y : B} →
                          yes x ≡[ ap Maybe P ]≡ yes y → x ≡[ P ]≡ y
yes-injective-dependent {l} {A} {B} {P} {x} p i =
  yes-elim (p i) partialP partial
  where partialP : A ≡ P i
        partialP j = P (i ∧ j)
        partial : yes x ≡[ ap Maybe partialP ]≡ p i
        partial j = p (i ∧ j)
        yes-elim : {C : Set l} (z : Maybe C) →
                   (Q : A ≡ C) → yes x ≡[ ap Maybe Q ]≡ z → C
        yes-elim (yes z) _ _ = z
        yes-elim no Q q = ⊥-elim (⊤≢⊥ (apd (λ {(yes _) → ⊤; no → ⊥}) q))

yes-injective≅ : ∀ {l m} {A : Set l} {B : A → Set m} {a b : A} {x : B a} {y : B b} →
                   yes x ≅[ (λ x → Maybe (B x)) ] yes y → x ≅[ B ] y
yes-injective≅ {A = A} {B} {a} {b} {x} {y} p =
  fst p ,≅ yes-injective-dependent (snd p)
