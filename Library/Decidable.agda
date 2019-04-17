{-# OPTIONS --safe --cubical #-}

module Library.Decidable where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Negation
open import Library.Negation.Proposition
open import Library.Union


data Decidable {l} (A : Set l) : Set l where
  yes : A → Decidable A
  no : ¬ A → Decidable A

Discrete : ∀ {l} → Set l → Set l
Discrete A = (x y : A) → Decidable (x ≡ y)


-- Hedberg's theorem.
private
  -- It is always possible to define a constant map
  -- of a decidable type into itself.
  const : ∀ {l} {A : Set l} → Decidable A → A → A
  const (yes a) _ = a
  const (no n) y = ⊥-elim (n y)

  isconst : ∀ {l} {A : Set l} (H : Decidable A) (x y : A) →
              const H x ≡ const H y
  isconst (yes a) x y i = a
  isconst (no n) x = ⊥-elim (n x)

  -- If that map has a left inverse, then the type is a mere proposition.
  constinv⇒isProp : ∀ {l} {A : Set l} (H : Decidable A)
                      (g : A → A) → ((x : A) → g (const H x) ≡ x) →
                      isProp A
  constinv⇒isProp (yes a) g ginv x y = ginv x ⁻¹ ∙ ginv y
  constinv⇒isProp (no n) g ginv x = ⊥-elim (n x)


  -- And any map x≡y → x≡y has a left inverse.
  ≡map-inv : ∀ {l} {A : Set l} (f : {x y : A} → x ≡ y → x ≡ y) →
               {x y : A} → x ≡ y → x ≡ y
  ≡map-isinv : ∀ {l} {A : Set l} (f : {x y : A} → x ≡ y → x ≡ y) →
                 {x y : A} (p : x ≡ y) → ≡map-inv f (f p) ≡ p
  ≡map-inv f {x} p = f (refl {x = x}) ⁻¹ ∙ p
  ≡map-isinv f {x} = J (λ p → ≡map-inv f (f p) ≡ p) -⁻¹∙-


DiscreteisSet : ∀ {l} {A : Set l} → Discrete A → isSet A
DiscreteisSet discrete {x} {y} =
  let c = λ {x} {y} → const (discrete x y)
      invc = ≡map-inv c
      isinvc = ≡map-isinv c
  in constinv⇒isProp (discrete x y) invc isinvc
