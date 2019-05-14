{-# OPTIONS --safe --cubical #-}

module Library.Negation.Proposition where

open import Agda.Primitive
open import Library.Negation
open import Library.Equality
open import Library.Sets


isProp⊥ : isProp ⊥
isProp⊥ ()

isProp¬ : ∀ {l} {A : Set l} → isProp (¬ A)
isProp¬ {A = A} f g i x = isProp⊥ (f x) (g x) i
