{-# OPTIONS --safe --without-K #-}

module Library.Union where

open import Agda.Primitive


infixr 4 _+_
data _+_ {l m} (A : Set l) (B : Set m) : Set (l ⊔ m) where
  inl : A → A + B
  inr : B → A + B


+-elim : ∀ {l m n} {A : Set l} {B : Set m} {C : A + B → Set n} →
           ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
           (x : A + B) → C x
+-elim f g (inl x) = f x
+-elim f g (inr x) = g x
