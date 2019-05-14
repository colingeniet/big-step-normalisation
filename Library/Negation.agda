{-# OPTIONS --safe --without-K #-}

module Library.Negation where

open import Agda.Primitive

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()


¬ : ∀ {l} (A : Set l) → Set l
¬ A = A → ⊥
