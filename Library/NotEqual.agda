{-# OPTIONS --safe --cubical #-}

module Library.NotEqual where

-- Proofs of disequality.

open import Agda.Primitive
open import Library.Equality public
open import Agda.Builtin.Unit public
open import Library.Negation public
open import Library.Bool public


⊤≢⊥ : ¬ (⊤ ≡ ⊥)
⊤≢⊥ p = p * tt

true≢false : ¬ (true ≡ false)
true≢false p = ⊤≢⊥ (ap (λ {true → ⊤; false → ⊥}) p)


≢-by-bool : ∀ {l} {A : Set l} (x y : A) (f : A → Bool) →
              f x ≡ true → f y ≡ false → ¬ (x ≡ y)
≢-by-bool x y f p q r = true≢false (p ⁻¹ ∙ ap f r ∙ q)
