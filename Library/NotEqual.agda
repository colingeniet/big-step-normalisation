{-# OPTIONS --safe --cubical #-}

module Library.NotEqual where

-- Proofs of disequality.

open import Agda.Primitive
open import Library.Equality public
open import Agda.Builtin.Unit public
open import Library.Negation public


⊤≢⊥ : ¬ (⊤ ≡ ⊥)
⊤≢⊥ p = p * tt
