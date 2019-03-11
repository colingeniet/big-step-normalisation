{-# OPTIONS --safe --cubical #-}

module Library.Nat.Sets where

open import Agda.Builtin.Nat
open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.Negation
open import Library.NotEqual


discreteNat : Discrete Nat
discreteNat zero zero = yes refl
discreteNat zero (suc n) = no λ p → ⊤≢⊥ (ap (λ {zero → ⊤; (suc _) → ⊥}) p)
discreteNat (suc n) zero = no λ p → ⊤≢⊥ (ap (λ {zero → ⊥; (suc _) → ⊤}) p)
discreteNat (suc n) (suc m)
  with discreteNat n m
...  | yes p = yes (ap suc p)
...  | no np = no λ p → np (ap (λ {zero → zero; (suc n) → n}) p)
