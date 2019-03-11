{-# OPTIONS --safe --cubical #-}

module Syntax.Types.Sets where

open import Syntax.Types
open import Library.Equality
open import Library.Sets
open import Library.Decidable
open import Library.NotEqual

discreteTy : Discrete Ty
discreteTy o o = yes refl
discreteTy o (A ⟶ B) = no λ p → ⊤≢⊥ (ap (λ {o → ⊤; (_ ⟶ _) → ⊥}) p)
discreteTy (A ⟶ B) o = no λ p → ⊤≢⊥ (ap (λ {o → ⊥; (_ ⟶ _) → ⊤}) p)
discreteTy (A ⟶ B) (C ⟶ D)
  with discreteTy A C | discreteTy B D
...  | no n  | _     = no λ p → n (ap (λ {o → o; (A ⟶ _) → A}) p)
...  | yes p | yes q = yes (ap2 _⟶_ p q)
...  | yes p | no n  = no λ p → n (ap (λ {o → o; (_ ⟶ A) → A}) p)

isSetTy : isSet Ty
isSetTy = DiscreteisSet discreteTy
