{-# OPTIONS --safe --cubical #-}

module Syntax.Types.Sets where

open import Syntax.Types
open import Library.Equality
open import Library.Sets
open import Library.Decidable
open import Library.NotEqual

discreteTy : Discrete Ty
discreteTy o o = yes refl
discreteTy o (_ ⟶ _) = no λ p → ⊤≢⊥ (ap (λ {o → ⊤; (_ ⟶ _) → ⊥}) p)
discreteTy (_ ⟶ _) o = no λ p → ⊤≢⊥ (ap (λ {o → ⊥; (_ ⟶ _) → ⊤}) p)
discreteTy (A ⟶ B) (C ⟶ D)
  with discreteTy A C | discreteTy B D
...  | no n  | _     = no λ p → n (ap (λ {o → o; (A ⟶ _) → A}) p)
...  | yes p | no n  = no λ p → n (ap (λ {o → o; (_ ⟶ A) → A}) p)
...  | yes p | yes q = yes (ap2 _⟶_ p q)

discreteCon : Discrete Con
discreteCon ● ● = yes refl
discreteCon ● (_ , _) = no λ p → ⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p)
discreteCon (_ , _) ● = no λ p → ⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p)
discreteCon (Γ , A) (Δ , B)
  with discreteCon Γ Δ | discreteTy A B
...  | no n  | _     = no λ p → n (ap (λ {● → ●; (Γ , _) → Γ}) p)
...  | yes p | no n  = no λ p → n (ap (λ {● → o; (_ , A) → A}) p)
...  | yes p | yes q = yes (ap2 _,_ p q)


isSetTy : isSet Ty
isSetTy = DiscreteisSet discreteTy

isSetCon : isSet Con
isSetCon = DiscreteisSet discreteCon
