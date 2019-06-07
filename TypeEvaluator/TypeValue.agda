{-# OPTIONS --cubical --safe #-}

module TypeEvaluator.TypeValue where

open import Library.Equality
open import Syntax.Terms
open import TypeEvaluator.Skeleton

-- Normalised (substitution free) types
data TV : TSk → Con → Set
⌜_⌝T : {S : TSk} {Γ : Con} → TV S Γ → Ty Γ

data TV where
  U : {Γ : Con} → TV U Γ
  El : {Γ : Con} → Tm Γ U → TV El Γ
  Π : {Γ : Con} {S T : TSk} (A : TV S Γ) (B : TV T (Γ , ⌜ A ⌝T)) → TV (Π S T) Γ

⌜ U ⌝T = U
⌜ El u ⌝T = El u
⌜ Π A B ⌝T = Π ⌜ A ⌝T ⌜ B ⌝T


skeleton⌜⌝T : {S : TSk} {Γ : Con} {A : TV S Γ} → skeleton ⌜ A ⌝T ≡ S
skeleton⌜⌝T {A = U} = refl
skeleton⌜⌝T {A = El u} = refl
skeleton⌜⌝T {A = Π A B} = ap2 Π (skeleton⌜⌝T {A = A}) (skeleton⌜⌝T {A = B})
