{-# OPTIONS --cubical --safe #-}

module TypeEvaluator.TypeValue where

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
