{-# OPTIONS --safe --cubical #-}

{-
  Definition of values and environments.
-}

module Normalisation.Values where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.NeutralForms public


-- Values and environments (list of values) are mutually defined.
data Val : Tm-like

Env : Tms-like
Env = list Val

⌜_⌝V : {Γ : Con} {A : Ty} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty} → Ne Val Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ

-- A value is a λ-closure or a neutral value.
data Val where
  lam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ (A ⟶ B)
  neu : {Γ : Con} {A : Ty} → Ne Val Γ A → Val Γ A
  veq : {Γ : Con} {A : Ty} {u v : Val Γ A} → ⌜ u ⌝V ≡ ⌜ v ⌝V → u ≡ v
  isSetVal : {Γ : Con} {A : Ty} → isSet (Val Γ A)

-- Embeddings.
⌜ lam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ neu n ⌝V = ⌜ n ⌝NV
⌜ veq p i ⌝V = p i
⌜ isSetVal p q i j ⌝V = isSetTm (λ k → ⌜ p k ⌝V) (λ k → ⌜ q k ⌝V) i j
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V
