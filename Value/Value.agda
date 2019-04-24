{-# OPTIONS --safe --cubical #-}

{-
  Definition of values and environments.
-}

module Value.Value where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Weakening.Variable


-- Values and environments (list of values) are mutually defined.
data Val : Con → Ty → Set
data NV : Con → Ty → Set
-- Do NOT define this using Syntax.List
-- lists are defined using records (⊤ and Σ), which mess up the termination
-- checker with --without-K, requiring some ugly and annoying hacks to even
-- define embeddings.
-- cf https://github.com/agda/agda/issues/1680
-- Note that this issue is specific to values, due to the closure constructor
-- having an environment values as argument (values have a tree structure).
-- For variables, normal forms, ... the lists of X can be defined after X,
-- and the issue does not exist.
data Env : Con → Con → Set

⌜_⌝V : {Γ : Con} {A : Ty} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty} → NV Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ

-- A value is a λ-closure or a neutral value.
data Val where
  lam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ (A ⟶ B)
  neu : {Γ : Con} {A : Ty} → NV Γ A → Val Γ A
  veq : {Γ : Con} {A : Ty} {u v : Val Γ A} → ⌜ u ⌝V ≡ ⌜ v ⌝V → u ≡ v
  isSetVal : {Γ : Con} {A : Ty} → isSet (Val Γ A)

data NV where
  var : {Γ : Con} {A : Ty} → Var Γ A → NV Γ A
  app : {Γ : Con} {A B : Ty} → NV Γ (A ⟶ B) → Val Γ A → NV Γ B

infixl 10 _,_
data Env where
  ε : {Γ : Con} → Env Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → Env Γ Δ → Val Γ A → Env Γ (Δ , A)


-- Embeddings.
⌜ lam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ neu n ⌝V = ⌜ n ⌝NV
⌜ veq p i ⌝V = p i
⌜ isSetVal p q i j ⌝V = isSetTm (λ k → ⌜ p k ⌝V) (λ k → ⌜ q k ⌝V) i j
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V

