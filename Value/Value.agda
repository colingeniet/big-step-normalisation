{-# OPTIONS --safe --cubical #-}

{-
  Definition of values and environments.
-}

module Value.Value where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Variable.Variable


-- Values and environments (list of values) are mutually defined.
data Val : (Γ : Con) → Ty Γ → Set
data NV : (Γ : Con) → Ty Γ → Set
data Env : Con → Con → Set

⌜_⌝V : {Γ : Con} {A : Ty Γ} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty Γ} → NV Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ

-- A value is a λ-closure or a neutral value.
data Val where
  lam : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
        (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ ((Π A B) [ ⌜ ρ ⌝E ]T)
  neu : {Γ : Con} {A : Ty Γ} → NV Γ A → Val Γ A
  veq : {Γ : Con} {A : Ty Γ} {u v : Val Γ A} → ⌜ u ⌝V ≡ ⌜ v ⌝V → u ≡ v
  isSetVal : {Γ : Con} {A : Ty Γ} → isSet (Val Γ A)

data NV where
  var : {Γ : Con} {A : Ty Γ} → Var Γ A → NV Γ A
  app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
        NV Γ (Π A B) → (v : Val Γ A) → NV Γ (B [ < ⌜ v ⌝V > ]T)

infixl 10 _,_
data Env where
  ε : {Γ : Con} → Env Γ ●
  _,_ : {Γ Δ : Con} {A : Ty Δ} → (ρ : Env Γ Δ) → Val Γ (A [ ⌜ ρ ⌝E  ]T) → Env Γ (Δ , A)


-- Embeddings.
⌜ lam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ neu n ⌝V = ⌜ n ⌝NV
⌜ veq p i ⌝V = p i
⌜ isSetVal p q i j ⌝V = isSetTm (λ k → ⌜ p k ⌝V) (λ k → ⌜ q k ⌝V) i j
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V
