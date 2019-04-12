{-# OPTIONS --cubical --safe #-}

module Weakening.Variable.Presheaf where

open import Library.Equality
open import Syntax.Types
open import Weakening.Variable
open import Weakening.Presheaf
open import Weakening.Variable.Sets
open import Syntax.Terms.Presheaf

-- Variables and weakenings form presheaves over the category of weakenings.
-- (for weakenings, this is just the Yoneda embedding)

Var' : Ty → Pshw
(Var' A) $o Γ = Var Γ A
isSetapply (Var' A) = isSetVar
x +⟨ Var' A ⟩ σ = x +v σ
+id (Var' A) = +vid
+∘ (Var' A) {x = x} {σ} {ν} = +v∘ {x = x} {σ} {ν}

Wk' : Con → Pshw
(Wk' Δ) $o Γ = Wk Γ Δ
isSetapply (Wk' Δ) = isSetWk
σ +⟨ Wk' Δ ⟩ ν = σ ∘w ν
+id (Wk' Δ) = ∘idw
+∘ (Wk' Δ) = ∘∘w ⁻¹

-- Embeddings are natural transformations.
embv : {A : Ty} → Natw (Var' A) (Tm' A)
act embv _ x = ⌜ x ⌝v
nat embv = ⌜⌝+v

embw : {Δ : Con} → Natw (Wk' Δ) (Tms' Δ)
act embw _ σ = ⌜ σ ⌝w
nat embw = ⌜∘⌝w
