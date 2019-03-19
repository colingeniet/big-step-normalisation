{-# OPTIONS --safe --cubical #-}

-- Definition of generalised weakening.

module Syntax.Weakening where

open import Library.Equality
open import Syntax.Types
open import Syntax.Terms
open import Syntax.Terms.Lemmas

-- Definition
data Wk : Con → Con → Set where
  nil : Wk ● ●
  drop : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) Δ
  keep : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) (Δ , A)

-- Category
idw : {Γ : Con} → Wk Γ Γ
idw {●} = nil
idw {Δ , A} = keep A idw

_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ
σ ∘w nil = σ
σ ∘w (drop A ν) = drop A (σ ∘w ν)
(drop A σ) ∘w (keep A ν) = drop A (σ ∘w ν)
(keep A σ) ∘w (keep A ν) = keep A (σ ∘w ν)

id∘w : {Γ Δ : Con} {σ : Wk Γ Δ} → idw ∘w σ ≡ σ
id∘w {σ = nil} = refl
id∘w {σ = drop A σ} = ap (drop A) id∘w
id∘w {σ = keep A σ} = ap (keep A) id∘w

∘idw : {Γ Δ : Con} {σ : Wk Γ Δ} → σ ∘w idw ≡ σ
∘idw {σ = nil} = refl
∘idw {σ = drop A σ} = ap (drop A) ∘idw
∘idw {σ = keep A σ} = ap (keep A) ∘idw

∘∘w : {Γ Δ Θ Ψ : Con} {σ : Wk Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
∘∘w {δ = nil} = refl
∘∘w {δ = drop A δ} = ap (drop A) (∘∘w {δ = δ})
∘∘w {ν = drop A ν} {keep A δ} = ap (drop A) (∘∘w {δ = δ})
∘∘w {σ = drop A σ} {keep A ν} {keep A δ} = ap (drop A) (∘∘w {δ = δ})
∘∘w {σ = keep A σ} {keep A ν} {keep A δ} = ap (keep A) (∘∘w {δ = δ})

-- Embedding into substitutions
⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ
⌜ nil ⌝w = ε
⌜ drop A σ ⌝w = ⌜ σ ⌝w ∘ wk
⌜ keep A σ ⌝w = ⌜ σ ⌝w ↑ A

⌜id⌝w : {Γ : Con} → ⌜ idw {Γ} ⌝w ≡ id
⌜id⌝w {Γ = ●} = εη ⁻¹
⌜id⌝w {Γ = Γ , A} = ap (λ σ → σ ↑ A) ⌜id⌝w ∙ ↑id

⌜∘⌝w : {Γ Δ Θ : Con} {σ : Wk Δ Θ} {ν : Wk Γ Δ} → ⌜ σ ∘w ν ⌝w ≡ ⌜ σ ⌝w ∘ ⌜ ν ⌝w
⌜∘⌝w {σ = σ} {ν = nil} with σ
...                      | nil = εη ⁻¹
⌜∘⌝w {ν = drop A ν} = ap (λ σ → σ ∘ wk) ⌜∘⌝w ∙ ∘∘
⌜∘⌝w {σ = drop A σ} {ν = keep A ν} = ap (λ σ → σ ∘ wk) (⌜∘⌝w {σ = σ} {ν})
                                   ∙ ∘∘ ∙ ap (λ ν → ⌜ σ ⌝w ∘ ν) wk, ⁻¹ ∙ ∘∘ ⁻¹
⌜∘⌝w {σ = keep A σ} {ν = keep A ν} = ap (λ σ → σ ↑ A) (⌜∘⌝w {σ = σ} {ν})
                                   ∙ ap (λ σ → σ , vz) ∘∘
                                   ∙ ↑∘, {σ = ⌜ σ ⌝w} {ν = ⌜ ν ⌝w ∘ wk} {u = vz} ⁻¹
