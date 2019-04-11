{-# OPTIONS --safe --cubical #-}

module Syntax.Terms.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Weakening.Weakening


_+t_ : {Γ Δ : Con} {A : Ty} → Tm Δ A → Wk Γ Δ → Tm Γ A
u +t σ = u [ ⌜ σ ⌝w ]

+tid : {Γ : Con} {A : Ty} {u : Tm Γ A} → u +t idw ≡ u
+tid = ap (λ σ → _ [ σ ]) ⌜id⌝w ∙ [id]

+t∘ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      u +t (σ ∘w ν) ≡ (u +t σ) +t ν
+t∘ = ap (λ σ → _ [ σ ]) ⌜∘⌝w ∙ [][]

_+s_ : {Γ Δ Θ : Con} → Tms Δ Θ → Wk Γ Δ → Tms Γ Θ
σ +s ν = σ ∘ ⌜ ν ⌝w

+sid : {Γ Δ : Con} {σ : Tms Γ Δ} → σ +s idw ≡ σ
+sid = ap (λ ν → _ ∘ ν) ⌜id⌝w ∙ ∘id

+s∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      σ +s (ν ∘w δ) ≡ (σ +s ν) +s δ
+s∘ = ap (λ σ → _ ∘ σ) ⌜∘⌝w ∙ ∘∘ ⁻¹

[]+ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Tms Δ Θ} {ν : Wk Γ Δ} →
      u [ σ +s ν ] ≡ u [ σ ] +t ν
[]+ = [][]
