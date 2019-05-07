{-# OPTIONS --safe --cubical #-}

module Syntax.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Lemmas
open import Weakening.Variable


_+t_ : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (σ : Wk Γ Δ) → Tm Γ (A [ ⌜ σ ⌝w ]T)
u +t σ = u [ ⌜ σ ⌝w ]

+tid : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → u +t idw ≅[ Tm Γ ] u
+tid {u = u} =
  u [ ⌜ idw ⌝w ] ≅⟨ apd (λ σ → u [ σ ]) ⌜idw⌝ ⟩
  u [ id ]      ≅⟨ [id] ⟩'
  u             ≅∎

+t∘ : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      u +t (σ ∘w ν) ≅[ Tm Γ ] (u +t σ) +t ν
+t∘ {u = u} {σ} {ν} =
  u [ ⌜ σ ∘w ν ⌝w ]      ≅⟨ apd (λ ρ → u [ ρ ]) ⌜∘⌝w ⟩
  u [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≅⟨ [][] ⟩'
  u [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≅∎

_+s_ : {Γ Δ Θ : Con} → Tms Δ Θ → Wk Γ Δ → Tms Γ Θ
σ +s ν = σ ∘ ⌜ ν ⌝w

+sid : {Γ Δ : Con} {σ : Tms Γ Δ} → σ +s idw ≡ σ
+sid {σ = σ} =
  σ ∘ ⌜ idw ⌝w ≡⟨ ap (λ ν → _ ∘ ν) ⌜idw⌝ ⟩
  σ ∘ id      ≡⟨ ∘id ⟩
  σ           ∎

+s∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      σ +s (ν ∘w δ) ≡ (σ +s ν) +s δ
+s∘ {σ = σ} {ν} {δ} =
  σ ∘ ⌜ ν ∘w δ ⌝w      ≡⟨ ap (λ σ → _ ∘ σ) ⌜∘⌝w ⟩
  σ ∘ (⌜ ν ⌝w ∘ ⌜ δ ⌝w) ≡⟨ ∘∘ ⁻¹ ⟩
  (σ ∘ ⌜ ν ⌝w) ∘ ⌜ δ ⌝w ∎

[]+ : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {σ : Tms Δ Θ} {ν : Wk Γ Δ} →
      u [ σ +s ν ] ≅[ Tm Γ ] u [ σ ] +t ν
[]+ {u = u} {σ} {ν} =
  u [ σ ∘ ⌜ ν ⌝w ]   ≅⟨ [][] ⟩'
  u [ σ ] [ ⌜ ν ⌝w ] ≅∎
