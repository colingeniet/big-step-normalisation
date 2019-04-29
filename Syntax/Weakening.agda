{-# OPTIONS --safe --cubical #-}

module Syntax.Terms.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Weakening.Variable.Base


_+t_ : {Γ Δ : Con} {A : Ty} → Tm Δ A → Wk Γ Δ → Tm Γ A
u +t σ = u [ ⌜ σ ⌝w ]

+tid : {Γ : Con} {A : Ty} {u : Tm Γ A} → u +t idw ≡ u
+tid {u = u} =
  u [ ⌜ idw ⌝w ] ≡⟨ ap (λ σ → u [ σ ]) ⌜id⌝w ⟩
  u [ id ]      ≡⟨ [id] ⟩
  u ∎

+t∘ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      u +t (σ ∘w ν) ≡ (u +t σ) +t ν
+t∘ {u = u} {σ} {ν} =
  u [ ⌜ σ ∘w ν ⌝w ]      ≡⟨ ap (λ ρ → u [ ρ ]) ⌜∘⌝w ⟩
  u [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ [][] ⟩
  u [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ∎

_+s_ : {Γ Δ Θ : Con} → Tms Δ Θ → Wk Γ Δ → Tms Γ Θ
σ +s ν = σ ∘ ⌜ ν ⌝w

+sid : {Γ Δ : Con} {σ : Tms Γ Δ} → σ +s idw ≡ σ
+sid {σ = σ} =
  σ ∘ ⌜ idw ⌝w ≡⟨ ap (λ ν → _ ∘ ν) ⌜id⌝w ⟩
  σ ∘ id      ≡⟨ ∘id ⟩
  σ           ∎

+s∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      σ +s (ν ∘w δ) ≡ (σ +s ν) +s δ
+s∘ {σ = σ} {ν} {δ} =
  σ ∘ ⌜ ν ∘w δ ⌝w      ≡⟨ ap (λ σ → _ ∘ σ) ⌜∘⌝w ⟩
  σ ∘ (⌜ ν ⌝w ∘ ⌜ δ ⌝w) ≡⟨ ∘∘ ⁻¹ ⟩
  (σ ∘ ⌜ ν ⌝w) ∘ ⌜ δ ⌝w ∎

[]+ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Tms Δ Θ} {ν : Wk Γ Δ} →
      u [ σ +s ν ] ≡ u [ σ ] +t ν
[]+ {u = u} {σ} {ν} =
  u [ σ ∘ ⌜ ν ⌝w ]   ≡⟨ [][] ⟩
  u [ σ ] [ ⌜ ν ⌝w ] ∎
