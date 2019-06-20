{-# OPTIONS --cubical #-}

module Syntax.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable


_+t_ : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (σ : Wk Γ Δ) → Tm Γ (A [ ⌜ σ ⌝w ])
u +t σ = u [ ⌜ σ ⌝w ]

+tid : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → u +t idw ≈ u
+tid {u = u} =
  u [ ⌜ idw ⌝w ] ≈⟨ refl≈ [ ⌜idw⌝ ]≈ ⟩
  u [ id ]      ≈⟨ [id] ⟩
  u             ≈∎

+t∘ : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      u +t (σ ∘w ν) ≈ (u +t σ) +t ν
+t∘ {u = u} {σ} {ν} =
  u [ ⌜ σ ∘w ν ⌝w ]      ≈⟨ refl≈ [ ⌜∘⌝w ]≈ ⟩
  u [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≈⟨ [][] ⟩
  u [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≈∎

_+s_ : {Γ Δ Θ : Con} → Tms Δ Θ → Wk Γ Δ → Tms Γ Θ
σ +s ν = σ ∘ ⌜ ν ⌝w

abstract
  +sid : {Γ Δ : Con} {σ : Tms Γ Δ} → σ +s idw ≋ σ
  +sid {σ = σ} =
    σ ∘ ⌜ idw ⌝w ≋⟨ refl≋ ∘≋ ⌜idw⌝ ⟩
    σ ∘ id      ≋⟨ ∘id ⟩
    σ           ≋∎

  +s∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
        σ +s (ν ∘w δ) ≋ (σ +s ν) +s δ
  +s∘ {σ = σ} {ν} {δ} =
    σ ∘ ⌜ ν ∘w δ ⌝w      ≋⟨ refl≋ ∘≋ ⌜∘⌝w ⟩
    σ ∘ (⌜ ν ⌝w ∘ ⌜ δ ⌝w) ≋⟨ ∘∘ ≋⁻¹ ⟩
    (σ ∘ ⌜ ν ⌝w) ∘ ⌜ δ ⌝w ≋∎

  []+ : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {σ : Tms Δ Θ} {ν : Wk Γ Δ} →
        u [ σ +s ν ] ≈ u [ σ ] +t ν
  []+ {u = u} {σ} {ν} =
    u [ σ ∘ ⌜ ν ⌝w ]   ≈⟨ [][] ⟩
    u [ σ ] [ ⌜ ν ⌝w ] ≈∎
