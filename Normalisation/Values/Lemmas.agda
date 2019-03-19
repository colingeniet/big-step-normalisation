{-# OPTIONS --safe --cubical #-}

module Normalisation.Values.Lemmas where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.Values
open import Normalisation.Values.Weakening


-- Embedding and projections commute.
π₁E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₁list σ ⌝E ≡ π₁ ⌜ σ ⌝E
π₁E≡ {σ = _ , _} = π₁β ⁻¹
π₂E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₂list σ ⌝V ≡ π₂ ⌜ σ ⌝E
π₂E≡ {σ = _ , _} = π₂β ⁻¹

-- Weakening and projections commute.
π₁+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
      π₁list (ρ +E σ) ≡ (π₁list ρ) +E σ
π₁+ {ρ = _ , _} = refl
π₂+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
      π₂list (ρ +E σ) ≡ (π₂list ρ) +V σ
π₂+ {ρ = _ , _} = refl

-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E (drop A idw) , neu (var z)

idenv≡ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≡ id
idenv≡ {●} = εη ⁻¹
idenv≡ {Γ , A} = ap (λ σ → σ , vz)
                    (⌜⌝+E ∙ ∘∘ ⁻¹
                    ∙ ap (λ x → x ∘ wk) (+sid ∙ idenv≡))
                 ∙ ↑id

enveq : {Γ Δ : Con} {σ ν : Env Γ Δ} → ⌜ σ ⌝E ≡ ⌜ ν ⌝E → σ ≡ ν
enveq {Δ = ●} {ε} {ε} _ = refl
enveq {Δ = Δ , A} {σ , u} {ν , v} p =
  let p1 : σ ≡ ν
      p1 = enveq (π₁β ⁻¹ ∙ ap π₁ p ∙ π₁β)
      p2 : u ≡ v
      p2 = veq (π₂β ⁻¹ ∙ ap π₂ p ∙ π₂β)
  in ap2 _,_ p1 p2
