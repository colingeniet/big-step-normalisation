{-# OPTIONS --safe --cubical #-}

module Value.Lemmas where

open import Library.Equality
open import Syntax.Terms
open import Weakening.Variable
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Value.Value
open import Value.Weakening

-- Projection for lists.
π₁E : {Γ Δ : Con} {A : Ty} → Env Γ (Δ , A) → Env Γ Δ
π₁E (ρ , _) = ρ
π₂E : {Γ Δ : Con} {A : Ty} → Env Γ (Δ , A) → Val Γ A
π₂E (_ , v) = v

πηE : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} → (π₁E ρ , π₂E ρ) ≡ ρ
πηE {ρ = _ , _} = refl

-- Embedding and projections commute.
π₁E≡ : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} → ⌜ π₁E ρ ⌝E ≡ π₁ ⌜ ρ ⌝E
π₁E≡ {ρ = ρ , v} =
  ⌜ ρ ⌝E              ≡⟨ π₁β ⁻¹ ⟩
  π₁ (⌜ ρ ⌝E , ⌜ v ⌝V) ∎
π₂E≡ : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} → ⌜ π₂E ρ ⌝V ≡ π₂ ⌜ ρ ⌝E
π₂E≡ {ρ = ρ , v} =
  ⌜ v ⌝V              ≡⟨ π₂β ⁻¹ ⟩
  π₂ (⌜ ρ ⌝E , ⌜ v ⌝V) ∎

-- Weakening and projections commute.
π₁+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
      π₁E (ρ +E σ) ≡ (π₁E ρ) +E σ
π₁+ {ρ = _ , _} = refl
π₂+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
      π₂E (ρ +E σ) ≡ (π₂E ρ) +V σ
π₂+ {ρ = _ , _} = refl

-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E (wkwk A idw) , neu (var z)

idenv≡ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≡ id
idenv≡ {●} =
  ε ≡⟨ εη ⁻¹ ⟩
  id ∎
idenv≡ {Γ , A} =
  ⌜ idenv +E wkwk A idw ⌝E , vz    ≡⟨ ap (λ x → x , vz) ⌜⌝+E ⟩
  ⌜ idenv ⌝E ∘ ⌜ wkwk A idw ⌝w , vz ≡⟨ ap (λ x → x ∘ ⌜ wkwk A idw ⌝w , vz) idenv≡ ⟩
  id ∘ ⌜ wkwk A idw ⌝w , vz        ≡⟨ ap (λ x → x , vz) id∘ ⟩
  ⌜ wkwk A idw ⌝w , vz             ≡⟨ ap (λ x → x , vz) ⌜wkwk⌝w ⟩
  ⌜ idw ⌝w ∘ wk , vz               ≡⟨ ap (λ x → x ↑ A) ⌜id⌝w ⟩
  id ∘ wk , vz                     ≡⟨ ↑id ⟩
  id                               ∎

-- Since embedding of values is (by definition) injective,
-- so is the embedding of environments.
enveq : {Γ Δ : Con} {σ ν : Env Γ Δ} → ⌜ σ ⌝E ≡ ⌜ ν ⌝E → σ ≡ ν
enveq {Δ = ●} {ε} {ε} _ = refl
enveq {Δ = Δ , A} {σ , u} {ν , v} p =
  let p1 : σ ≡ ν
      p1 = enveq (π₁β ⁻¹ ∙ ap π₁ p ∙ π₁β)
      p2 : u ≡ v
      p2 = veq (π₂β ⁻¹ ∙ ap π₂ p ∙ π₂β)
  in ap2 _,_ p1 p2
