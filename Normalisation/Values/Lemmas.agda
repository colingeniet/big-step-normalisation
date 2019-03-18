{-# OPTIONS --safe --cubical #-}

module Normalisation.Values.Lemmas where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.Values
open import Normalisation.Values.Weakening


-- Weakening can be pushed inside a λ-closure.T
[]++V : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} →
        lam u (ρ ++E Θ) ≡ (lam u ρ) ++V Θ
[]++V {Θ = ●} = refl
[]++V {Θ = Θ , C} {u = u} {ρ = ρ} =
  ap (λ u → u +V C) ([]++V {Θ = Θ} {u = u} {ρ = ρ})

-- Embedding and projections commute.
π₁E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₁list σ ⌝E ≡ π₁ ⌜ σ ⌝E
π₁E≡ {σ = _ , _} = π₁β ⁻¹
π₂E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₂list σ ⌝V ≡ π₂ ⌜ σ ⌝E
π₂E≡ {σ = _ , _} = π₂β ⁻¹

-- Weakening and projections commute.
π₁+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₁list (envgenwk Δ σ A) ≡ envgenwk Δ (π₁list σ) A
π₁+ {σ = _ , _} = refl
π₂+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₂list (envgenwk Δ σ A) ≡ valgenwk Δ (π₂list σ) A
π₂+ {σ = _ , _} = refl

π₁++ : {Γ Δ Θ : Con} {A : Ty} {σ : Env Γ (Δ , A)} →
       π₁list (σ ++E Θ) ≡ (π₁list σ) ++E Θ
π₁++ {Θ = ●} = refl
π₁++ {Θ = Θ , B} {σ = σ} = π₁+ {Δ = ●} {A = B} {σ = σ ++E Θ}
                           ∙ ap (λ σ → σ +E B) (π₁++ {Θ = Θ} {σ = σ})
π₂++ : {Γ Δ Θ : Con} {A : Ty} {σ : Env Γ (Δ , A)} →
       π₂list (σ ++E Θ) ≡ (π₂list σ) ++V Θ
π₂++ {Θ = ●} = refl
π₂++ {Θ = Θ , B} {σ = σ} = π₂+ {Δ = ●} {A = B} {σ = σ ++E Θ}
                           ∙ ap (λ σ → σ +V B) (π₂++ {Θ = Θ} {σ = σ})

-- Weakening and environment extension commute.
,++E : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Γ Δ} {v : Val Γ A} →
       (ρ , v) ++E Θ ≡ (ρ ++E Θ , v ++V Θ)
,++E {Θ = ●} = refl
,++E {Θ = Θ , B} = ap (λ u → u +E B) (,++E {Θ = Θ})

-- Weakening and constructors commute.
++var : {Γ Δ : Con} {A : Ty} {x : Var Γ A} →
        (var x) ++NV Δ ≡ var (x ++v Δ)
++var {Δ = ●} = refl
++var {Δ = Δ , B} {x = x} = ap (λ u → u +NV B) (++var {Δ = Δ} {x = x})

++VNV : {Γ Δ : Con} {A : Ty} {v : Ne Val Γ A} →
        (neu v) ++V Δ ≡ neu (v ++NV Δ)
++VNV {Δ = ●} = refl
++VNV {Δ = Δ , B} {v = v} = ap (λ u → u +V B) (++VNV {Δ = Δ} {v = v})

-- 'Associativity' of weakening.
V+-++ : {Γ Δ : Con} {A B : Ty} {u : Val Γ A} →
                 (u +V B) ++V Δ ≡[ ap (λ Γ → Val Γ A) ,++ ]≡ u ++V ((● , B) ++ Δ)
V+-++ {Δ = ●} = refl
V+-++ {Δ = Δ , C} = apd (λ u → u +V C) (V+-++ {Δ = Δ})

E+-++ : {Γ Δ Θ : Con} {B : Ty} {σ : Env Γ Θ} →
        (σ +E B) ++E Δ ≡[ ap (λ Γ → Env Γ Θ) ,++ ]≡ σ ++E ((● , B) ++ Δ)
E+-++ {Δ = ●} = refl
E+-++ {Δ = Δ , C} = apd (λ σ → σ +E C) E+-++



-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E A , neu (var z)

idenv≡ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≡ id
idenv≡ {●} = εη ⁻¹
idenv≡ {Γ , A} = ap (λ σ → σ , vz)
                    (+E≡ ∙ ap (λ σ → σ ∘ wk) idenv≡)
                 ∙ ↑id


enveq : {Γ Δ : Con} {σ ν : Env Γ Δ} → ⌜ σ ⌝E ≡ ⌜ ν ⌝E → σ ≡ ν
enveq {Δ = ●} {ε} {ε} _ = refl
enveq {Δ = Δ , A} {σ , u} {ν , v} p =
  let p1 : σ ≡ ν
      p1 = enveq (π₁β ⁻¹ ∙ ap π₁ p ∙ π₁β)
      p2 : u ≡ v
      p2 = veq (π₂β ⁻¹ ∙ ap π₂ p ∙ π₂β)
  in ap2 _,_ p1 p2
