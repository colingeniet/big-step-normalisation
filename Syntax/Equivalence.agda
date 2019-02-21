{-# OPTIONS --safe --without-K #-}

{-
  Definition of βησ-equivalence.
-}

module Syntax.Equivalence where

open import Syntax.Types
open import Syntax.Terms

infix 5 _≈_
infix 5 _≋_
infixr 10 _,≋_
infixr 20 _∘≋_
infixl 30 _[_]≈
infix 8 _≈⁻¹ _≋⁻¹
infixr 6 _∙≈_ _∙≋_

data _≈_ : {Γ : Con} {A : Ty} → Tm Γ A → Tm Γ A → Set
data _≋_ : {Γ Δ : Con} → Tms Γ Δ → Tms Γ Δ → Set

data _≈_ where
  -- Rules
  π₂β : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → π₂ (σ , u) ≈ u
  β : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} → app (lam u) ≈ u
  η : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} → lam (app f) ≈ f
  lam[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {σ : Tms Γ Δ} →
          (lam u) [ σ ] ≈ lam (u [ σ ∘ (π₁ id) , π₂ id ])
  -- Equivalence
  refl≈ : {Γ : Con} {A : Ty} {u : Tm Γ A} → u ≈ u
  _≈⁻¹ : {Γ : Con} {A : Ty} {u v : Tm Γ A} → u ≈ v → v ≈ u
  _∙≈_ : {Γ : Con} {A : Ty} {u v w : Tm Γ A} → u ≈ v → v ≈ w → u ≈ w
  -- Congruence
  _[_]≈ : {Γ Δ : Con} {A : Ty} {u v : Tm Δ A} {σ ν : Tms Γ Δ} →
          u ≈ v → σ ≋ ν → u [ σ ] ≈ v [ ν ]
  π₂≈ : {Γ Δ : Con} {A : Ty} {σ ν : Tms Γ (Δ , A)} →
        σ ≋ ν → π₂ σ ≈ π₂ ν
  lam≈ : {Γ : Con} {A B : Ty} {u v : Tm (Γ , A) B} →
         u ≈ v → lam u ≈ lam v
  app≈ : {Γ : Con} {A B : Ty} {u v : Tm Γ (A ⟶ B)} →
         u ≈ v → app u ≈ app v
data _≋_ where
  -- Rules
  id∘ : {Γ Δ : Con} {σ : Tms Γ Δ} → id ∘ σ ≋ σ
  ∘id : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ∘ id ≋ σ
  ∘∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {δ : Tms Γ Δ} →
       (σ ∘ ν) ∘ δ ≋ σ ∘ (ν ∘ δ)
  εη : {Γ : Con} {σ : Tms Γ ●} → σ ≋ ε
  π₁β : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → π₁ (σ , u) ≋ σ
  πη : {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} → (π₁ σ , π₂ σ) ≋ σ
  ,∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Δ A} →
       (σ , u) ∘ ν ≋ σ ∘ ν , u [ ν ]
  -- Equivalence
  refl≋ : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ≋ σ
  _≋⁻¹ : {Γ Δ : Con} {σ ν : Tms Γ Δ} → σ ≋ ν → ν ≋ σ
  _∙≋_ : {Γ Δ : Con} {σ ν δ : Tms Γ Δ} → σ ≋ ν → ν ≋ δ → σ ≋ δ
  -- Congruence
  _∘≋_ : {Γ Δ Θ : Con} {σ₁ σ₂ : Tms Δ Θ} {ν₁ ν₂ : Tms Γ Δ} →
         σ₁ ≋ σ₂ → ν₁ ≋ ν₂ → σ₁ ∘ ν₁ ≋ σ₂ ∘ ν₂
  _,≋_ : {Γ Δ : Con} {A : Ty} {σ ν : Tms Γ Δ} {u v : Tm Γ A} →
         σ ≋ ν → u ≈ v → σ , u ≋ ν , v
  π₁≋ : {Γ Δ : Con} {A : Ty} {σ ν : Tms Γ (Δ , A)} →
        σ ≋ ν → π₁ σ ≋ π₁ ν


