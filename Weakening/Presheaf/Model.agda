{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.Model where

open import Agda.Primitive
open import Syntax.Terms
open import Weakening.Presheaf.List
open import Weakening.Presheaf.CCC


record PshModel : Set₁ where
  field
    ⟦o⟧ : Pshw

  ⟦_⟧T : Ty → Pshw
  ⟦ o ⟧T = ⟦o⟧
  ⟦ A ⟶ B ⟧T = ⟦ A ⟧T ⇒p ⟦ B ⟧T

  ⟦_⟧C : Con → Pshw
  ⟦_⟧C = listp ⟦_⟧T

  ⟦_⟧type : term-index → Set _
  ⟦ Tm-i Γ A ⟧type = Natw ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦ Tms-i Γ Δ ⟧type = Natw ⟦ Γ ⟧C ⟦ Δ ⟧C


  ⟦_⟧ : {i : term-index} → term i → ⟦ i ⟧type

  ⟦ u [ σ ] ⟧ = ⟦ u ⟧ ∘n ⟦ σ ⟧
  ⟦ π₂ {Δ = Δ} {A} σ ⟧ = π₂n ⟦ Δ ⟧C ⟦ A ⟧T ⟦ σ ⟧
  ⟦ lam {Γ = Γ} {A} {B} u ⟧ =
    lamp {F = ⟦ Γ ⟧C} {G = ⟦ A ⟧T} {H = ⟦ B ⟧T} ⟦ u ⟧
  ⟦ app {Γ = Γ} {A} {B} f ⟧ =
    appp {F = ⟦ Γ ⟧C} {G = ⟦ A ⟧T} {H = ⟦ B ⟧T} ⟦ f ⟧

  ⟦ id ⟧ = idn
  ⟦ σ ∘ ν ⟧ = ⟦ σ ⟧ ∘n ⟦ ν ⟧ 
  ⟦ ε ⟧ = !p
  ⟦ σ , u ⟧ = ⟦ σ ⟧ ,n ⟦ u ⟧
  ⟦ π₁ {Δ = Δ} {A} σ ⟧ = π₁n ⟦ Δ ⟧C ⟦ A ⟧T ⟦ σ ⟧

  ⟦ π₂β {σ = σ} {u = u} i ⟧ = π₂nβ {θ = ⟦ σ ⟧} {α = ⟦ u ⟧} i
  ⟦ β {Γ = Γ} {A} {B} {u} i ⟧ =
    βp {F = ⟦ Γ ⟧C} {G = ⟦ A ⟧T} {H = ⟦ B ⟧T} {θ = ⟦ u ⟧} i
  ⟦ η {Γ = Γ} {A} {B} {f} i ⟧ =
    ηp {F = ⟦ Γ ⟧C} {G = ⟦ A ⟧T} {H = ⟦ B ⟧T} {θ = ⟦ f ⟧} i
  ⟦ lam[] {Γ = Γ} {Δ} {A} {B} {u} {σ} i ⟧ =
    natlam {F = ⟦ Δ ⟧C} {G = ⟦ A ⟧T} {H = ⟦ B ⟧T} {K = ⟦ Γ ⟧C} {θ = ⟦ u ⟧} {α = ⟦ σ ⟧} i
  
  ⟦ id∘ {σ = σ} i ⟧ = id∘n {θ = ⟦ σ ⟧} i
  ⟦ ∘id {σ = σ} i ⟧ = ∘idn {θ = ⟦ σ ⟧} i
  ⟦ ∘∘ {σ = σ} {ν} {ρ} i ⟧ = ∘∘n {θ = ⟦ σ ⟧} {⟦ ν ⟧} {⟦ ρ ⟧} i
  ⟦ εη {σ = σ} i ⟧ = !pη {θ = ⟦ σ ⟧} i
  ⟦ π₁β {σ = σ} {u} i ⟧ = π₁nβ {θ = ⟦ σ ⟧} {α = ⟦ u ⟧} i
  ⟦ πη {Γ} {Δ} {A} {σ = σ} i ⟧ = πnη {F = ⟦ Γ ⟧C} {G = ⟦ Δ ⟧C} {H = ⟦ A ⟧T} {θ = ⟦ σ ⟧} i
  ⟦ ,∘ {σ = σ} {ν} {u} i ⟧ = ,∘n {θ = ⟦ σ ⟧} {⟦ u ⟧} {⟦ ν ⟧} i

  ⟦ isSetTm p q i j ⟧ = isSetnat (λ j → ⟦ p j ⟧) (λ j → ⟦ q j ⟧) i j
  ⟦ isSetTms p q i j ⟧ = isSetnat (λ j → ⟦ p j ⟧) (λ j → ⟦ q j ⟧) i j
