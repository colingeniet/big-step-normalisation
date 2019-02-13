{-# OPTIONS --cubical #-}

module Syntax.Equality where

open import Equality
open import Syntax.Types
open import Syntax.Terms

-- Equality lemmas on terms.
π₁∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₁ (σ ∘ ν) ≡ (π₁ σ) ∘ ν
π₁∘ {ν = ν} = ap π₁
                 (ap (λ σ → σ ∘ ν) πη ⁻¹
                 ∙ ,∘)
              ∙ π₁β

π₂∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₂ (σ ∘ ν) ≡ (π₂ σ) [ ν ]
π₂∘ {ν = ν} = ap π₂ (ap (λ σ → σ ∘ ν) πη ⁻¹
                    ∙ ,∘)
              ∙ π₂β

-- Applying id or ∘ to a term behaves as expected.
[id] : {Γ : Con} {A : Ty} {u : Tm Γ A} → u [ id ] ≡ u
[id] {u = u} = π₂β {σ = id} ⁻¹
               ∙ ap π₂ (ap (λ ν → ν , u [ id ]) id∘ ⁻¹
                       ∙ ,∘ ⁻¹ ∙ ∘id)
               ∙ π₂β

[][] : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Θ A} →
       u [ σ ∘ ν ] ≡ u [ σ ] [ ν ]
[][] {σ = σ} {ν = ν} {u = u} = π₂β {σ = σ ∘ ν} ⁻¹
                               ∙ ap π₂ (ap (λ ρ → ρ , u [ σ ∘ ν ]) id∘ ⁻¹
                                       ∙ ,∘ ⁻¹ ∙ ∘∘ ⁻¹)
                               ∙ π₂∘ ∙ ap (λ u → u [ ν ]) π₂∘
                               ∙ ap (λ u → u [ σ ] [ ν ]) π₂β


vz[,] : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → vz [ σ , u ] ≡ u
vz[,] = π₂∘ ⁻¹ ∙ ap π₂ id∘ ∙ π₂β

vz[<>] : {Γ : Con} {A : Ty} {u : Tm Γ A} → vz [ < u > ] ≡ u
vz[<>] = vz[,]

wk, : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → wk ∘ (σ , u) ≡ σ
wk, = π₁∘ ⁻¹ ∙ ap π₁ id∘ ∙ π₁β

↑∘, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ (ν , u) ≡ (σ ∘ ν) , u
↑∘, {σ = σ} {ν = ν} {u = u} =
  ,∘
  ∙ ap (λ ρ → ρ , vz [ ν , u ]) (∘∘ ∙ ap (λ ρ → σ ∘ ρ) wk,)
  ∙ ap (λ v → σ ∘ ν , v) vz[,]

↑∘,id : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ (id , u) ≡ σ , u
↑∘,id {u = u} = ↑∘, ∙ ap (λ σ → σ , u) ∘id

[]app : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ Δ} →
        app (f [ σ ]) ≡ (app f) [ σ ↑ A ]
[]app {f = f} {σ = σ} = (ap (λ x → app x)
                            ((ap (λ x → x [ σ ]) η) ⁻¹
                            ∙ (lam[] {u = app f} {σ = σ})))
                        ∙ β

,++ : {Γ Δ : Con} {A : Ty} → (Γ , A) ++ Δ ≡ Γ ++ ((● , A) ++ Δ)
,++ {Δ = ●} = refl
,++ {Γ} {Δ , B} {A} = ap (λ Γ → Γ , B) ,++

[]++ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Δ A} {σ : Tms Γ Δ} → u [ σ ++s Θ ] ≡ u [ σ ] ++t Θ
[]++ {Θ = ●} = refl
[]++ {Θ = Θ , B} = [][] ∙ ap (λ u → u + B) []++



app[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ (Δ , A)} →
        (app f) [ σ ] ≡ f [ π₁ σ ] $ π₂ σ
app[] {f = f} {σ = σ} = ap (λ σ → (app f) [ σ ])
                           (πη ⁻¹ ∙ ↑∘,id ⁻¹)
                        ∙ [][]
                        ∙ ap (λ u → u [ < π₂ σ > ]) []app ⁻¹

$[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
      (f $ u) [ σ ] ≡ (f [ σ ]) $ (u [ σ ])
$[] {f = f} {u = u} {σ = σ} = [][] {σ = < u >} {ν = σ} {u = app f} ⁻¹
                              ∙ ap (λ σ → app f [ σ ]) ,∘
                              ∙ app[]
                              ∙ ap (λ ν → f [ ν ] $ π₂ (id ∘ σ , u [ σ ])) (π₁β ∙ id∘)
                              ∙ ap (λ ν → f [ σ ] $ ν) π₂β

clos[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ A} →
         (lam u) [ ρ ] $ v ≡ u [ ρ , v ]
clos[] {u = u} {v = v} = ap (λ x → x [ < v > ])
                            (ap app lam[] ∙ β)
                         ∙ [][] ⁻¹
                         ∙ ap (λ σ → u [ σ ]) ↑∘,id


classicη : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
           lam (f + A $ vz) ≡ f
classicη {A = A} {f = f} = ap lam (app[] ⁻¹ ∙ [id])
                           ∙ η {f = f}
