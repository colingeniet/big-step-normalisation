{-# OPTIONS --safe --without-K #-}

module Syntax.Lemmas where

open import Equality
open import Syntax.Types
open import Syntax.Terms
open import Syntax.Equivalence

-- Additional congruences.
infixl 10 _$≈_
_$≈_ : {Γ : Con} {A B : Ty} {f g : Tm Γ (A ⟶ B)} {u v : Tm Γ A} →
       f ≈ g → u ≈ v → f $ u ≈ g $ v
p $≈ q = (app≈ p) [ refl≋ ,≋ q ]≈

-- Equality lemmas on terms and substitutions.

π₁∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₁ (σ ∘ ν) ≋ (π₁ σ) ∘ ν
π₁∘ = π₁≋ ((πη ≋⁻¹) ∘≋ refl≋ ∙≋ ,∘) ∙≋ π₁β

π₂∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₂ (σ ∘ ν) ≈ (π₂ σ) [ ν ]
π₂∘ = π₂≈ ((πη ≋⁻¹) ∘≋ refl≋ ∙≋ ,∘) ∙≈ π₂β


-- Applying id or ∘ to a term behaves as expected.
[id] : {Γ : Con} {A : Ty} {u : Tm Γ A} → u [ id ] ≈ u
[id] = π₂β ≈⁻¹
     ∙≈ π₂≈ ((id∘ ≋⁻¹) ,≋ refl≈
            ∙≋ ,∘ ≋⁻¹
            ∙≋ ∘id)
     ∙≈ π₂β

[][] : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Θ A} →
       u [ σ ∘ ν ] ≈ u [ σ ] [ ν ]
[][] = π₂β ≈⁻¹
     ∙≈ π₂≈ ((id∘ ≋⁻¹) ,≋ refl≈
            ∙≋ ,∘ ≋⁻¹
            ∙≋ ∘∘ ≋⁻¹)
     ∙≈ π₂∘
     ∙≈ π₂∘ [ refl≋ ]≈
     ∙≈ π₂β [ refl≋ ]≈ [ refl≋ ]≈

↑id : {Γ : Con} {A : Ty} → _↑_ {Γ = Γ} id A ≋ id
↑id = id∘ ,≋ refl≈
    ∙≋ πη

vz[,] : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → vz [ σ , u ] ≈ u
vz[,] = π₂∘ ≈⁻¹
      ∙≈ π₂≈ id∘
      ∙≈ π₂β

vz[<>] : {Γ : Con} {A : Ty} {u : Tm Γ A} → vz [ < u > ] ≈ u
vz[<>] = vz[,]

wk, : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → wk ∘ (σ , u) ≋ σ
wk, = π₁∘ ≋⁻¹
    ∙≋ π₁≋ id∘
    ∙≋ π₁β

↑∘, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ (ν , u) ≋ (σ ∘ ν) , u
↑∘, = ,∘
    ∙≋ (∘∘ ∙≋ (refl≋ ∘≋ wk,)) ,≋ vz[,]

↑∘<> : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ < u > ≋ σ , u
↑∘<> = ↑∘, ∙≋ ∘id ,≋ refl≈

[]app : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ Δ} →
        app (f [ σ ]) ≈ (app f) [ σ ↑ A ]
[]app = app≈ (η [ refl≋ ]≈ ≈⁻¹
             ∙≈ lam[])
      ∙≈ β

,++ : {Γ Δ : Con} {A : Ty} → (Γ , A) ++ Δ ≡ Γ ++ ((● , A) ++ Δ)
,++ {Δ = ●} = refl
,++ {Δ = Δ , B} = ap (λ Γ → Γ , B) ,++

[]++ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Δ A} {σ : Tms Γ Δ} → u [ σ ++s Θ ] ≈ u [ σ ] ++t Θ
[]++ {Θ = ●} = refl≈
[]++ {Θ = Θ , B} = [][] ∙≈ []++ [ refl≋ ]≈


app[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ (Δ , A)} →
        (app f) [ σ ] ≈ f [ π₁ σ ] $ π₂ σ
app[] = refl≈ [ (πη ≋⁻¹) ∙≋ (↑∘<> ≋⁻¹) ]≈
      ∙≈ [][]
      ∙≈ ([]app ≈⁻¹) [ refl≋ ]≈

$[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
      (f $ u) [ σ ] ≈ (f [ σ ]) $ (u [ σ ])
$[] = [][] ≈⁻¹
    ∙≈ refl≈ [ ,∘ ]≈
    ∙≈ app[]
    ∙≈ refl≈ [ π₁β ∙≋ id∘ ]≈ $≈ π₂β

clos[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ A} →
         (lam u) [ ρ ] $ v ≈ u [ ρ , v ]
clos[] = (app≈ lam[] ∙≈ β) [ refl≋ ]≈
       ∙≈ [][] ≈⁻¹
       ∙≈ refl≈ [ ↑∘<> ]≈

wkclos[] : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm (Γ ++ Θ) A} →
           (((lam u) [ ρ ]) ++t Θ) $ v ≈ u [ ρ ++s Θ , v ]
wkclos[] = (app≈ []++ ≈⁻¹) [ refl≋ ]≈
         ∙≈ clos[]

classicη : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
           lam (f + A $ vz) ≈ f
classicη = lam≈ (app[] ≈⁻¹ ∙≈ [id])
         ∙≈ η
