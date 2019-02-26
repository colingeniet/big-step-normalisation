{-# OPTIONS --safe --cubical #-}

module Syntax.Lemmas where

open import Library.Equality
open import Syntax.Types
open import Syntax.Terms

-- Interaction between projections and composition.
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

-- Lifting the identity yields the identity.
↑id : {Γ : Con} {A : Ty} → _↑_ {Γ = Γ} id A ≡ id
↑id = ap (λ σ → σ , vz) id∘ ∙ πη

-- Applying a substitution to the variable 0 gives the last element of thereof.
vz[,] : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → vz [ σ , u ] ≡ u
vz[,] = π₂∘ ⁻¹ ∙ ap π₂ id∘ ∙ π₂β

-- Particular case.
vz[<>] : {Γ : Con} {A : Ty} {u : Tm Γ A} → vz [ < u > ] ≡ u
vz[<>] = vz[,]

-- Postcomposing with a weakening simply forgets the last element.
wk, : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → wk ∘ (σ , u) ≡ σ
wk, = π₁∘ ⁻¹ ∙ ap π₁ id∘ ∙ π₁β

-- Composition followed by extension is the same as extension followed
-- by composition up to a lifting.
↑∘, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ (ν , u) ≡ (σ ∘ ν) , u
↑∘, {σ = σ} {ν = ν} {u = u} =
  ,∘
  ∙ ap2 _,_ (∘∘ ∙ ap (λ ρ → σ ∘ ρ) wk,) vz[,]

-- This version of the previous lemma proves to be particularly usefull.
↑∘<> : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ < u > ≡ σ , u
↑∘<> {u = u} = ↑∘, ∙ ap (λ σ → σ , u) ∘id

-- Interaction between application and substitution.
-- You may be more interested in app[] just below.
[]app : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ Δ} →
        app (f [ σ ]) ≡ (app f) [ σ ↑ A ]
[]app {f = f} {σ = σ} =
  (ap (λ x → app x)
      ((ap (λ x → x [ σ ]) η) ⁻¹
      ∙ (lam[] {u = app f} {σ = σ})))
  ∙ β

-- Behaviour of app through substitution.
app[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ (Δ , A)} →
        (app f) [ σ ] ≡ f [ π₁ σ ] $ π₂ σ
app[] {f = f} {σ = σ} =
  ap (λ σ → (app f) [ σ ])
    (πη ⁻¹ ∙ ↑∘<> ⁻¹)
  ∙ [][]
  ∙ ap (λ u → u [ < π₂ σ > ]) []app ⁻¹

-- Behaviour of classical application through substitution.
$[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
      (f $ u) [ σ ] ≡ (f [ σ ]) $ (u [ σ ])
$[] {f = f} {u = u} {σ = σ} =
  [][] {σ = < u >} {ν = σ} {u = app f} ⁻¹
  ∙ ap (λ σ → app f [ σ ]) ,∘
  ∙ app[]
  ∙ ap2 (λ ν x → f [ ν ] $ x) (π₁β ∙ id∘) π₂β

-- 'Associativity' of context extension.
,++ : {Γ Δ : Con} {A : Ty} → (Γ , A) ++ Δ ≡ Γ ++ ((● , A) ++ Δ)
,++ {Δ = ●} = refl
,++ {Γ} {Δ , B} {A} = ap (λ Γ → Γ , B) ,++

-- Weakening the application of a substitution is the same as weakening the
-- substitution itself.
[]++ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Δ A} {σ : Tms Γ Δ} →
       u [ σ ++s Θ ] ≡ u [ σ ] ++t Θ
[]++ {Θ = ●} = refl
[]++ {Θ = Θ , B} = [][] ∙ ap (λ u → u + B) []++


-- Applying a λ-closure (i.e. a term of the form (λ u)[ρ]) to something
-- is the same as evaluating the body of the closure in the extended
-- environment.
clos[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ A} →
         (lam u) [ ρ ] $ v ≡ u [ ρ , v ]
clos[] {u = u} {v = v} = ap (λ x → x [ < v > ])
                            (ap app lam[] ∙ β)
                         ∙ [][] ⁻¹
                         ∙ ap (λ σ → u [ σ ]) ↑∘<>

-- The same, except the closure is weakened beforehand.
-- This lemma is crucial for the notion of strong computability defined
-- when proving termination.
wkclos[] : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B}
           {ρ : Tms Γ Δ} {v : Tm (Γ ++ Θ) A} →
           (((lam u) [ ρ ]) ++t Θ) $ v ≡ u [ ρ ++s Θ , v ]
wkclos[] {v = v} = ap (λ u → u $ v) []++ ⁻¹ ∙ clos[]


-- Classical β and η conversion rules.
classicβ : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} {v : Tm Γ A} →
           lam u $ v ≡ u [ < v > ]
classicβ {v = v} = ap (λ x → x $ v) [id] ⁻¹
                   ∙ clos[]

classicη : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
           lam (f + A $ vz) ≡ f
classicη {A = A} {f = f} = ap lam (app[] ⁻¹ ∙ [id])
                           ∙ η {f = f}
