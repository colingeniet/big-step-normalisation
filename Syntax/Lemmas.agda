{-# OPTIONS --safe --cubical #-}

{-
  Basic lemmas on the syntax of the λ-calculus.
  Most of those lemmas are proof of equivalences.
-}

module Syntax.Lemmas where

open import Library.Equality
open import Syntax.Types
open import Syntax.Terms
open import Syntax.Equivalence


-- Congruence rule for the classical application.
abstract
  infixl 10 _$≈_
  _$≈_ : {Γ : Con} {A B : Ty} {f g : Tm Γ (A ⟶ B)} {u v : Tm Γ A} →
         f ≈ g → u ≈ v → f $ u ≈ g $ v
  p $≈ q = (app≈ p) [ refl≋ ,≋ q ]≈


  -- Interaction between projections and composition.
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

  -- Lifting the identity yields the identity.
  ↑id : {Γ : Con} {A : Ty} → _↑_ {Γ = Γ} id A ≋ id
  ↑id = id∘ ,≋ refl≈
      ∙≋ πη

  -- Applying a substitution to the variable 0 gives the last element of thereof.
  vz[,] : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → vz [ σ , u ] ≈ u
  vz[,] = π₂∘ ≈⁻¹
        ∙≈ π₂≈ id∘
        ∙≈ π₂β

  -- Particular case.
  vz[<>] : {Γ : Con} {A : Ty} {u : Tm Γ A} → vz [ < u > ] ≈ u
  vz[<>] = vz[,]

  -- Postcomposing with a weakening simply forgets the last element.
  wk, : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → wk ∘ (σ , u) ≋ σ
  wk, = π₁∘ ≋⁻¹
      ∙≋ π₁≋ id∘
      ∙≋ π₁β

  -- Composition followed by extension is the same as extension followed
  -- by composition up to a lifting.
  ↑∘, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ A} →
        (σ ↑ A) ∘ (ν , u) ≋ (σ ∘ ν) , u
  ↑∘, = ,∘
      ∙≋ (∘∘ ∙≋ (refl≋ ∘≋ wk,)) ,≋ vz[,]

  -- This version of the previous lemma proves to be particularely usefull.
  ↑∘<> : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
        (σ ↑ A) ∘ < u > ≋ σ , u
  ↑∘<> = ↑∘, ∙≋ ∘id ,≋ refl≈

  -- Interaction between application and substitution.
  -- You may be more interested in app[] just below.
  []app : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ Δ} →
          app (f [ σ ]) ≈ (app f) [ σ ↑ A ]
  []app = app≈ (η [ refl≋ ]≈ ≈⁻¹
               ∙≈ lam[])
        ∙≈ β

  -- Behaviour of app through substitution.
  app[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ (Δ , A)} →
          (app f) [ σ ] ≈ f [ π₁ σ ] $ π₂ σ
  app[] = refl≈ [ (πη ≋⁻¹) ∙≋ (↑∘<> ≋⁻¹) ]≈
        ∙≈ [][]
        ∙≈ ([]app ≈⁻¹) [ refl≋ ]≈

  -- Behaviour of classical application through substitution.
  $[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
        (f $ u) [ σ ] ≈ (f [ σ ]) $ (u [ σ ])
  $[] = [][] ≈⁻¹
      ∙≈ refl≈ [ ,∘ ]≈
      ∙≈ app[]
      ∙≈ refl≈ [ π₁β ∙≋ id∘ ]≈ $≈ π₂β


  -- 'Associativity' of context extension.
  ,++ : {Γ Δ : Con} {A : Ty} → (Γ , A) ++ Δ ≡ Γ ++ ((● , A) ++ Δ)
  ,++ {Δ = ●} = refl
  ,++ {Δ = Δ , B} = ap (λ Γ → Γ , B) ,++

  -- Weakening the application of a substitution is the same as weakening the
  -- substitution itself.
  []++ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Δ A} {σ : Tms Γ Δ} →
         u [ σ ++s Θ ] ≈ u [ σ ] ++t Θ
  []++ {Θ = ●} = refl≈
  []++ {Θ = Θ , B} = [][] ∙≈ []++ [ refl≋ ]≈


  -- Applying a λ-closure (i.e. a term of the form (λ u)[ρ]) to something
  -- is the same as evaluating the body of the closure in the extended
  -- environment.
  clos[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ A} →
           (lam u) [ ρ ] $ v ≈ u [ ρ , v ]
  clos[] = (app≈ lam[] ∙≈ β) [ refl≋ ]≈
         ∙≈ [][] ≈⁻¹
         ∙≈ refl≈ [ ↑∘<> ]≈

  -- The same, except the closure is weakened beforehand.
  -- This lemma is crucial for the notion of strong computability defined
  -- when proving termination.
  wkclos[] : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B}
             {ρ : Tms Γ Δ} {v : Tm (Γ ++ Θ) A} →
             (((lam u) [ ρ ]) ++t Θ) $ v ≈ u [ ρ ++s Θ , v ]
  wkclos[] = (app≈ []++ ≈⁻¹) [ refl≋ ]≈
           ∙≈ clos[]

  -- Classical β and η conversion rules.
  classicβ : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} {v : Tm Γ A} →
             lam u $ v ≈ u [ < v > ]
  classicβ = ([id] ≈⁻¹) $≈ refl≈
           ∙≈ clos[]

  classicη : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
             lam (f + A $ vz) ≈ f
  classicη = lam≈ (app[] ≈⁻¹ ∙≈ [id])
           ∙≈ η
