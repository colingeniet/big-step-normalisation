{-# OPTIONS --safe --cubical #-}

module Normalisation.Variables.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Weakening
open import Syntax.Terms.Lemmas
open import Normalisation.Variables


-- 's' is already the weakening of variables by a type.
-- Weakening by a context.
_++v_ : {Γ : Con} {A : Ty} → Var Γ A → (Δ : Con) → Var (Γ ++ Δ) A
x ++v ● = x
x ++v (Δ , B) = s (x ++v Δ)

-- Weakening below a context.
varwk : {Γ : Con} (Δ : Con) {B : Ty} → Var (Γ ++ Δ) B → (A : Ty) →
          Var ((Γ , A) ++ Δ) B
varwk ● x A = s x
varwk (Δ , C) z A = z
varwk (Δ , C) (s x) A = s (varwk Δ x A)

varwk≡ : {Γ Δ : Con} {A B : Ty} {x : Var (Γ ++ Δ) B} →
         ⌜ varwk Δ x A ⌝v ≡ tmgenwk Δ ⌜ x ⌝v A
varwk≡ {Δ = ●} {x = x} = refl
varwk≡ {Δ = Δ , C} {A} {x = z} = π₂β ⁻¹ ∙ ap π₂ id∘ ⁻¹ ∙ π₂∘
varwk≡ {Δ = Δ , C} {A} {x = s x} =
  ap vs (varwk≡ {Δ = Δ} {A} {x = x})
  ∙ [][] ⁻¹
  ∙ ap (λ σ → ⌜ x ⌝v [ σ ])
       (π₁β ⁻¹ ∙ ap π₁ id∘ ⁻¹ ∙ π₁∘)
  ∙ [][]
