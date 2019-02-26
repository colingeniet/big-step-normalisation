{-# OPTIONS --cubical #-}

{-
  The result of evaluation/normalisation is equivalent to the input.
  This is a straight forward induction over the evaluation/quote relations.
-}

module Normalisation.Completeness where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator


abstract
  eval≡ : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ}
          {uρ : Val Γ A} → eval u > ρ ⇒ uρ →
          u [ ⌜ ρ ⌝E ] ≡ ⌜ uρ ⌝V
  evals≡ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
           {σρ : Env Γ Θ} → evals σ > ρ ⇒ σρ →
           σ ∘ ⌜ ρ ⌝E ≡ ⌜ σρ ⌝E
  eval$≡ : {Γ : Con} {A B : Ty} {u : Val Γ (A ⟶ B)} {v : Val Γ A}
           {uv : Val Γ B} → u $ v ⇒ uv →
           ⌜ u ⌝V $ ⌜ v ⌝V ≡ ⌜ uv ⌝V

  eval≡ (eval[] cσ cu) = [][] ⁻¹
                         ∙ ap (_[_] _) (evals≡ cσ)
                       ∙ eval≡ cu
  eval≡ (evalπ₂ cσ) = π₂∘ ⁻¹ ∙ ap π₂ (evals≡ cσ) ∙ π₂E≡ ⁻¹
  eval≡ (evallam u ρ) = refl
  eval≡ (evalapp cf $fρ) = app[]
                         ∙ ap2 (_$_)
                               (ap (_[_] _) π₁E≡ ⁻¹ ∙ eval≡ cf)
                               (π₂E≡ ⁻¹)
                         ∙ eval$≡ $fρ

  evals≡ evalsid = id∘
  evals≡ (evals∘ cν cσ) = ∘∘
                        ∙ ap (_∘_ _) (evals≡ cν)
                        ∙ evals≡ cσ
  evals≡ evalsε = εη
  evals≡ (evals, cσ cu) = ,∘
                        ∙ ap2 _,_ (evals≡ cσ) (eval≡ cu)
  evals≡ (evalsπ₁ cσ) = π₁∘ ⁻¹
                      ∙ ap π₁ (evals≡ cσ)
                      ∙ π₁E≡ ⁻¹

  eval$≡ ($lam cu) = clos[] ∙ eval≡ cu
  eval$≡ ($app n v) = refl


  q≡ : {Γ : Con} {A : Ty} {u : Val Γ A} {n : Nf Γ A} →
       q u ⇒ n → ⌜ u ⌝V ≡ ⌜ n ⌝N
  qs≡ : {Γ : Con} {A : Ty} {u : Ne Val Γ A} {n : Ne Nf Γ A} →
        qs u ⇒ n → ⌜ u ⌝NV ≡ ⌜ n ⌝NN
  q≡ (qo qn) = qs≡ qn
  q≡ (q⟶ {f = f} $f qf) = classicη ⁻¹
                          ∙ ap lam (ap (λ x → x $ vz) (+V≡ {u = f}) ⁻¹
                                   ∙ eval$≡ $f ∙ q≡ qf)
  qs≡ qsvar = refl
  qs≡ (qsapp qf qu) = ap2 _$_ (qs≡ qf) (q≡ qu)


  norm≡ : {Γ : Con} {A : Ty} {u : Tm Γ A} {n : Nf Γ A} →
          norm u ⇒ n → u ≡ ⌜ n ⌝N
  norm≡ (qeval c q) = [id] ⁻¹
                      ∙ ap (_[_] _) idenv≡ ⁻¹
                      ∙ eval≡ c
                      ∙ q≡ q

