{-# OPTIONS --cubical #-}

module Normalisation.Evaluator where

open import Library.Equality
open import Library.Pairs
open import Library.Negation
open import Library.NotEqual
open import Syntax.Terms
open import Syntax.Weakening
open import Normalisation.Variables
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Weakening
open import Normalisation.NormalForms.Sets
open import Normalisation.Substitutions


eval-type : term-index → Set
eval-type (Tm-i Δ A) = {Γ : Con} → Env Γ Δ → Nf Γ A
eval-type (Tms-i Δ Θ) = {Γ : Con} → Env Γ Δ → Env Γ Θ

eval : {i : term-index} → term i → eval-type i


eval (u [ σ ]) ρ = eval u (eval σ ρ)
eval (π₂ σ) ρ = π₂env (eval σ ρ)
eval (lam u) ρ = lam (eval u (ρ ↑env _))
eval (app f) (ρ , n) = appNf (eval f ρ) n

eval id ρ = ρ
eval (σ ∘ ν) ρ = eval σ (eval ν ρ)
eval ε _ = ε
eval (σ , u) ρ = eval σ ρ , eval u ρ
eval (π₁ σ) ρ = π₁env (eval σ ρ)

eval (id∘ {σ = σ} _) ρ = eval σ ρ
eval (∘id {σ = σ} _) ρ = eval σ ρ
eval (∘∘ {σ = σ} {ν} {δ} _) ρ = eval σ (eval ν (eval δ ρ))
eval (εη {σ = σ} i) ρ = εηenv {ρ = eval σ ρ} i
eval (,∘ {σ = σ} {ν} {u} _) ρ = eval σ (eval ν ρ) , eval u (eval ν ρ)
eval (π₁β {σ = σ} _) ρ = eval σ ρ
eval (π₂β {u = u} _) ρ = eval u ρ
eval (πη {σ = σ} i) ρ = πηenv {ρ = eval σ ρ} i
eval (β {u = u} _) ρ = {!!}
eval (η {f = f} _) ρ = {!!}
eval (lam[] {u = u} {σ} i) ρ = {!!}

eval (isSetTm p q i j) ρ = isSetNf (λ k → eval (p k) ρ) (λ k → eval (q k) ρ) i j
eval (isSetTms p q i j) ρ = isSetEnv (λ k → eval (p k) ρ) (λ k → eval (q k) ρ) i j
