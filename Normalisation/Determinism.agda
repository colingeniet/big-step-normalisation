{-# OPTIONS --safe --cubical #-}

{-
  The eval/quote relations are deterministic.
  The proof is a straight forward induction:
  for every possible term, only one rule can be applied to evaluate it.
-}

module Normalisation.Determinism where

open import Library.Equality
open import Syntax.Terms
open import Normalisation.NormalForms
open import Normalisation.Evaluator


abstract
  eval-deterministic : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ}
                       {v v' : Val Γ A} → eval u > ρ ⇒ v → eval u > ρ ⇒ v' →
                       v ≡ v'
  evals-deterministic : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
                        {ν ν' : Env Γ Θ} → evals σ > ρ ⇒ ν → evals σ > ρ ⇒ ν' →
                        ν ≡ ν'
  $-deterministic : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} {u : Val Γ A}
                    {v v' : Val Γ B} → f $ u ⇒ v → f $ u ⇒ v' →
                    v ≡ v'

  eval-deterministic (eval[] evalσ evalu) (eval[] evalσ' evalu') =
    let evalu = tr (λ ρ → eval _ > ρ ⇒ _)
                   (evals-deterministic evalσ evalσ') evalu
    in eval-deterministic evalu evalu'
  eval-deterministic (evalπ₂ evalσ) (evalπ₂ evalσ') =
    ap π₂list (evals-deterministic evalσ evalσ')
  eval-deterministic {u = lam u} {ρ = ρ} (evallam u ρ) (evallam u ρ) = refl
  eval-deterministic (evalapp evalu $u) (evalapp evalu' $u') =
    let $u = tr (λ f → f $ _ ⇒ _)
                (eval-deterministic evalu evalu') $u
    in $-deterministic $u $u'

  evals-deterministic evalsid evalsid = refl
  evals-deterministic (evals∘ evalν evalσ) (evals∘ evalν' evalσ') =
    let evalσ = tr (λ ρ → evals _ > ρ ⇒ _)
                   (evals-deterministic evalν evalν') evalσ
    in evals-deterministic evalσ evalσ'
  evals-deterministic evalsε evalsε = refl
  evals-deterministic (evals, evalσ evalu) (evals, evalσ' evalu') =
    ap (λ σ → σ , _) (evals-deterministic evalσ evalσ')
    ∙ ap (λ u → _ , u) (eval-deterministic evalu evalu')
  evals-deterministic (evalsπ₁ evalσ) (evalsπ₁ evalσ') =
    ap π₁list (evals-deterministic evalσ evalσ')

  $-deterministic ($lam evalu) ($lam evalu') =
    eval-deterministic evalu evalu'
  $-deterministic {f = vneu n} {u = u} ($app f u) ($app f u) = refl



  q-deterministic : {Γ : Con} {A : Ty} {v : Val Γ A} {n n' : Nf Γ A} →
                    q v ⇒ n → q v ⇒ n' → n ≡ n'
  qs-deterministic : {Γ : Con} {A : Ty} {v : Ne Val Γ A} {n n' : Ne Nf Γ A} →
                     qs v ⇒ n → qs v ⇒ n' → n ≡ n'
  q-deterministic (qo qv) (qo qv') = ap nneu (qs-deterministic qv qv')
  q-deterministic (q⟶ $v qv) (q⟶ $v' qv') =
    let qv = tr (λ v → q v ⇒ _) ($-deterministic $v $v') qv in
    ap nlam (q-deterministic qv qv')
  qs-deterministic qsvar qsvar = refl
  qs-deterministic (qsapp qsn qv) (qsapp qsn' qv') =
    ap (λ n → app n _) (qs-deterministic qsn qsn')
    ∙ ap (λ v → app _ v) (q-deterministic qv qv')


  norm-deterministic : {Γ : Con} {A : Ty} {u : Tm Γ A} {n n' : Nf Γ A} →
                       norm u ⇒ n → norm u ⇒ n' → n ≡ n'
  norm-deterministic (qeval evalu qu) (qeval evalu' qu') =
    let qu = tr (λ v → q v ⇒ _)
                (eval-deterministic evalu evalu') qu
    in q-deterministic qu qu'
