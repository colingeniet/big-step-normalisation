{-# OPTIONS --cubical #-}

module StrongComputability.Sets where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Value.Value
open import Value.Sets
open import NormalForm.NormalForm
open import Evaluator.Evaluator
open import Evaluator.Soundness
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Evaluator
open import StrongComputability.StrongComputability


abstract
  isPropscvTV : {S : TSk} {Γ : Con} {A : TV S Γ} {v : Val Γ ⌜ A ⌝T} → isProp (scvTV A v)
  isPropscvTV {A = U} {v} (n ,, qn) (m ,, qm) i =
    let n≡m : n ≡ m
        n≡m = q-sound qn qm
    in n≡m i ,, isPropDependent isPropq n≡m qn qm i
  isPropscvTV {A = El u} {v} (n ,, qn) (m ,, qm) i =
    let n≡m : n ≡ m
        n≡m = q-sound qn qm
    in n≡m i ,, isPropDependent isPropq n≡m qn qm i
  isPropscvTV {Π S T} {Γ} {Π A B} {f} x y i {Δ} σ {v} scvv =
    let C ,, fv ,, $fv ,, scvfv = x σ scvv
        C' ,, fv' ,, $fv' ,, scvfv' = y σ scvv
        fv≅fv' = $-sound $fv $fv'
        C≡C' = ⌜⌝T-injective (fst fv≅fv')
        fv≡fv' = ≅-to-≡[] isSetTy fv≅fv' {P = ap ⌜_⌝T C≡C'}
    in C≡C' i ,, fv≡fv' i ,,
       isPropPath {B = λ i → _ $ _ ⇒ (fv≡fv' i)} isProp$ $fv $fv' i ,,
       isPropPath {B = λ i → scvTV (C≡C' i) (fv≡fv' i)} isPropscvTV scvfv scvfv' i


isPropscv : {Γ : Con} {A : Ty Γ} {v : Val Γ A} → isProp (scv v)
isPropscv = isPropscvTV

isPropsce : {Γ Δ : Con} {ρ : Env Γ Δ} → isProp (sce ρ)
isPropsce {Δ = ●} {ε} = isProp⊤
isPropsce {Δ = Δ , A} {ρ , v} = isProp× (isPropsce {ρ = ρ}) (isPropscv {v = v})
