{-# OPTIONS --safe --cubical #-}

module Normalisation.Values.Eliminator where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Values


record Motives {l} : Set (lsuc l) where
  field
    Valᴹ : {Γ : Con} {A : Ty} → Val Γ A → Set l
    NVᴹ  : {Γ : Con} {A : Ty} → Ne Val Γ A → Set l
    Envᴹ : {Γ Δ : Con} → Env Γ Δ → Set l


record Methods {l} (M : Motives {l}) : Set (lsuc l) where
  open Motives M
  field
    lamᴹ : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B)
           {ρ : Env Γ Δ} → Envᴹ ρ → Valᴹ (lam u ρ)
    neuᴹ : {Γ : Con} {A : Ty} {u : Ne Val Γ A} →
           NVᴹ u → Valᴹ (neu u)
    varᴹ : {Γ : Con} {A : Ty} (x : Var Γ A) → NVᴹ (var x)
    appᴹ : {Γ : Con} {A B : Ty} {f : Ne Val Γ (A ⟶ B)} {u : Val Γ A} →
           NVᴹ f → Valᴹ u → NVᴹ (app f u)
    εᴹ : {Γ : Con} → Envᴹ (ε {Γ = Γ})
    _,ᴹ_ : {Γ Δ : Con} {A : Ty} {σ : Env Γ Δ} {u : Val Γ A} →
           Envᴹ σ → Valᴹ u → Envᴹ (σ , u)

    veqᴹ : {Γ : Con} {A : Ty} {u v : Val Γ A} (p : ⌜ u ⌝V ≡ ⌜ v ⌝V) →
           (uᴹ : Valᴹ u) (vᴹ : Valᴹ v) → uᴹ ≡[ ap Valᴹ (veq p) ]≡ vᴹ

    isSetValᴹ : {Γ : Con} {A : Ty} {u : Val Γ A} → isSet (Valᴹ u)

  elimVal : {Γ : Con} {A : Ty} (u : Val Γ A) → Valᴹ u
  elimNV : {Γ : Con} {A : Ty} (u : Ne Val Γ A) → NVᴹ u
  elimEnv : {Γ Δ : Con} (σ : Env Γ Δ) → Envᴹ σ

  elimVal (lam u ρ) = lamᴹ u (elimEnv ρ)
  elimVal (neu n) = neuᴹ (elimNV n)
  elimVal (veq {u = u} {v = v} p i) = veqᴹ p (elimVal u) (elimVal v) i
  elimVal (isSetVal p q i j) =
    isset-dependent2 {B = Valᴹ} isSetVal isSetValᴹ
                     (λ k → elimVal (p k)) (λ k → elimVal (q k)) i j
  elimNV (var x) = varᴹ x
  elimNV (app n u) = appᴹ (elimNV n) (elimVal u)
  elimEnv ε = εᴹ
  elimEnv (σ , u) = elimEnv σ ,ᴹ elimVal u
