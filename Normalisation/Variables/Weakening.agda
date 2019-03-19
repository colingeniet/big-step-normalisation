{-# OPTIONS --safe --cubical #-}

module Normalisation.Variables.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Terms.Weakening
open import Syntax.Terms.Lemmas
open import Normalisation.Variables

_+v_ : {Γ Δ : Con} {A : Ty} → Var Δ A → Wk Γ Δ → Var Γ A
x +v (drop A σ) = s (x +v σ)
z +v (keep A σ) = z
(s x) +v (keep A σ) = s (x +v σ)

+vid : {Γ : Con} {A : Ty} {x : Var Γ A} → x +v idw ≡ x
+vid {x = z} = refl
+vid {x = s x} = ap s +vid

+v∘ : {Γ Δ Θ : Con} {A : Ty} {x : Var Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      x +v (σ ∘w ν) ≡ (x +v σ) +v ν
+v∘ {x = x} {σ} {nil} with σ   | x
...                      | nil | ()
+v∘ {ν = drop A ν} = ap s +v∘
+v∘ {σ = drop A σ} {keep A ν} = ap s +v∘
+v∘ {x = z} {keep A σ} {keep A ν} = refl
+v∘ {x = s x} {keep A σ} {keep A ν} = ap s +v∘

⌜⌝+v : {Γ Δ : Con} {A : Ty} {x : Var Δ A} {σ : Wk Γ Δ} →
       ⌜ x +v σ ⌝v ≡ ⌜ x ⌝v +t σ
⌜⌝+v {x = x} {drop A σ} = ap (λ x → vs x) (⌜⌝+v {x = x} {σ = σ})
                          ∙ [][] ⁻¹
⌜⌝+v {x = z} {keep A σ} = vz[,] ⁻¹
⌜⌝+v {x = s x} {keep A σ} = ap (λ x → vs x) (⌜⌝+v {x = x} {σ = σ})
                            ∙ [][] ⁻¹ ∙ ap (λ σ → ⌜ x ⌝v [ σ ]) wk, ⁻¹ ∙ [][]
