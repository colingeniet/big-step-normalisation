{-# OPTIONS --safe --cubical #-}

module Normalisation.NormalForms.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Normalisation.Variables.Weakening
open import Normalisation.NormalForms

_+N_ : {Γ Δ : Con} {A : Ty} → Nf Δ A → Wk Γ Δ → Nf Γ A
_+NN_ : {Γ Δ : Con} {A : Ty} → Ne Nf Δ A → Wk Γ Δ → Ne Nf Γ A

(lam n) +N σ = lam (n +N (keep _ σ))
(neu n) +N σ = neu (n +NN σ)
(var x) +NN σ = var (x +v σ)
(app f n) +NN σ = app (f +NN σ) (n +N σ)


+Nid : {Γ : Con} {A : Ty} {n : Nf Γ A} → n +N idw ≡ n
+NNid : {Γ : Con} {A : Ty} {n : Ne Nf Γ A} → n +NN idw ≡ n
+Nid {n = lam n} = ap lam +Nid
+Nid {n = neu n} = ap neu +NNid
+NNid {n = var x} = ap var +vid
+NNid {n = app f n} = ap2 app +NNid +Nid

+N∘ : {Γ Δ Θ : Con} {A : Ty} {n : Nf Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      n +N (σ ∘w ν) ≡ (n +N σ) +N ν
+NN∘ : {Γ Δ Θ : Con} {A : Ty} {n : Ne Nf Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       n +NN (σ ∘w ν) ≡ (n +NN σ) +NN ν
+N∘ {n = lam n} = ap lam +N∘
+N∘ {n = neu n} = ap neu +NN∘
+NN∘ {n = var x} = ap var +v∘
+NN∘ {n = app f n} = ap2 app +NN∘ +N∘


⌜⌝+N : {Γ Δ : Con} {A : Ty} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≡ ⌜ n ⌝N +t σ
⌜⌝+NN : {Γ Δ : Con} {A : Ty} {n : Ne Nf Δ A} {σ : Wk Γ Δ} →
        ⌜ n +NN σ ⌝NN ≡ ⌜ n ⌝NN +t σ
⌜⌝+N {n = lam n} = ap lam (⌜⌝+N {n = n} {keep _ _}) ∙ lam[] ⁻¹
⌜⌝+N {n = neu n} = ⌜⌝+NN {n = n}
⌜⌝+NN {n = var x} = ⌜⌝+v 
⌜⌝+NN {n = app f n} = ap2 _$_ (⌜⌝+NN {n = f}) (⌜⌝+N {n = n}) ∙ $[] ⁻¹
