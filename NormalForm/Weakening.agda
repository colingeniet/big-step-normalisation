{-# OPTIONS --safe --cubical #-}

module NormalForm.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.List
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Weakening.Variable
open import NormalForm.NormalForm

_+N_ : {Γ Δ : Con} {A : Ty} → Nf Δ A → Wk Γ Δ → Nf Γ A
_+NN_ : {Γ Δ : Con} {A : Ty} → NN Δ A → Wk Γ Δ → NN Γ A

(lam n) +N σ = lam (n +N wk↑ _ σ)
(neu n) +N σ = neu (n +NN σ)
(var x) +NN σ = var (x +v σ)
(app f n) +NN σ = app (f +NN σ) (n +N σ)


+Nid : {Γ : Con} {A : Ty} {n : Nf Γ A} → n +N idw ≡ n
+NNid : {Γ : Con} {A : Ty} {n : NN Γ A} → n +NN idw ≡ n
+Nid {n = lam n} = ap lam +Nid
+Nid {n = neu n} = ap neu +NNid
+NNid {n = var x} = ap var +vid
+NNid {n = app f n} = ap2 app +NNid +Nid

+N∘ : {Γ Δ Θ : Con} {A : Ty} {n : Nf Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      n +N (σ ∘w ν) ≡ (n +N σ) +N ν
+NN∘ : {Γ Δ Θ : Con} {A : Ty} {n : NN Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       n +NN (σ ∘w ν) ≡ (n +NN σ) +NN ν
+N∘ {n = lam n} = ap lam (ap (λ x → n +N (x , z)) wk∘↑w ∙ +N∘ {n = n})
+N∘ {n = neu n} = ap neu +NN∘
+NN∘ {n = var x} = ap var (+v∘ {x = x})
+NN∘ {n = app f n} = ap2 app +NN∘ +N∘


⌜⌝+N : {Γ Δ : Con} {A : Ty} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≡ ⌜ n ⌝N +t σ
⌜⌝+NN : {Γ Δ : Con} {A : Ty} {n : NN Δ A} {σ : Wk Γ Δ} →
        ⌜ n +NN σ ⌝NN ≡ ⌜ n ⌝NN +t σ
⌜⌝+N {n = lam n} =
  ap lam (⌜⌝+N {n = n}
         ∙ ap (λ σ → _ [ σ , vz ]) ⌜wkwk⌝w)
  ∙ lam[] ⁻¹
⌜⌝+N {n = neu n} = ⌜⌝+NN {n = n}
⌜⌝+NN {n = var x} = ⌜⌝+v 
⌜⌝+NN {n = app f n} = ap2 _$_ (⌜⌝+NN {n = f}) (⌜⌝+N {n = n}) ∙ $[] ⁻¹
