{-# OPTIONS --cubical #-}

module NormalForm.Weakening where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Variable.Variable
open import Variable.Lemmas
open import NormalForm.NormalForm


_+N_ : {Γ Δ : Con} {A : Ty Δ} → Nf Δ A → (σ : Wk Γ Δ) → Nf Γ (A [ ⌜ σ ⌝w ]T)
_+NN_ : {Γ Δ : Con} {A : Ty Δ} → NN Δ A → (σ : Wk Γ Δ) → NN Γ (A [ ⌜ σ ⌝w ]T)

⌜⌝+N : {Γ Δ : Con} {A : Ty Δ} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≡ ⌜ n ⌝N +t σ
⌜⌝+NN : {Γ Δ : Con} {A : Ty Δ} {n : NN Δ A} {σ : Wk Γ Δ} →
        ⌜ n +NN σ ⌝NN ≡ ⌜ n ⌝NN +t σ

private
  abstract
    [⌜↑⌝] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Wk Γ Δ} →
            B [ ⌜ σ ↑w A ⌝w ]T ≡ B [ ⌜ σ ⌝w ↑ A ]T
    [⌜↑⌝] {B = B} = ap (B [_]T) ⌜↑w⌝

    [<>][] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {n : Nf Δ A} {σ : Wk Γ Δ} →
             B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ n +N σ ⌝N > ]T ≡ B [ < ⌜ n ⌝N > ]T [ ⌜ σ ⌝w ]T
    [<>][] {Γ} {Δ} {A} {B} {n} {σ} =
      B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ n +N σ ⌝N > ]T ≡⟨ [][]T ⁻¹ ⟩
      B [ (⌜ σ ⌝w ↑ A) ∘ < ⌜ n +N σ ⌝N > ]T  ≡⟨ ap (λ x → B [ x ]T) ↑∘<> ⟩
      B [ ⌜ σ ⌝w , ⌜ n +N σ ⌝N ]T            ≡⟨ ap (λ x → B [ _ , x ]T) ⌜⌝+N ⟩
      B [ ⌜ σ ⌝w , ⌜ n ⌝N [ ⌜ σ ⌝w ] ]T      ≡⟨ ap (B [_]T) <>∘ ⁻¹ ⟩
      B [ < ⌜ n ⌝N > ∘ ⌜ σ ⌝w ]T             ≡⟨ [][]T ⟩
      B [ < ⌜ n ⌝N > ]T [ ⌜ σ ⌝w ]T          ∎


(lam {A = A} {B} n) +N σ =
  tr (Nf _) (Π[] ⁻¹)
     (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w _))))
(neuU n) +N σ =
  tr (Nf _) (U[] ⁻¹)
     (neuU (tr (NN _) U[] (n +NN σ)))
(neuEl n) +N σ = 
  tr (Nf _) (El[] ⁻¹)
     (neuEl (tr (NN _) El[] (n +NN σ)))
(var x) +NN σ = var (x +v σ)
(app f n) +NN σ =
  tr (NN _) ([<>][] {n = n})
     (app (tr (NN _) Π[] (f +NN σ)) (n +N σ))


abstract
  ⌜⌝+N {Γ} {n = lam {A = A} {B} n} {σ} =
    let p : ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
            ≅[ Tm (Γ , A [ ⌜ σ ⌝w ]T) ]
            ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ]
        p = ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
              ≅⟨ apd ⌜_⌝N (trfill (Nf _) [⌜↑⌝] (n +N (σ ↑w A))) ⁻¹ ⟩
            ⌜ n +N (σ ↑w A) ⌝N
              ≅⟨ ⌜⌝+N {n = n} ⟩
            ⌜ n ⌝N [ ⌜ σ ↑w A ⌝w ]
              ≅⟨ apd (⌜ n ⌝N [_]) ⌜↑w⌝ ⟩
            ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ] ≅∎
    in ≅-to-≡ {B = Tm Γ} isSetTy (
       ⌜ tr (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)))) ⌝N
         ≅⟨ apd ⌜_⌝N (trfill (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A))))) ⁻¹ ⟩
       lam ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
         ≅⟨ ap≅ lam p ⟩'
       lam (⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ])
         ≅⟨ lam[] ≅⁻¹ ⟩'
       (lam ⌜ n ⌝N) [ ⌜ σ ⌝w ] ≅∎)
  ⌜⌝+N {Γ} {n = neuU n} {σ} = ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ))) ⌝N
      ≅⟨ apd ⌜_⌝N (trfill (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ)))) ⁻¹ ⟩
    ⌜ tr (NN _) U[] (n +NN σ) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN _) U[] (n +NN σ)) ⁻¹ ⟩
    ⌜ n +NN σ ⌝NN
      ≅⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≅∎)
  ⌜⌝+N {Γ} {n = neuEl n} {σ} = ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ))) ⌝N
      ≅⟨ apd ⌜_⌝N (trfill (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ)))) ⁻¹ ⟩
    ⌜ tr (NN _) El[] (n +NN σ) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN _) El[] (n +NN σ)) ⁻¹ ⟩
    ⌜ n +NN σ ⌝NN
      ≅⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≅∎)
    
  ⌜⌝+NN {n = var x} = ⌜⌝+v 
  ⌜⌝+NN {Γ} {Δ} {A} {app {B = B} f n} {σ} =
    let p : ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≅[ Tm Γ ] tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN
        p = ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≅⟨ apd ⌜_⌝NN (trfill (NN Γ) Π[] (f +NN σ)) ⁻¹ ⟩
            ⌜ f +NN σ ⌝NN                 ≅⟨ trfill (Tm Γ) Π[] ⌜ f +NN σ ⌝NN ⟩
            tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN   ≅∎
    in ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (NN Γ) ([<>][] {n = n}) (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ)) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN Γ) ([<>][] {n = n})
                           (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ))) ⁻¹ ⟩
    ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN $ ⌜ n +N σ ⌝N
      ≅⟨ (λ i → ≅-to-≡ isSetTy p i $ ⌜ n +N σ ⌝N) ⟩
    (tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN) $ ⌜ n +N σ ⌝N
      ≅⟨ apd (λ x → tr (Tm Γ) Π[] x $ ⌜ n +N σ ⌝N) (⌜⌝+NN {n = f}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $ ⌜ n +N σ ⌝N
      ≅⟨ apd ((tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $_) (⌜⌝+N {n = n}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $ (⌜ n ⌝N [ ⌜ σ ⌝w ])
      ≅⟨ $[] ≅⁻¹ ⟩'
    (⌜ f ⌝NN $ ⌜ n ⌝N) [ ⌜ σ ⌝w ] ≅∎)

{-
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
+N∘ {n = lam {A = A} n} {σ} {ν} =
  lam (n +N (wk↑ A (σ ∘w ν)))     ≡⟨ ap (λ ρ → lam (n +N (ρ ,, z))) wk∘↑w ⟩
  lam (n +N (wk↑ A σ ∘w wk↑ A ν)) ≡⟨ ap lam +N∘ ⟩
  (lam n +N σ) +N ν               ∎
+N∘ {n = neu n} = ap neu +NN∘
+NN∘ {n = var x} = ap var (+v∘ {x = x})
+NN∘ {n = app f n} = ap2 app +NN∘ +N∘
-}
