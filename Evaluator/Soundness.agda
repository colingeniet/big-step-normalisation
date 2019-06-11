{-# OPTIONS --cubical #-}

module Evaluator.Soundness where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Value.Value
open import Value.Lemmas
open import NormalForm.NormalForm
open import Evaluator.Evaluator


abstract
  eval-sound : {Γ Δ : Con} {A : Ty Δ} {B B' : Ty Γ} {u : Tm Δ A}
               {ρ : Env Γ Δ} {v : Val Γ B} {w : Val Γ B'} →
               eval u > ρ ⇒ v → eval u > ρ ⇒ w → v ≅[ Val Γ ] w
  eval-sound {B = B} {B'} {u} {ρ} {v} {w} evalv evalw =
    let p : ⌜ v ⌝V ≅[ Tm _ ] ⌜ w ⌝V
        p = ⌜ v ⌝V       ≅⟨ eval≡ evalv ≅⁻¹ ⟩'
            u [ ⌜ ρ ⌝E ] ≅⟨ eval≡ evalw ⟩'
            ⌜ w ⌝V       ≅∎
    in ≡[]-to-≅ (veqdep (snd p))

  evals-sound : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν δ : Env Γ Θ} →
                evals σ > ρ ⇒ ν → evals σ > ρ ⇒ δ → ν ≡ δ
  evals-sound {σ = σ} {ρ} {ν} {δ} evalsν evalsδ =
    let p : ⌜ ν ⌝E ≡ ⌜ δ ⌝E
        p = ⌜ ν ⌝E     ≡⟨ evals≡ evalsν ⁻¹ ⟩
            σ ∘ ⌜ ρ ⌝E ≡⟨ evals≡ evalsδ ⟩
            ⌜ δ ⌝E     ∎
    in enveq p

  $-sound : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C C' : Ty Γ}
            {f : Val Γ (Π A B)} {v : Val Γ A} {w : Val Γ C} {t : Val Γ C'} →
            f $ v ⇒ w → f $ v ⇒ t → w ≅[ Val Γ ] t
  $-sound {f = f} {v} {w} {t} $w $t =
    let p : ⌜ w ⌝V ≅[ Tm _ ] ⌜ t ⌝V
        p = ⌜ w ⌝V         ≅⟨ eval$≡ $w ≅⁻¹ ⟩'
            ⌜ f ⌝V $ ⌜ v ⌝V ≅⟨ eval$≡ $t ⟩'
            ⌜ t ⌝V         ≅∎
    in ≡[]-to-≅ (veqdep (snd p))

  postulate
    ⌜⌝N-injective : {Γ : Con} {A : Ty Γ} {n m : Nf Γ A} → ⌜ n ⌝N ≡ ⌜ m ⌝N → n ≡ m
    ⌜⌝NN-injective : {Γ : Con} {A : Ty Γ} {n m : NN Γ A} → ⌜ n ⌝NN ≡ ⌜ m ⌝NN → n ≡ m

  q-sound : {Γ : Con} {A : Ty Γ} {v : Val Γ A} {n m : Nf Γ A} →
            q v ⇒ n → q v ⇒ m → n ≡ m
  q-sound {v = v} {n} {m} qn qm =
    let p : ⌜ n ⌝N ≡ ⌜ m ⌝N
        p = ⌜ n ⌝N ≡⟨ q≡ qn ⁻¹ ⟩
            ⌜ v ⌝V ≡⟨ q≡ qm ⟩
            ⌜ m ⌝N ∎
    in ⌜⌝N-injective p

  qs-sound : {Γ : Con} {A : Ty Γ} {v : NV Γ A} {n m : NN Γ A} →
            qs v ⇒ n → qs v ⇒ m → n ≡ m
  qs-sound {v = v} {n} {m} qn qm =
    let p : ⌜ n ⌝NN ≡ ⌜ m ⌝NN
        p = ⌜ n ⌝NN ≡⟨ qs≡ qn ⁻¹ ⟩
            ⌜ v ⌝NV ≡⟨ qs≡ qm ⟩
            ⌜ m ⌝NN ∎
    in ⌜⌝NN-injective p
