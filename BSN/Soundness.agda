{-# OPTIONS --safe --cubical #-}

module BSN.Soundness where

open import Library.Equality
open import Syntax.Terms
open import Value.Value
open import Value.Lemmas
open import NormalForm.NormalForm
open import Evaluator.Evaluator
open import BSN.Completeness
open import NBE.Stability


-- Soundness of the evaluator is trivial using completeness, and the fact
-- that embeddings are injective
--  - by definition for values
--  - using NBE for normal forms
eval-sound : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} {v w : Val Γ A} →
             eval u > ρ ⇒ v → eval u > ρ ⇒ w → v ≡ w
eval-sound {u = u} {ρ} {v} {w} evalv evalw =
  let p : ⌜ v ⌝V ≡ ⌜ w ⌝V
      p = ⌜ v ⌝V       ≡⟨ eval≡ evalv ⁻¹ ⟩
          u [ ⌜ ρ ⌝E ] ≡⟨ eval≡ evalw ⟩
          ⌜ w ⌝V       ∎
  in veq p

evals-sound : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν δ : Env Γ Θ} →
              evals σ > ρ ⇒ ν → evals σ > ρ ⇒ δ → ν ≡ δ
evals-sound {σ = σ} {ρ} {ν} {δ} evalsν evalsδ =
  let p : ⌜ ν ⌝E ≡ ⌜ δ ⌝E
      p = ⌜ ν ⌝E     ≡⟨ evals≡ evalsν ⁻¹ ⟩
          σ ∘ ⌜ ρ ⌝E ≡⟨ evals≡ evalsδ ⟩
          ⌜ δ ⌝E     ∎
  in enveq p

$-sound : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} {v : Val Γ A} {w t : Val Γ B} →
          f $ v ⇒ w → f $ v ⇒ t → w ≡ t
$-sound {f = f} {v} {w} {t} $w $t =
  let p : ⌜ w ⌝V ≡ ⌜ t ⌝V
      p = ⌜ w ⌝V         ≡⟨ eval$≡ $w ⁻¹ ⟩
          ⌜ f ⌝V $ ⌜ v ⌝V ≡⟨ eval$≡ $t ⟩
          ⌜ t ⌝V         ∎
  in veq p

q-sound : {Γ : Con} {A : Ty} {v : Val Γ A} {n m : Nf Γ A} →
          q v ⇒ n → q v ⇒ m → n ≡ m
q-sound {v = v} {n} {m} qn qm =
  let p : ⌜ n ⌝N ≡ ⌜ m ⌝N
      p = ⌜ n ⌝N ≡⟨ q≡ qn ⁻¹ ⟩
          ⌜ v ⌝V ≡⟨ q≡ qm ⟩
          ⌜ m ⌝N ∎
  in ⌜⌝N-injective p
