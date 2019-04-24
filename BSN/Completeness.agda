{-# OPTIONS --safe --cubical #-}

{-
  The result of evaluation/normalisation is equivalent to the input.
  This is a straight forward induction over the evaluation/quote relations.
-}

module BSN.Completeness where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Weakening.Variable
open import Value.Value
open import Value.Lemmas
open import Value.Weakening
open import NormalForm.NormalForm
open import Evaluator.Evaluator


eval≡ : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ}
        {uρ : Val Γ A} → eval u > ρ ⇒ uρ →
        u [ ⌜ ρ ⌝E ] ≡ ⌜ uρ ⌝V
evals≡ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
         {σρ : Env Γ Θ} → evals σ > ρ ⇒ σρ →
         σ ∘ ⌜ ρ ⌝E ≡ ⌜ σρ ⌝E
eval$≡ : {Γ : Con} {A B : Ty} {u : Val Γ (A ⟶ B)} {v : Val Γ A}
         {uv : Val Γ B} → u $ v ⇒ uv →
         ⌜ u ⌝V $ ⌜ v ⌝V ≡ ⌜ uv ⌝V

eval≡ (eval[] {u = u} {σ} {ρ} {σρ} {uσρ} cσ cu) =
  u [ σ ] [ ⌜ ρ ⌝E ] ≡⟨ [][] ⁻¹ ⟩
  u [ σ ∘ ⌜ ρ ⌝E ]   ≡⟨ ap (λ x → u [ x ]) (evals≡ cσ) ⟩
  u [ ⌜ σρ ⌝E ]      ≡⟨ eval≡ cu ⟩
  ⌜ uσρ ⌝V           ∎
eval≡ (evalπ₂ {σ = σ} {ρ} {σρ} cσ) =
  (π₂ σ) [ ⌜ ρ ⌝E ] ≡⟨ π₂∘ ⁻¹ ⟩
  π₂ (σ ∘ ⌜ ρ ⌝E)   ≡⟨ ap π₂ (evals≡ cσ) ⟩
  π₂ ⌜ σρ ⌝E        ≡⟨ π₂E≡ ⁻¹ ⟩
  ⌜ π₂E σρ ⌝V       ∎
eval≡ (evallam u ρ) =
  (lam u) [ ⌜ ρ ⌝E ] ∎
eval≡ (evalapp {f = f} {ρ , v} {fρ} {fρv} cf $fρ) =
  (app f) [ ⌜ ρ , v ⌝E ]            ≡⟨ app[] ⟩
  f [ π₁ ⌜ ρ , v ⌝E ] $ π₂ ⌜ ρ , v ⌝E ≡⟨ ap2 (λ ρ v → f [ ρ ] $ v) π₁β π₂β ⟩
  f [ ⌜ ρ ⌝E ] $ ⌜ v ⌝V              ≡⟨ ap (λ x → x $ ⌜ v ⌝V) (eval≡ cf) ⟩
  ⌜ fρ ⌝V $ ⌜ v ⌝V                   ≡⟨ eval$≡ $fρ ⟩
  ⌜ fρv ⌝V                          ∎
eval≡ (isPropeval c c' i) =
  isSetTm (eval≡ c) (eval≡ c') i

evals≡ (evalsid {ρ = ρ}) =
  id ∘ ⌜ ρ ⌝E ≡⟨ id∘ ⟩
  ⌜ ρ ⌝E      ∎
evals≡ (evals∘ {σ = σ} {ν} {ρ} {νρ} {σνρ} cν cσ) =
  (σ ∘ ν) ∘ ⌜ ρ ⌝E ≡⟨ ∘∘ ⟩
  σ ∘ (ν ∘ ⌜ ρ ⌝E) ≡⟨ ap (_∘_ _) (evals≡ cν) ⟩
  σ ∘ ⌜ νρ ⌝E      ≡⟨ evals≡ cσ ⟩
  ⌜ σνρ ⌝E         ∎
evals≡ (evalsε {ρ = ρ}) =
  ε ∘ ⌜ ρ ⌝E ≡⟨ εη ⟩
  ε         ∎
evals≡ (evals, {σ = σ} {v} {ρ} {σρ} {vρ} cσ cu) =
  (σ , v) ∘ ⌜ ρ ⌝E             ≡⟨ ,∘ ⟩
  (σ ∘ ⌜ ρ ⌝E) , (v [ ⌜ ρ ⌝E ]) ≡⟨ ap2 _,_ (evals≡ cσ) (eval≡ cu) ⟩
  ⌜ σρ ⌝E , ⌜ vρ ⌝V             ∎
evals≡ (evalsπ₁ {σ = σ} {ρ} {σρ} cσ) =
  (π₁ σ) ∘ ⌜ ρ ⌝E ≡⟨ π₁∘ ⁻¹ ⟩
  π₁ (σ ∘ ⌜ ρ ⌝E) ≡⟨ ap π₁ (evals≡ cσ) ⟩
  π₁ ⌜ σρ ⌝E      ≡⟨ π₁E≡ ⁻¹ ⟩
  ⌜ π₁E σρ ⌝E     ∎
evals≡ (isPropevals c c' i) =
  isSetTms (evals≡ c) (evals≡ c') i

eval$≡ ($lam {u = u} {ρ} {v} {uv} cu) =
  lam u [ ⌜ ρ ⌝E ] $ ⌜ v ⌝V ≡⟨ clos[] ⟩
  u [ ⌜ ρ , v ⌝E ]         ≡⟨ eval≡ cu ⟩
  ⌜ uv ⌝V                  ∎
eval$≡ ($app n v) =
  ⌜ n ⌝NV $ ⌜ v ⌝V ∎
eval$≡ (isProp$ c c' i) =
  isSetTm (eval$≡ c) (eval$≡ c') i


q≡ : {Γ : Con} {A : Ty} {u : Val Γ A} {n : Nf Γ A} →
     q u ⇒ n → ⌜ u ⌝V ≡ ⌜ n ⌝N
qs≡ : {Γ : Con} {A : Ty} {u : NV Γ A} {n : NN Γ A} →
      qs u ⇒ n → ⌜ u ⌝NV ≡ ⌜ n ⌝NN
q≡ (qo {n = v} {n} qn) =
  ⌜ v ⌝NV ≡⟨ qs≡ qn ⟩
  ⌜ n ⌝NN ∎
q≡ (q⟶ {A = A} {f = f} {fz} {nfz} $f qf) =
  ⌜ f ⌝V                               ≡⟨ classicη ⁻¹ ⟩
  lam (⌜ f ⌝V [ wk ] $ vz)             ≡⟨ ap (λ x → lam (⌜ f ⌝V [ x ] $ vz)) id∘ ⁻¹ ⟩
  lam (⌜ f ⌝V [ id ∘ wk ] $ vz)        ≡⟨ ap (λ x → lam (⌜ f ⌝V [ x ∘ wk ] $ vz)) ⌜id⌝w ⁻¹ ⟩
  lam (⌜ f ⌝V [ ⌜ idw ⌝w ∘ wk ] $ vz)   ≡⟨ ap (λ x → lam (⌜ f ⌝V [ x ] $ vz)) ⌜wkwk⌝w ⁻¹ ⟩
  lam (⌜ f ⌝V [ ⌜ wkwk A idw ⌝w ] $ vz) ≡⟨ ap (λ x → lam (x $ vz)) (⌜⌝+V {v = f}) ⁻¹ ⟩
  lam (⌜ f +V (wkwk A idw) ⌝V $ vz)    ≡⟨ ap lam (eval$≡ $f) ⟩
  lam ⌜ fz ⌝V                          ≡⟨ ap lam (q≡ qf) ⟩
  ⌜ lam nfz ⌝N ∎
q≡ (isPropq c c' i) =
  isSetTm (q≡ c) (q≡ c') i

qs≡ (qsvar {x = x}) =
  ⌜ x ⌝v ∎
qs≡ (qsapp {f = f} {v} {n} {m} qf qv) =
  ⌜ f ⌝NV $ ⌜ v ⌝V ≡⟨ ap2 _$_ (qs≡ qf) (q≡ qv) ⟩
  ⌜ n ⌝NN $ ⌜ m ⌝N ∎
qs≡ (isPropqs c c' i) =
  isSetTm (qs≡ c) (qs≡ c') i


norm≡ : {Γ : Con} {A : Ty} {u : Tm Γ A} {n : Nf Γ A} →
        norm u ⇒ n → u ≡ ⌜ n ⌝N
norm≡ (qeval {u = u} {v} {n} cu qv) =
  u               ≡⟨ [id] ⁻¹ ⟩
  u [ id ]        ≡⟨ ap (λ x → u [ x ]) idenv≡ ⁻¹ ⟩
  u [ ⌜ idenv ⌝E ] ≡⟨ eval≡ cu ⟩
  ⌜ v ⌝V           ≡⟨ q≡ qv ⟩
  ⌜ n ⌝N           ∎
  
