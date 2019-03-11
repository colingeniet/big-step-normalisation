{-# OPTIONS --allow-unsolved-meta --cubical #-}

module Normalisation.Evaluator.Weakening where


open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Weakening
open import Normalisation.Evaluator


-- All computations can be weakened.
abstract
  -- Most general version, for the induction.
  evalgenwk : {Γ Δ : Con} {B : Ty} (Ψ : Con) {u : Tm Δ B} {ρ : Env (Γ ++ Ψ) Δ}
              {uρ : Val (Γ ++ Ψ) B} → eval u > ρ ⇒ uρ → (A : Ty) →
              eval u > (envgenwk Ψ ρ A) ⇒ (valgenwk Ψ uρ A)
  evalsgenwk : {Γ Δ Θ : Con} (Ψ : Con) {σ : Tms Δ Θ} {ρ : Env (Γ ++ Ψ) Δ}
               {σρ : Env (Γ ++ Ψ) Θ} → evals σ > ρ ⇒ σρ → (A : Ty) →
               evals σ > (envgenwk Ψ ρ A) ⇒ (envgenwk Ψ σρ A)
  $genwk : {Γ : Con} {A B : Ty} (Δ : Con) {f : Val (Γ ++ Δ) (A ⟶ B)}
           {u : Val (Γ ++ Δ) A} {fu : Val (Γ ++ Δ) B} → f $ u ⇒ fu → (C : Ty) →
           (valgenwk Δ f C) $ (valgenwk Δ u C) ⇒ (valgenwk Δ fu C)

  evalgenwk Δ (eval[] cσ cu) A =
    eval[] (evalsgenwk Δ cσ A) (evalgenwk Δ cu A)
  evalgenwk Δ (evalπ₂ {σρ = σρ} cσ) A =
    tr (λ u → eval _ > _ ⇒ u) (π₂+ {σ = σρ}) (evalπ₂ (evalsgenwk Δ cσ A))
  evalgenwk Δ (evallam u ρ) A = evallam u (envgenwk Δ ρ A)
  evalgenwk Δ (evalapp {ρ = ρ} cf $fρ) A =
    evalapp
    (tr (λ ρ → eval _ > ρ ⇒ _) (π₁+ {σ = ρ} ⁻¹) (evalgenwk Δ cf A))
    (tr (λ v → _ $ v ⇒ _) (π₂+ {σ = ρ} ⁻¹) ($genwk Δ $fρ A))
  evalgenwk Δ (isPropeval c c' i) A =
    isPropeval (evalgenwk Δ c A) (evalgenwk Δ c' A) i

  evalsgenwk Δ evalsid A = evalsid
  evalsgenwk Δ (evals∘ cν cσ) A = evals∘ (evalsgenwk Δ cν A) (evalsgenwk Δ cσ A)
  evalsgenwk Δ evalsε A = evalsε
  evalsgenwk Δ (evals, cσ cu) A = evals, (evalsgenwk Δ cσ A) (evalgenwk Δ cu A)
  evalsgenwk Δ (evalsπ₁ {σρ = σρ} cσ) A =
    tr (λ u → evals _ > _ ⇒ u) (π₁+ {σ = σρ}) (evalsπ₁ (evalsgenwk Δ cσ A))
  evalsgenwk Δ (isPropevals c c' i) A =
    isPropevals (evalsgenwk Δ c A) (evalsgenwk Δ c' A) i

  $genwk Δ ($lam cu) A = $lam (evalgenwk Δ cu A)
  $genwk Δ ($app n v) A = $app (nvgenwk Δ n A) (valgenwk Δ v A)
  $genwk Δ (isProp$ c c' i) A =
    isProp$ ($genwk Δ c A) ($genwk Δ c' A) i


  qgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Val (Γ ++ Δ) B}
           {n : Nf (Γ ++ Δ) B} → q u ⇒ n → (A : Ty) →
           q (valgenwk Δ u A) ⇒ (nfgenwk Δ n A)
  qsgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Ne Val (Γ ++ Δ) B}
            {n : Ne Nf (Γ ++ Δ) B} → qs u ⇒ n → (A : Ty) →
            qs (nvgenwk Δ u A) ⇒ (nefgenwk Δ n A)

  qgenwk Δ (qo qn) A = qo (qsgenwk Δ qn A)
  qgenwk Δ (q⟶ {A = A} {f = u} $f qf) C =
    q⟶ (tr (λ x → x $ _ ⇒ _) (++-+V {u = u} ⁻¹) ($genwk (Δ , A) $f C))
       (qgenwk (Δ , A) qf C)
    where ++-+V : {Γ Δ : Con} {A B C : Ty} {u : Val (Γ ++ Δ) A} →
                  (valgenwk Δ u C) +V B ≡ valgenwk (Δ , B) (u +V B) C
          ++-+NV : {Γ Δ : Con} {A B C : Ty} {u : Ne Val (Γ ++ Δ) A} →
                   (nvgenwk Δ u C) +NV B ≡ nvgenwk (Δ , B) (u +NV B) C
          ++-+E : {Γ Δ Θ : Con} {B C : Ty} {σ : Env (Γ ++ Δ) Θ} →
                  (envgenwk Δ σ C) +E B ≡ envgenwk (Δ , B) (σ +E B) C
          ++-+V {u = lam u ρ} = ap (lam u) ++-+E
          ++-+V {u = neu u} = ap neu ++-+NV
          ++-+V {u = veq p i} j = {!!}
          ++-+V {u = isSetVal p q i j} k = {!!}
          ++-+NV {u = var x} = refl
          ++-+NV {u = app f u} = ap2 app (++-+NV {u = f}) (++-+V {u = u})
          ++-+E {σ = ε} = refl
          ++-+E {σ = σ , u} = ap2 _,_ (++-+E {σ = σ}) (++-+V {u = u})
  qgenwk Δ (isPropq c c' i) A =
    isPropq (qgenwk Δ c A) (qgenwk Δ c' A) i
  
  qsgenwk Δ qsvar A = qsvar
  qsgenwk Δ (qsapp qf qu) A = qsapp (qsgenwk Δ qf A) (qgenwk Δ qu A)
  qsgenwk Δ (isPropqs c c' i) A =
    isPropqs (qsgenwk Δ c A) (qsgenwk Δ c' A) i



  -- Those are the lemmas which are actually used later on.
  qwk : {Γ : Con} {B : Ty} {u : Val Γ B} {n : Nf Γ B} →
        q u ⇒ n → (A : Ty) → q (u +V A) ⇒ (n +N A)
  qwk = qgenwk ●

  evalwks : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} {v : Val Γ A} →
            eval u > ρ ⇒ v → (Θ : Con) → eval u > (ρ ++E Θ) ⇒ (v ++V Θ)
  evalwks c ● = c
  evalwks c (Θ , A) = evalgenwk ● (evalwks c Θ) A

  evalswks : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν : Env Γ Θ} →
            evals σ > ρ ⇒ ν → (Θ : Con) → evals σ > (ρ ++E Θ) ⇒ (ν ++E Θ)
  evalswks c ● = c
  evalswks c (Θ , A) = evalsgenwk ● (evalswks c Θ) A

  qswks : {Γ : Con} {A : Ty} {u : Ne Val Γ A} {n : Ne Nf Γ A} →
          qs u ⇒ n → (Δ : Con) → qs (u ++NV Δ) ⇒ (n ++NN Δ)
  qswks qu ● = qu
  qswks qu (Δ , A) = qsgenwk ● (qswks qu Δ) A
