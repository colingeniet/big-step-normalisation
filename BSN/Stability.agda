{-# OPTIONS --safe --cubical #-}

{-
  Values are invariant by evaluation (in the identity environment),
  normal forms are invariant by normalisation.
-}

module Normalisation.Stability where

open import Library.Equality
open import Library.Pairs
open import Library.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.Weakening
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Evaluator.Weakening



-- Stability by evaluation for variables.
stable-var : {Γ : Con} {A : Ty} (x : Var Γ A) →
             eval ⌜ x ⌝v > idenv ⇒ neu (var x)

-- The induction requires an appropriate weakening.
stable-var-aux : {Γ Δ : Con} {A : Ty} {x : Var Δ A} {σ : Wk Γ Δ} →
                 eval ⌜ x ⌝v > (idenv +E σ) ⇒ neu (var (x +v σ))

stable-var x =
  ap2 (λ ρ y → eval ⌜ x ⌝v > ρ ⇒ neu (var y)) +Eid +vid
  * stable-var-aux {σ = idw}

stable-var-aux {x = z} = evalπ₂ evalsid
stable-var-aux {x = s {B = B} x} {σ = drop C σ} =
  let p : ((idenv +E drop B idw) +E σ) +E drop C idw
          ≡ (idenv +E drop B idw) +E drop C σ
      p = +E∘ ⁻¹ ∙ ap (λ σ → _ +E (drop C σ)) ∘idw
      q : (z +v σ) +v idw ≡ z +v σ
      q = +vid
      r : (s x +v σ) +v idw ≡ s x +v σ
      r = +vid
  in (λ i → eval vs ⌜ x ⌝v > (p i , neu (var (s (q i)))) ⇒ neu (var (s (r i))))
      * ((stable-var-aux {x = s x} {σ = σ}) +eval (drop C idw))
stable-var-aux {x = s {B = B} x} {σ = keep B σ} =
  let p : (idenv +E (drop B idw)) +E (keep B σ) ≡ idenv +E (drop B σ)
      p = +E∘ ⁻¹ ∙ ap (λ σ → _ +E (drop B σ)) id∘w 
  in eval[] (tr (λ ρ → evals wk > (ρ , neu (var z)) ⇒ (idenv +E (drop B σ)))
                (p ⁻¹) (evalsπ₁ evalsid))
            (stable-var-aux {x = x} {σ = drop B σ})


-- Stability by evaluation for values, neutral values and environments.
stable-val : {Γ : Con} {A : Ty} (v : Val Γ A) →
             eval ⌜ v ⌝V > idenv ⇒ v
stable-neval : {Γ : Con} {A : Ty} (n : Ne Val Γ A) →
               eval ⌜ n ⌝NV > idenv ⇒ neu n
stable-env : {Γ Δ : Con} (ρ : Env Γ Δ) →
             evals ⌜ ρ ⌝E > idenv ⇒ ρ
             
stable-val (lam u ρ) = eval[] (stable-env ρ) (evallam u ρ)
stable-val (neu n) = stable-neval n
stable-val (veq {u = u} {v} p i) =
  isPropDependent {B = λ v → eval ⌜ v ⌝V > idenv ⇒ v}
                   isPropeval
                   (veq p) (stable-val u) (stable-val v) i
stable-val (isSetVal p q i j) =
  isSetDependent2 {B = λ v → eval ⌜ v ⌝V > idenv ⇒ v}
                   isSetVal (PropisSet isPropeval)
                   (λ k → stable-val (p k))
                   (λ k → stable-val (q k)) i j

stable-neval (var x) = stable-var x
stable-neval (app n v) = eval[] (evals, evalsid (stable-val v))
                                (evalapp (stable-neval n) ($app n v))

stable-env ε = evalsε
stable-env (ρ , v) = evals, (stable-env ρ) (stable-val v)


-- Stability by normalisation for normal forms and neutral normal forms.
stable-nf : {Γ : Con} {A : Ty} (n : Nf Γ A) →
            Σ[ v ∈ Val Γ A ] (eval ⌜ n ⌝N > idenv ⇒ v  ×  q v ⇒ n)
stable-nenf : {Γ : Con} {A : Ty} (n : Ne Nf Γ A) →
              Σ[ v ∈ Ne Val Γ A ] (eval ⌜ n ⌝NN > idenv ⇒ neu v  ×  qs v ⇒ n)

stable-nf (lam n) =
  let v ,, evaln ,, qv = stable-nf n in
  lam ⌜ n ⌝N idenv ,, evallam ⌜ n ⌝N idenv ,, q⟶ ($lam evaln) qv
stable-nf (neu n) =
  let v ,, evaln ,, qv = stable-nenf n in
  neu v ,, evaln ,, qo qv
  
stable-nenf (var x) =
  var x ,, stable-var x ,, qsvar
stable-nenf (app ne nf) =
  let nv ,, evalne ,, qsnv = stable-nenf ne in
  let v ,, evalnf ,, qv = stable-nf nf in
  app nv v ,,
  eval[] (evals, evalsid evalnf) (evalapp evalne ($app nv v)) ,,
  qsapp qsnv qv


stable-norm : {Γ : Con} {A : Ty} (n : Nf Γ A) → norm ⌜ n ⌝N ⇒ n
stable-norm n = qeval (fst (snd (stable-nf n))) (snd (snd (stable-nf n)))
