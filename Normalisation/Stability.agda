{-# OPTIONS --cubical #-}

{-
  Values are invariant by evaluation (in the identity environment),
  normal forms are invariant by normalisation.

  The lemmas in this module prove that a value _can_ be evaluated to itself,
  it follows by determinism that it also _can only_ be evaluated to itself
  (and idem for normal forms).
-}

module Normalisation.Stability where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Determinism



-- Stability by evaluation for variables.
postulate
  stable-var : {Γ Δ : Con} {A : Ty} (x : Var Γ A) →
               eval ⌜ x ⌝v > (idenv ++E Δ) ⇒ vneu (var (x ++v Δ))
{-
stable-var {Δ = Δ} {A} z =
  (ap (λ ρ → eval vz > ρ ⇒ (vneu (var z) ++V Δ))
      (,++E {ρ = idenv +E A} {v = vneu (var z)} ⁻¹)
  ∙ ap (λ x → eval vz > (idenv ++E Δ) ⇒ x)
       (++VNV {Δ = Δ} {v = var z}
      ∙ ap vneu (++var {Δ = Δ} {x = z})))
  * evalπ₂ evalsid

stable-var {Γ} {Δ} {A} (s {B = B} x) =
  eval[] (tr (λ ρ → evals wk > ρ ⇒ ((idenv +E B) ++E Δ))
             (,++E {ρ = idenv +E B} {v = vneu (var z)} ⁻¹)
             (evalsπ₁ evalsid))
         {!stable-var {Δ = ((● , B) ++ Δ)} x!}
-}

-- Stability by evaluation for values, neutral values and environments.
stable-val : {Γ : Con} {A : Ty} (v : Val Γ A) →
             eval ⌜ v ⌝V > idenv ⇒ v
stable-neval : {Γ : Con} {A : Ty} (n : Ne Val Γ A) →
               eval ⌜ n ⌝NV > idenv ⇒ vneu n
stable-env : {Γ Δ : Con} (ρ : Env Γ Δ) →
             evals ⌜ ρ ⌝E > idenv ⇒ ρ
             
stable-val (vlam u ρ) = eval[] (stable-env ρ) (evallam u ρ)
stable-val (vneu n) = stable-neval n

stable-neval (var x) = stable-var x
stable-neval (app n v) = eval[] (evals, evalsid (stable-val v))
                                (evalapp (stable-neval n) ($app n v))

stable-env ε = evalsε
stable-env (ρ , v) = evals, (stable-env ρ) (stable-val v)


-- Stability by normalisation for normal forms and neutral normal forms.
stable-nf : {Γ : Con} {A : Ty} (n : Nf Γ A) →
            Σ[ v ∈ Val Γ A ] (eval ⌜ n ⌝N > idenv ⇒ v  ∧  q v ⇒ n)
stable-nenf : {Γ : Con} {A : Ty} (n : Ne Nf Γ A) →
              Σ[ v ∈ Ne Val Γ A ] (eval ⌜ n ⌝NN > idenv ⇒ vneu v  ∧  qs v ⇒ n)

stable-nf (nlam n) =
  let v ,, evaln ,, qv = stable-nf n in
  vlam ⌜ n ⌝N idenv ,, evallam ⌜ n ⌝N idenv ,, q⟶ ($lam evaln) qv
stable-nf (nneu n) =
  let v ,, evaln ,, qv = stable-nenf n in
  vneu v ,, evaln ,, qo qv
  
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
