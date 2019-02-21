{-# OPTIONS --without-K #-}

module Normalisation.Stability where

open import Equality
open import Syntax.Terms
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Determinism

open import Agda.Builtin.Sigma renaming (_,_ to _,,_)


-- Stability : normalisation of a normal form does nothing.

-- Technical lemma : a variable evaluates to itself in the identity environment.
-- This requires some generalisation for the induction.
postulate
  stable-var : {Γ Δ : Con} {A : Ty} (x : Var Γ A) →
               eval ⌜ x ⌝v > (idenv ++E Δ) ⇒ vneu (var (x ++v Δ))
{-
stable-var {Γ} {Δ} {A} z =
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
         {!!}
-}

-- A value evaluates to itself.
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


-- A normal form normalises to itself.
stable-nf : {Γ : Con} {A : Ty} (n : Nf Γ A) →
            Σ (Val Γ A) λ v →
            Σ (eval ⌜ n ⌝N > idenv ⇒ v) λ _ →
              q v ⇒ n
stable-nenf : {Γ : Con} {A : Ty} (n : Ne Nf Γ A) →
              Σ (Ne Val Γ A) λ v →
              Σ (eval ⌜ n ⌝NN > idenv ⇒ vneu v) λ _ →
                qs v ⇒ n

stable-nf (nlam n) =
  let v ,, evaln ,, qv = stable-nf n in
  vlam ⌜ n ⌝N idenv ,,
  evallam ⌜ n ⌝N idenv ,,
  q⟶ ($lam evaln) qv
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
