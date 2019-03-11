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
open import Library.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator



-- Stability by evaluation for variables.
stable-var : {Γ Δ : Con} {A : Ty} (x : Var Γ A) →
             eval ⌜ x ⌝v > (idenv ++E Δ) ⇒ neu (var (x ++v Δ))

stable-var {Δ = Δ} {A} z =
  (ap (λ ρ → eval vz > ρ ⇒ (neu (var z) ++V Δ))
      (,++E {ρ = idenv +E A} {v = neu (var z)} ⁻¹)
  ∙ ap (λ x → eval vz > (idenv ++E Δ) ⇒ x)
       (++VNV {Δ = Δ} {v = var z}
      ∙ ap neu (++var {Δ = Δ} {x = z})))
  * evalπ₂ evalsid

stable-var {Γ} {Δ} {A} (s {B = B} x) =
  eval[] (tr (λ ρ → evals wk > ρ ⇒ ((idenv +E B) ++E Δ))
             (,++E {ρ = idenv +E B} {v = neu (var z)} ⁻¹)
             (evalsπ₁ evalsid))
         ((λ k → eval ⌜ x ⌝v > (E+-++≡ {Δ = Δ} {B = B} {σ = idenv} (1- k)) ⇒
                      neu (var (v+-++≡ {Δ = Δ} {B = B} {x = x} (1- k))))
          * (stable-var {Δ = ((● , B) ++ Δ)} x))
  where v+-++≡ : {Γ Δ : Con} {A B : Ty} {x : Var Γ A} →
                 (s x) ++v Δ ≡[ ap (λ Γ → Var Γ A) ,++ ]≡ x ++v ((● , B) ++ Δ)
        v+-++≡ {Δ = ●} = refl
        v+-++≡ {Δ = Δ , C} = apd s v+-++≡
        E+-++≡ : {Γ Δ Θ : Con} {B : Ty} {σ : Env Γ Θ} →
                 (σ +E B) ++E Δ ≡[ ap (λ Γ → Env Γ Θ) ,++ ]≡ σ ++E ((● , B) ++ Δ)
        E+-++≡ {Δ = ●} = refl
        E+-++≡ {Δ = Δ , C} = apd (λ σ → σ +E C) E+-++≡


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
