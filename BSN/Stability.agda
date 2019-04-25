{-# OPTIONS --safe --cubical #-}

{-
  Values are invariant by evaluation (in the identity environment),
  normal forms are invariant by normalisation.
-}

module BSN.Stability where

open import Library.Equality
open import Library.Pairs
open import Library.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Weakening.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import Evaluator.Evaluator
open import Evaluator.Weakening



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
stable-var-aux {x = s {B = B} x} {σ ,, y} =
  let e : eval ⌜ x ⌝v > (idenv +E σ) ⇒ neu (var (x +v σ))
      e = stable-var-aux {x = x} {σ}
      p : idenv +E σ ≡ (idenv +E (wkwk B idw)) +E (σ ,, y)
      p = idenv +E σ                          ≡⟨ ap (λ x → idenv +E x) id∘w ⁻¹ ⟩
          idenv +E (idw ∘w σ)                 ≡⟨ ap (λ x → idenv +E x) wkwk∘w ⁻¹ ⟩
          idenv +E ((wkwk B idw) ∘w (σ ,, y)) ≡⟨ +E∘ ⟩
          (idenv +E (wkwk B idw)) +E (σ ,, y) ∎
      f : eval ⌜ x ⌝v > ((idenv +E (wkwk B idw)) +E (σ ,, y)) ⇒ neu (var (x +v σ))
      f = tr (λ x → eval _ > x ⇒ _) p e
  in eval[] (evalsπ₁ evalsid) f



-- Stability by evaluation for values, neutral values and environments.
stable-val : {Γ : Con} {A : Ty} (v : Val Γ A) →
             eval ⌜ v ⌝V > idenv ⇒ v
stable-neval : {Γ : Con} {A : Ty} (n : NV Γ A) →
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
stable-nenf : {Γ : Con} {A : Ty} (n : NN Γ A) →
              Σ[ v ∈ NV Γ A ] (eval ⌜ n ⌝NN > idenv ⇒ neu v  ×  qs v ⇒ n)

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
