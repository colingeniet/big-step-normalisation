module Normalisation.Stability where

open import Equality
open import Syntax
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Determinism
open import Normalisation.Termination

open import Agda.Builtin.Sigma renaming (_,_ to _,,_)


-- Stability : normalisation of a normal form does nothing.

-- Technical lemma : a variable evaluates to itself in the identity environment.
-- This requires an anoying weakenings and generalisations...
postulate
  vareval : {Γ Δ : Con} {A : Ty} (x : Var Γ A) →
            eval ⌜ x ⌝v > (idenv ++E Δ) ⇒ vneu (var (x ++v Δ))


-- A normal form can be normalised to itself.
stable : {Γ : Con} {A : Ty} (n : Nf Γ A) →
          Σ (Val Γ A) λ v →
          Σ (eval ⌜ n ⌝N > idenv ⇒ v) λ _ →
            q v ⇒ n
stables : {Γ : Con} {A : Ty} (n : Ne Nf Γ A) →
          Σ (Ne Val Γ A) λ v →
          Σ (eval ⌜ n ⌝NN > idenv ⇒ vneu v) λ _ →
            qs v ⇒ n

stable (nlam n) =
  let v ,, evaln ,, qv = stable n in
  vlam ⌜ n ⌝N idenv ,,
  evallam ⌜ n ⌝N idenv ,,
  q⟶ ($lam evaln) qv
stable (nneu n) =
  let v ,, evaln ,, qv = stables n in
  vneu v ,, evaln ,, qo qv
  
stables (var x) =
  var x ,, vareval x ,, qsvar
stables (app ne nf) =
  let nv ,, evalne ,, qsnv = stables ne in
  let v ,, evalnf ,, qv = stable nf in
  app nv v ,,
  eval[] (evals, evalsid evalnf) (evalapp evalne ($app nv v)) ,,
  qsapp qsnv qv


-- It follows by determinism that nf is stable on normal forms.
stability : {Γ : Con} {A : Ty} (n : Nf Γ A) → nf ⌜ n ⌝N ≡ n
stability n =
  let v ,, evaln ,, qv = stable n in
  norm-deterministic (nf-is-norm ⌜ n ⌝N) (qeval evaln qv)
