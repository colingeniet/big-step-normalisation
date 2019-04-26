{-# OPTIONS --cubical #-}

{-
  Proof of termination of eval and quote.
  
  Since eval and quote are defined as relation, termination means that
  every input is in relation with at least one output (in fact exactly one
  by determinism). The proof then allows to redifine eval/quote/nf as actual
  functions.
-}

module BSN.Termination where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Terms.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Eliminator
  hiding (Methods)
  renaming (PropMethods to Methods)
open import Weakening.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import Value.Sets
open import Evaluator.Evaluator
open import BSN.Completeness
open import BSN.Soundness
open import BSN.StrongComputability



{-
  Main theorem: any term in a strongly computable environment evaluates
  to a strongly computable value.
  The proof is by induction on terms. Except for the case of λ-abstractions,
  it is only a matter of applying the hypothesis to each other,
  and reorganising them to get the result.
-}
evalsce : {Δ : Con} {A : Ty} (u : Tm Δ A) {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
          Σ[ uρ ∈ Val Γ A ] (eval u > ρ ⇒ uρ  ×  scv uρ)
evalssce : {Δ Θ : Con} (σ : Tms Δ Θ) {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
           Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ)

-- The theorem is defined using the eliminator.
evalsce-motives : Motives
open Motives evalsce-motives
Motives.Tmᴹ evalsce-motives {Δ} {A} u =
  {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
  Σ[ uρ ∈ Val Γ A ] (eval u > ρ ⇒ uρ  ×  scv uρ)
Motives.Tmsᴹ evalsce-motives {Δ} {Θ} σ =
  {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
  Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ)

evalsce-methods : Methods evalsce-motives
open Methods evalsce-methods

evalsce = elimTm
evalssce = elimTms


Methods._[_]ᴹ evalsce-methods IHu IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      uσρ ,, evalu ,, scvuσρ = IHu sceσρ
  in uσρ ,, eval[] evalsσ evalu ,, scvuσρ
Methods.π₂ᴹ evalsce-methods IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
  in π₂E σρ ,, evalπ₂ evalsσ ,, π₂sce sceσρ
Methods.lamᴹ evalsce-methods {u = u} IHu {ρ = ρ} sceρ =
  lam u ρ ,, evallam u ρ ,,
  λ σ {v} scvv →
  let uρv ,, evalu ,, scvuρv = IHu {ρ = ρ +E σ , v} (sceρ +sce σ ,, scvv)
  in uρv ,, $lam evalu ,, scvuρv
Methods.appᴹ evalsce-methods IHf sceρ =
  let f ,, evalf ,, scvf = IHf (π₁sce sceρ)
      fρ ,, $fρ ,, scvfρ = scvf idw (π₂sce sceρ)
      $fρ = tr (λ x → x $ _ ⇒ _) +Vid $fρ
  in fρ ,, evalapp evalf $fρ ,, scvfρ

Methods.idᴹ evalsce-methods {ρ = ρ} sceρ =
  ρ ,, evalsid ,, sceρ
Methods._∘ᴹ_ evalsce-methods IHσ IHν sceρ =
  let νρ ,, evalsν ,, sceνρ = IHν sceρ
      σνρ ,, evalsσ ,, sceσνρ = IHσ sceνρ in
  σνρ ,, evals∘ evalsν evalsσ ,, sceσνρ
Methods.εᴹ evalsce-methods _ =
  ε ,, evalsε ,, tt
Methods._,ᴹ_ evalsce-methods IHσ IHu sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      uρ ,, evalu ,, scvuρ = IHu sceρ in
  σρ , uρ ,, evals, evalsσ evalu ,, (sceσρ ,, scvuρ)
Methods.π₁ᴹ evalsce-methods IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  π₁E σρ ,, evalsπ₁ evalsσ ,, π₁sce sceσρ

Methods.isPropTmᴹ evalsce-methods {Δ} {A} {u} x y i {Γ} {ρ} sceρ =
  let uρ ,, evalu ,, scvuρ = x sceρ
      uρ' ,, evalu' ,, scvuρ' = y sceρ
      uρ≡uρ' : uρ ≡ uρ'
      uρ≡uρ' = eval-sound evalu evalu'
  in uρ≡uρ' i ,,
     isPropDependent {B = λ x → eval u > ρ ⇒ x} isPropeval
                     uρ≡uρ' evalu evalu' i ,,
     isPropDependent {B = scv} isPropscv uρ≡uρ' scvuρ scvuρ' i
Methods.isPropTmsᴹ evalsce-methods {Δ} {Θ} {σ} x y i {Γ} {ρ} sceρ =
  let σρ ,, evalsσ ,, scvσρ = x sceρ
      σρ' ,, evalsσ' ,, scvσρ' = y sceρ
      σρ≡σρ' : σρ ≡ σρ'
      σρ≡σρ' = evals-sound evalsσ evalsσ'
  in σρ≡σρ' i ,,
     isPropDependent {B = λ x → evals σ > ρ ⇒ x} isPropevals
                     σρ≡σρ' evalsσ evalsσ' i ,,
     isPropDependent {B = sce} isPropsce σρ≡σρ' scvσρ scvσρ' i



{-
-- By stability and determinism, a value can only evaluate to itself.
-- Thus the previous theorem applied to values implies that every value
-- is strongly computable.
val-scv : {Γ : Con} {A : Ty} (v : Val Γ A) → scv v
val-scv {Γ = Γ} v =
  let v' ,, evalv ,, scvv' = evalsce ⌜ v ⌝V (sceid {Γ})
      v'≡v = veq (eval≡ evalv ⁻¹ ∙ eval≡ (stable-val v))
  in tr scv v'≡v scvv'

env-sce : {Γ Δ : Con} (ρ : Env Γ Δ) → sce ρ
env-sce {Γ = Γ} ρ =
  let ρ' ,, evalsρ ,, sceρ' = evalssce ⌜ ρ ⌝E (sceid {Γ})
      ρ'≡ρ = enveq (evals≡ evalsρ ⁻¹ ∙ evals≡ (stable-env ρ))
  in tr sce ρ'≡ρ sceρ'
-}
