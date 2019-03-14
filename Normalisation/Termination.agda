{-# OPTIONS --cubical #-}

{-
  Proof of termination of eval and quote.
  
  Since eval and quote are defined as relation, termination means that
  every input is in relation with at least one output (in fact exactly one
  by determinism). The proof then allows to redifine eval/quote/nf as actual
  functions.
-}

module Normalisation.Termination where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Terms.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Eliminator
open import Normalisation.TermLike
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.Values.Sets
open import Normalisation.Evaluator
open import Normalisation.Evaluator.Weakening
open import Normalisation.Completeness
open import Normalisation.StrongComputability

{-
  Main theorem: any term in a strongly computable environment evaluates
  to a strongly computable value.
-}

-- The result type of the theorem.
terminatesTm : {Γ Δ : Con} {A : Ty} (u : Tm Δ A) (ρ : Env Γ Δ) → Set
terminatesTm {Γ} {A = A} u ρ = Σ[ uρ ∈ Val Γ A ] (eval u > ρ ⇒ uρ  ×  scv uρ)

terminatesTms : {Γ Δ Θ : Con} (σ : Tms Δ Θ) (ρ : Env Γ Δ) → Set
terminatesTms {Γ} {Θ = Θ} σ ρ = Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ)

-- Weakening of the result.
_++terminatesTm_ : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} →
                 terminatesTm u ρ → (Ψ : Con) → terminatesTm u (ρ ++E Ψ)
(uρ ,, evalu ,, scvuρ) ++terminatesTm Ψ =
  uρ ++V Ψ ,, evalwks evalu Ψ ,, scvuρ ++scv Ψ

_++terminatesTms_ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} →
                  terminatesTms σ ρ → (Ψ : Con) → terminatesTms σ (ρ ++E Ψ)
(σρ ,, evalsσ ,, sceσρ) ++terminatesTms Ψ =
  σρ ++E Ψ ,, evalswks evalsσ Ψ ,, sceσρ ++sce Ψ


{-
  The proof is by induction on terms. Except for the case of λ-abstractions,
  it is only a matter of applying the hypothesis to each other,
  and reorganising them to get the result.

  The function must be made non-mutually inductive to allow for the correct
  order of cases (the image of paths can only be defined after the image of
  regular constructors).
-}
evalsce-type : {i : term-index} → term i → Set
evalsce-type {Tm-i Δ A} u = {Γ : Con} {ρ : Env Γ Δ} → sce ρ → terminatesTm u ρ
evalsce-type {Tms-i Δ Θ} σ = {Γ : Con} {ρ : Env Γ Δ} → sce ρ → terminatesTms σ ρ


isSet-evalsce-type : {i : term-index} {x : term i} → isSet (evalsce-type x)
isSet-evalsce-type {Tm-i Δ A} {u} p q i j {Γ} {ρ} sceρ =
  isset (λ k _ _ sceρ → p k sceρ)
        (λ k _ _ sceρ → q k sceρ)
        i j Γ ρ sceρ
  where
    -- Make all arguments explicit to proven that it is a set.
    isset : isSet ((Γ : Con) (ρ : Env Γ Δ) → sce ρ →
                   Σ[ uρ ∈ Val Γ A ] (eval u > ρ ⇒ uρ  ×  scv uρ))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetVal (isSet× (PropisSet isPropeval) isSetscv)
isSet-evalsce-type {Tms-i Δ Θ} {σ} p q i j {Γ} {ρ} sceρ =
  isset (λ k _ _ sceρ → p k sceρ)
        (λ k _ _ sceρ → q k sceρ)
        i j Γ ρ sceρ
  where
    -- Make all arguments explicit when proving that it is a set.
    isset : isSet ((Γ : Con) (ρ : Env Γ Δ) → sce ρ →
                   Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetEnv (isSet× (PropisSet isPropevals) isSetsce)

evalsce : {i : term-index} (x : term i) → evalsce-type x



++evalsce≡ : {Δ : Con} {A : Ty} (u : Tm Δ A)
             {Γ : Con} {ρ : Env Γ Δ} (sceρ : sce ρ) (Ψ : Con) →
            evalsce u (sceρ ++sce Ψ) ≡ (evalsce u sceρ) ++terminatesTm Ψ
++evalssce≡ : {Δ Θ : Con} (σ : Tms Δ Θ)
              {Γ : Con} {ρ : Env Γ Δ} (sceρ : sce ρ) (Ψ : Con) →
              evalsce σ (sceρ ++sce Ψ) ≡ (evalsce σ sceρ) ++terminatesTms Ψ


-- Base constructors.
evalsce (u [ σ ]) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uσρ ,, evalu ,, scvuσρ = evalsce u sceσρ in
  uσρ ,, eval[] evalsσ evalu ,, scvuσρ
evalsce (π₂ σ) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  π₂list σρ ,, evalπ₂ evalsσ ,, π₂sce sceσρ
evalsce (lam u) {ρ = ρ} sceρ =
  -- Evaluation is trivial for functions.
  lam u ρ ,, evallam u ρ ,,
  -- Strong computability is not an immediate hypothesis.
  λ {Θ} {v} scvv →
  -- However, once given an argument to the function, it suffice to evaluate
  -- the function in the appropriate environment to get the result by induction
  -- hypothesis (with a few weakenings and transports, of course).
  let uρv ,, evalu ,, scvuρv = evalsce u (sceρ ++sce Θ ,, scvv)
      evallamu = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Θ}) ($lam evalu) in
  uρv ,, evallamu ,, scvuρv
evalsce (app f) sceρ =
  let f ,, evalf ,, scvf = evalsce f (π₁sce sceρ)
      fρ ,, $fρ ,, scvfρ = scvf (π₂sce sceρ) in
  fρ ,, evalapp evalf $fρ ,, scvfρ

evalsce id {ρ = ρ} sceρ =
  ρ ,, evalsid ,, sceρ
evalsce (σ ∘ ν) sceρ =
  let νρ ,, evalsν ,, sceνρ = evalsce ν sceρ
      σνρ ,, evalsσ ,, sceσνρ = evalsce σ sceνρ in
  σνρ ,, evals∘ evalsν evalsσ ,, sceσνρ
evalsce ε _ =
  ε ,, evalsε ,, tt
evalsce (σ , u) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uρ ,, evalu ,, scvuρ = evalsce u sceρ in
  σρ , uρ ,, evals, evalsσ evalu ,, (sceσρ ,, scvuρ)
evalsce (π₁ σ) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  π₁list σρ ,, evalsπ₁ evalsσ ,, π₁sce sceσρ

-- Path constructors.
evalsce (id∘ {σ = σ} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals id∘
                   (evals∘ evalsσ evalsid) evalsσ i ,,
  sceσρ
evalsce (∘id {σ = σ} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals ∘id
                   (evals∘ evalsid evalsσ) evalsσ i ,,
  sceσρ
evalsce (∘∘ {σ = σ} {ν} {δ} i) {ρ = ρ} sceρ =
  let δρ ,, evalsδ ,, sceδρ = evalsce δ sceρ
      νδρ ,, evalsν ,, sceνδρ = evalsce ν sceδρ
      σνδρ ,, evalsσ ,, sceσνδρ = evalsce σ sceνδρ in
  σνδρ ,,
  isPropDependent {B = λ σ → evals σ > ρ ⇒ σνδρ} isPropevals ∘∘
                   (evals∘ evalsδ (evals∘ evalsν evalsσ))
                   (evals∘ (evals∘ evalsδ evalsν) evalsσ) i ,,
  sceσνδρ
evalsce (εη {σ = σ} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  envεη σρ i ,,
  isPropPath {B = λ i → evals εη i > _ ⇒ envεη σρ i} isPropevals
              evalsσ evalsε i ,,
  sceεη sceσρ i
  where envεη : {Γ : Con} (σ : Env Γ ●) → σ ≡ ε
        envεη ε = refl
        sceεη : {Γ : Con} {σ : Env Γ ●} (sceσ : sce σ) →
                sceσ ≡[ ap sce (envεη σ) ]≡ tt
        sceεη {σ = ε} tt = refl
evalsce (π₁β {σ = σ} {u} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uρ ,, evalu ,, scvuρ = evalsce u sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals π₁β
                   (evalsπ₁ (evals, evalsσ evalu)) evalsσ i ,,
  sceσρ
evalsce (π₂β {σ = σ} {u} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uρ ,, evalu ,, scvuρ = evalsce u sceρ in
  uρ ,,
  isPropDependent {B = λ u → eval u > _ ⇒ uρ} isPropeval π₂β
                   (evalπ₂ (evals, evalsσ evalu)) evalu i ,,
  scvuρ
evalsce (πη {σ = σ} i) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ in
  πηlist {ρ = σρ} i  ,,
  isPropPath {B = λ i → evals πη i > _ ⇒ πηlist {ρ = σρ} i} isPropevals
              (evals, (evalsπ₁ evalsσ) (evalπ₂ evalsσ)) evalsσ i ,,
  πηsce sceσρ i
evalsce (,∘ {σ = σ} {ν} {u} i) {ρ = ρ} sceρ =
  let νρ ,, evalsν ,, sceνρ = evalsce ν sceρ
      σνρ ,, evalsσ ,, sceσνρ = evalsce σ sceνρ
      uνρ ,, evalu ,, scvuνρ = evalsce u sceνρ
      σuνρ = σνρ , uνρ in
  σuνρ ,,
  isPropDependent {B = λ σ → evals σ > ρ ⇒ σuνρ} isPropevals ,∘
                   (evals∘ evalsν (evals, evalsσ evalu))
                   (evals, (evals∘ evalsν evalsσ)
                           (eval[] evalsν evalu)) i ,,
  (sceσνρ ,, scvuνρ)
evalsce (β {u = u} i) {ρ = ρ} sceρ =
  let uρ ,, evalu ,, scvuρ = evalsce u sceρ
      uρ' ,, evalu' ,, scvuρ' = evalsce u {ρ = π₁list ρ , π₂list ρ}
                                        (π₁sce sceρ ,, π₂sce sceρ)
      uρ'≡uρ : uρ' ≡ uρ
      uρ'≡uρ i = fst (evalsce u (πηsce sceρ i))
      scvuρ'≡scvuρ : scvuρ' ≡[ ap scv uρ'≡uρ ]≡ scvuρ
      scvuρ'≡scvuρ i = snd (snd (evalsce u (πηsce sceρ i)))
  in
  uρ'≡uρ i ,,
  isPropPath {B = λ i → eval β i > ρ ⇒ uρ'≡uρ i} isPropeval
              -- This is just the result of evalsce on  app (lam u) ρ
              -- The transport does nothing, but is required to match
              -- the definition.
              (evalapp (evallam u (π₁list ρ))
                       (tr (λ u → u $ π₂list ρ ⇒ uρ')
                           ([]++V {Θ = ●})
                           ($lam evalu')))
              evalu i ,,
  scvuρ'≡scvuρ i
evalsce (η {f = f} i) {ρ = ρ} sceρ =
  let fρ ,, evalf ,, scvfρ = evalsce f sceρ
      fρ' = Val.lam (app f) ρ
      evalf' = evallam (app f) ρ
      fρ'≡fρ : fρ' ≡ fρ
      fρ'≡fρ = veq (ap (λ u → u [ _ ]) η ∙ eval≡ evalf)
  in
  fρ'≡fρ i ,,
  isPropPath {B = λ i → eval η i > ρ ⇒ fρ'≡fρ i} isPropeval
             evalf' evalf i ,,
  λ {Θ} {v} scvv →
  let fρv ,, $fρv ,, scvfρv = scvfρ scvv
      fρ+ ,, evalf+ ,, scvfρ+ = evalsce f (sceρ ++sce Θ)
      fρv+ ,, $fρv+ ,, scvfρv+ = scvfρ+ {Δ = ●} scvv
      evalfρv+ = evalapp {ρ = ρ ++E Θ , v} evalf+ $fρv+
      $lamappfρv = tr (λ u → u $ v ⇒ fρv+) ([]++V {Θ = Θ}) ($lam evalfρv+)
      fρv+≡fρv : fρv+ ≡ fρv
      fρv+≡fρv = veq (eval$≡ $fρv+ ⁻¹
                     ∙ ap (λ x → x $ _)
                          (eval≡ evalf+ ⁻¹
                          ∙ ap (λ σ → f [ σ ]) (++E≡ {Θ = Θ} {σ = ρ})
                          ∙ []++
                          ∙ ap (λ x → x ++t Θ) (eval≡ evalf)
                          ∙ ++V≡ {Θ = Θ} ⁻¹)
                     ∙ eval$≡ $fρv)
      fρ+≡fρ : fρ+ ≡ fρ ++V Θ
      fρ+≡fρ = ap fst (++evalsce≡ f sceρ Θ)
      scvfρ+≡scvfρ : (λ {Δ} {u} → scvfρ+ {Δ} {u})
                     ≡[ ap scv fρ+≡fρ ]≡
                     (λ {Δ} {u} → ((λ {Δ} → scvfρ {Δ}) ++scv Θ) {Δ} {u})
      scvfρ+≡scvfρ = λ i {Δ} {u} →  snd (snd (++evalsce≡ f sceρ Θ i)) {Δ} {u}
      scvfρv+≡scvfρv : scvfρv+ ≅⟨ scv ⟩ scvfρv
      scvfρv+≡scvfρv = {!!}
      scvfρv+≡scvfρv : scvfρv+ ≡[ ap scv fρv+≡fρv ]≡ scvfρv
      scvfρv+≡scvfρv = ≅-to-≡[] {B = scv} isSetVal scvfρv+≡scvfρv
  in
  fρv+≡fρv i ,,
  isPropPath {B = λ i → (fρ'≡fρ i ++V Θ) $ v ⇒ (fρv+≡fρv i)} isProp$
             $lamappfρv $fρv i ,,
  scvfρv+≡scvfρv i
evalsce (lam[] {A = A} {u = u} {σ} i) {Δ} {ρ} sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uσρ = Val.lam u σρ
      evaluσρ : eval (lam u [ σ ]) > ρ ⇒ uσρ
      evaluσρ = eval[] evalsσ (evallam u σρ)
      uσρ' = Val.lam (u [ σ ↑ A ]) ρ
      evaluσρ' : eval (lam (u [ σ ↑ A ])) > ρ ⇒ uσρ'
      evaluσρ' = evallam (u [ σ ↑ A ]) ρ
      uσρ≡uσρ' : uσρ ≡ uσρ'
      uσρ≡uσρ' = veq (ap (λ σ → lam u [ σ ])
                               (evals≡ evalsσ ⁻¹)
                           ∙ [][] ∙ ap (λ u → u [ ⌜ ρ ⌝E ]) lam[])
  in
  uσρ≡uσρ' i ,,
  isPropPath {B = λ i → eval (lam[] i) > ρ ⇒ uσρ≡uσρ' i} isPropeval
             evaluσρ evaluσρ' i ,,
  λ {Θ} {v} scvv →
  let uσρv ,, evalu ,, scvuσρv = evalsce u (sceσρ ++sce Θ ,, scvv)
      evaluσρv = tr (λ u → u $ v ⇒ uσρv) ([]++V {Θ = Θ}) ($lam evalu)
      σρ' ,, evalsσ' ,, sceσρ' = evalsce σ (sceρ ++sce Θ)
      evalsσρ' : evals (σ ∘ wk) > (ρ ++E Θ , v) ⇒ σρ'
      evalsσρ' = evals∘ (evalsπ₁ evalsid) evalsσ'
      σρv' = σρ' , v
      evalsσρv' : evals (σ ↑ A) > (ρ ++E Θ , v) ⇒ σρv'
      evalsσρv' = evals, evalsσρ' (evalπ₂ evalsid)
      sceσρv' : sce σρv'
      sceσρv' = sceσρ' ,, scvv
      uσρv' ,, evalu' ,, scvuσρv' = evalsce u sceσρv'
      evaluσ' : eval (u [ σ ↑ A ]) > (ρ ++E Θ , v) ⇒ uσρv'
      evaluσ' = eval[] evalsσρv' evalu'
      evaluσρv' = tr (λ u → u $ v ⇒ uσρv') ([]++V {Θ = Θ}) ($lam evaluσ')
      uσρv≡uσρv' : uσρv ≡ uσρv'
      uσρv≡uσρv' = veq (eval$≡ evaluσρv ⁻¹
                       ∙ ap (λ u → ⌜ u ++V Θ ⌝V $ ⌜ v ⌝V) uσρ≡uσρ'
                       ∙ eval$≡ evaluσρv')
      scvuσρv≡scvuσρv' : scvuσρv ≡[ ap scv uσρv≡uσρv' ]≡ scvuσρv'
      scvuσρv≡scvuσρv' = change-underlying {B = scv} isSetVal
        (λ i → snd (snd (evalsce u {ρ = fst (++evalssce≡ σ {ρ = ρ} sceρ Θ (1- i)) , v}
                                 ((snd (snd (++evalssce≡ σ {ρ = ρ} sceρ Θ (1- i)))) ,, scvv))))
  in
  uσρv≡uσρv' i ,,
  isPropPath {B = λ i → (uσρ≡uσρ' i ++V Θ) $ v ⇒ uσρv≡uσρv' i} isProp$
             evaluσρv evaluσρv' i ,,
  scvuσρv≡scvuσρv' i

evalsce {Tm-i Δ A} (isSetTm p q i j) =
  isSetDependent2 {B = evalsce-type} isSetTm
                  (λ {u : Tm Δ A} → isSet-evalsce-type {x = u})
                  (λ k → evalsce (p k)) (λ k → evalsce (q k)) i j
evalsce {Tms-i Δ Θ} (isSetTms p q i j) =
  isSetDependent2 {B = evalsce-type} isSetTms
                  (λ {σ : Tms Δ Θ} → isSet-evalsce-type {x = σ})
                  (λ k → evalsce (p k)) (λ k → evalsce (q k)) i j



++evalsce≡ (u [ σ ]) {ρ = ρ} sceρ Ψ i =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      uσρ ,, evalu ,, scvuσρ = evalsce u sceσρ
      evaluσ = eval[] evalsσ evalu
      σρ' ,, evalsσ' ,, sceσρ' = evalsce σ (sceρ ++sce Ψ)
      uσρ' ,, evalu' ,, scvuσρ' = evalsce u sceσρ'
      evaluσ' = eval[] evalsσ' evalu'
      uσρ'≡uσρ : uσρ' ≡ uσρ ++V Ψ
      uσρ'≡uσρ = veq (eval≡ evaluσ' ⁻¹ ∙ eval≡ (evalwks evaluσ Ψ))
      scvuσρ'≡scvuσρ : scvuσρ' ≅⟨ scv ⟩ scvuσρ ++scv Ψ
      scvuσρ'≡scvuσρ = ≡[]-to-≅ (apd (λ x → snd (snd (evalsce u (snd (snd x)))))
                                     (++evalssce≡ σ sceρ Ψ))
                       ∙≅ ≡[]-to-≅ (apd (λ x → snd (snd x))
                                        (++evalsce≡ u sceσρ Ψ))
      scvuσρ'≡scvuσρ : scvuσρ' ≡[ ap scv uσρ'≡uσρ ]≡ scvuσρ ++scv Ψ
      scvuσρ'≡scvuσρ = ≅-to-≡[] {B = scv} isSetVal scvuσρ'≡scvuσρ
  in
  uσρ'≡uσρ i ,,
  isPropPath {B = λ i → eval (u [ σ ]) > (ρ ++E Ψ) ⇒ uσρ'≡uσρ i} isPropeval
             evaluσ' (evalwks evaluσ Ψ) i ,,
  scvuσρ'≡scvuσρ i
++evalsce≡ (π₂ σ) {ρ = ρ} sceρ Ψ i =
  let σρ ,, evalsσ ,, sceσρ = evalsce σ sceρ
      σρ' ,, evalsσ' ,, sceσρ' = evalsce σ (sceρ ++sce Ψ)
      p = ++evalssce≡ σ sceρ Ψ
      σρ'≡σρ : σρ' ≡ σρ ++E Ψ
      σρ'≡σρ = ap fst p
      πσρ'≡πσρ : π₂list σρ' ≡ (π₂list σρ) ++V Ψ
      πσρ'≡πσρ = ap π₂list σρ'≡σρ ∙ π₂++ {Θ = Ψ} {σ = σρ}
      scvπσρ' = π₂sce sceσρ'
      scvπσρ = π₂sce sceσρ
      scvπσρ'≡scvπσρ : scvπσρ' ≅⟨ scv ⟩ scvπσρ ++scv Ψ
      scvπσρ'≡scvπσρ = ≡[]-to-≅ (apd (λ x → π₂sce (snd (snd x))) p)
                       ∙≅ ≡[]-to-≅ (π₂sce++ {sceσ = sceσρ})
      scvπσρ'≡scvπσρ : scvπσρ' ≡[ ap scv πσρ'≡πσρ ]≡ scvπσρ ++scv Ψ
      scvπσρ'≡scvπσρ = ≅-to-≡[] {B = scv} isSetVal scvπσρ'≡scvπσρ
  in πσρ'≡πσρ i ,,
     isPropPath {B = λ i → eval π₂ σ > ρ ++E Ψ ⇒ πσρ'≡πσρ i} isPropeval
                (evalπ₂ evalsσ') (evalwks (evalπ₂ evalsσ) Ψ) i ,,
     scvπσρ'≡scvπσρ i
++evalsce≡ (lam u) {ρ = ρ} sceρ Ψ i =
  let p = []++V {Θ = Ψ} {u = u} {ρ}
  in
  p i ,,
  isPropPath {B = λ i → eval lam u > ρ ++E Ψ ⇒ p i} isPropeval
             (evallam u (ρ ++E Ψ)) (evalwks (evallam u ρ) Ψ) i ,,
  λ {Θ} {v} scvv →
  let uρv ,, evalu ,, scvuρv = evalsce u ((sceρ ++sce Ψ) ++sce Θ ,, scvv)
      evallamu = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Θ}) ($lam evalu)
  in {!!} ,, {!!} ,, {!!}

++evalssce≡ id {ρ = ρ} sceρ Ψ i =
  ρ ++E Ψ ,, isPropevals evalsid (evalswks evalsid Ψ) i ,, sceρ ++sce Ψ
++evalssce≡ (σ ∘ ν) {ρ = ρ} sceρ Ψ i =
  let νρ ,, evalsν ,, sceνρ = evalsce ν ρ

{-
-- By stability and determinism, a value can only evaluate to itself.
-- Thus the previous theorem applied to values implies that every value
-- is strongly computable.
val-scv : {Γ : Con} {A : Ty} (v : Val Γ A) → scv v
val-scv {Γ = Γ} v =
  let _ ,, evalv ,, scvv = evalsce ⌜ v ⌝V (sceid {Γ}) in
  tr scv (eval-deterministic evalv (stable-val v)) scvv

env-sce : {Γ Δ : Con} (ρ : Env Γ Δ) → sce ρ
env-sce {Γ = Γ} ρ =
  let _ ,, evalsρ ,, sceρ = evalsce ⌜ ρ ⌝E (sceid {Γ}) in
  tr sce (evals-deterministic evalsρ (stable-env ρ)) sceρ


-- With those two results, it is easy to define eval, quote, norm...
-- as functions. Of course, those functions coincide with the relation.

eval : {Γ Δ : Con} {A : Ty} → Tm Δ A → Env Γ Δ → Val Γ A
eval u ρ = fst (evalsce u (env-sce ρ))

eval-is-eval : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} →
               eval u > ρ ⇒ (eval u ρ)
eval-is-eval {u = u} {ρ = ρ} = fst (snd (evalsce u (env-sce ρ)))


evals : {Γ Δ Θ : Con} → Tms Δ Θ → Env Γ Δ → Env Γ Θ
evals σ ρ = fst (evalsce σ (env-sce ρ))

evals-is-evals : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} →
               evals σ > ρ ⇒ (evals σ ρ)
evals-is-evals {σ = σ} {ρ = ρ} = fst (snd (evalsce σ (env-sce ρ)))


_$$_ : {Γ : Con} {A B : Ty} → Val Γ (A ⟶ B) → Val Γ A → Val Γ B
(vlam u ρ) $$ v = eval u (ρ , v)
(vneu n) $$ v = vneu (app n v)

$$-is-$ : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} {v : Val Γ A} →
          f $ v ⇒ (f $$ v)
$$-is-$ {f = vlam u ρ} {v = v} = $lam eval-is-eval
$$-is-$ {f = vneu n} {v = v} = $app n v


q : {Γ : Con} {A : Ty} → Val Γ A → Nf Γ A
q v = fst (scv-q (val-scv v))

q-is-q : {Γ : Con} {A : Ty} {v : Val Γ A} → q v ⇒ (q v)
q-is-q {v = v} = snd (scv-q (val-scv v))


qs : {Γ : Con} {A : Ty} → Ne Val Γ A → Ne Nf Γ A
qs (var x) = var x
qs (app n v) = app (qs n) (q v)

qs-is-qs : {Γ : Con} {A : Ty} {n : Ne Val Γ A} → qs n ⇒ (qs n)
qs-is-qs {n = var x} = qsvar
qs-is-qs {n = app n v} = qsapp qs-is-qs q-is-q


nf : {Γ : Con} {A : Ty} → Tm Γ A → Nf Γ A
nf u = q (eval u idenv)

nf-is-norm : {Γ : Con} {A : Ty} {u : Tm Γ A} → norm u ⇒ (nf u)
nf-is-norm = qeval eval-is-eval q-is-q



-- It is convenient to reprove the inductive definition of eval, quote,...
-- to simplify manipulation of their function versions.
-- Some of the cases do not hold definitionally and require the use of
-- determinism, the others are included for the sake of completeness.
eval[]≡ : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Tms Δ Θ} {ρ : Env Γ Δ} →
          eval (u [ σ ]) ρ ≡ eval u (evals σ ρ)
eval[]≡ {u = u} {σ = σ} =
  eval-deterministic (eval-is-eval {u = u [ σ ]})
                     (eval[] evals-is-evals eval-is-eval)

evalπ₂≡ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ} →
          eval (π₂ σ) ρ ≡ π₂list (evals σ ρ)
evalπ₂≡ = refl

evallam≡ : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} →
           eval (lam u) ρ ≡ vlam u ρ
evallam≡ = refl

evalapp≡ : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {ρ : Env Γ (Δ , A)} →
           eval (app f) ρ ≡ (eval f (π₁list ρ)) $$ (π₂list ρ)
evalapp≡ {f = f} {ρ = ρ} =
  eval-deterministic (eval-is-eval {u = app f} {ρ = ρ})
                     (evalapp eval-is-eval $$-is-$)

evalsid≡ : {Γ Δ : Con} {ρ : Env Γ Δ} → evals id ρ ≡ ρ
evalsid≡ = refl

evals∘≡ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {ρ : Env Γ Δ} →
          evals (σ ∘ ν) ρ ≡ evals σ (evals ν ρ)
evals∘≡ {σ = σ} {ν = ν} {ρ = ρ} =
  evals-deterministic (evals-is-evals {σ = σ ∘ ν})
                      (evals∘ evals-is-evals evals-is-evals)

evalsε≡ : {Γ Δ : Con} {ρ : Env Γ Δ} → evals ε ρ ≡ ε
evalsε≡ = refl 

evals,≡ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {u : Tm Δ A} {ρ : Env Γ Δ} →
          evals (σ , u) ρ ≡ (evals σ ρ , eval u ρ)
evals,≡ = refl

evalsπ₁≡ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ} →
           evals (π₁ σ) ρ ≡ π₁list (evals σ ρ)
evalsπ₁≡ = refl


$lam≡ : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} {v : Val Γ A} →
        (vlam u ρ) $$ v ≡ eval u (ρ , v)
$lam≡ = refl

$app≡ : {Γ : Con} {A B : Ty} {n : Ne Val Γ (A ⟶ B)} {v : Val Γ A} →
        (vneu n) $$ v ≡ vneu (app n v)
$app≡ = refl


qo≡ : {Γ : Con} {n : Ne Val Γ o} →
      q (vneu n) ≡ nneu (qs n)
qo≡ = q-deterministic q-is-q (qo qs-is-qs)

q⟶≡ : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} →
      q f ≡ nlam (q ((f +V A) $$ (vneu (var z))))
q⟶≡ {f = f} = q-deterministic (q-is-q {v = f}) (q⟶ $$-is-$ q-is-q)


qsvar≡ : {Γ : Con} {A : Ty} {x : Var Γ A} → qs (var x) ≡ (var x)
qsvar≡ = refl

qsapp≡ : {Γ : Con} {A B : Ty} {f : Ne Val Γ (A ⟶ B)} {u : Val Γ A} →
         qs (app f u) ≡ app (qs f) (q u)
qsapp≡ = refl
-}
