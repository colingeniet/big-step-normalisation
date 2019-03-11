{-# OPTIONS --cubical --allow-unsolved-meta #-}

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
open import Normalisation.Variables
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.Values.Sets
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Weakening
open import Normalisation.NormalForms.Sets
open import Normalisation.Evaluator
open import Normalisation.Evaluator.Weakening
open import Normalisation.Completeness
open import Normalisation.Stability


{-
  The proof of termination is based on the notion of strongly computable values.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

-- Definition of strongly computable values.
scv : {Γ : Con} {A : Ty} → Val Γ A → Set
-- At the base type, a value is strongly computable if quote is defined on it.
scv {Γ = Γ} {A = o} u = Σ (Nf Γ o) λ n → q u ⇒ n
-- For function types, a function is strongly computable if for any sc argument,
-- the application of that function to that argument gives a scv.
-- Furthermore, the argument may come from an extended environment, in which
-- case the function is to be weakened.
scv {Γ = Γ} {A = A ⟶ B} f =
  {Δ : Con} {u : Val (Γ ++ Δ) A} → scv u →
  Σ[ fu ∈ Val (Γ ++ Δ) B ] ((f ++V Δ) $ u ⇒ fu  ×  scv fu)



isSetscv : {Γ : Con} {A : Ty} {u : Val Γ A} → isSet (scv u)
isSetscv {A = o} {u} =
  isSetΣ isSetNf (PropisSet isPropq)
isSetscv {Γ} {A ⟶ B} {f} {x} {y} p q i j {Δ} {u} scvu =
  isset (λ k _ _ scvu → p k scvu)
        (λ k _ _ scvu → q k scvu)
        i j Δ u scvu
  where
    -- Make all arguments explicit.
    isset : isSet ((Δ : Con) (u : Val (Γ ++ Δ) A) → scv u →
                   Σ[ fu ∈ Val (Γ ++ Δ) B ] ((f ++V Δ) $ u ⇒ fu  ×  scv fu))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetVal (isSet× (PropisSet isProp$) isSetscv)



-- Strong computablility is stable by weakening.
_+scv_ : {Γ : Con} {B : Ty} {u : Val Γ B} → scv u → (A : Ty) → scv (u +V A)
_+scv_ {B = o} (n ,, qu) A = n +N A ,, qwk qu A
_+scv_ {B = B ⟶ C} {u = f} scvf A {Δ} {u} scvu =
  let u' = tr (λ Γ → Val Γ B) ,++ u in
  let u≡u' = trfill (λ Γ → Val Γ B) ,++ u in
  let scvu' = trd scv u≡u' scvu in
  let fu' ,, $fu' ,, scvfu' = scvf scvu' in
  let fu = tr (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let fu'≡fu = trfill (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let scvfu = trd scv fu'≡fu scvfu' in
  fu ,,
  (λ i → (V+-++≡ {Δ = Δ} {B = A} {u = f} (1- i)) $ (u≡u' (1- i)) ⇒
    (fu'≡fu i))
  * $fu' ,,
  scvfu
  where V+-++≡ : {Γ Δ : Con} {A B : Ty} {u : Val Γ A} →
                 (u +V B) ++V Δ ≡[ ap (λ Γ → Val Γ A) ,++ ]≡ u ++V ((● , B) ++ Δ)
        V+-++≡ {Δ = ●} = refl
        V+-++≡ {Δ = Δ , C} = apd (λ u → u +V C) (V+-++≡ {Δ = Δ})

_++scv_ : {Γ : Con} {B : Ty} {u : Val Γ B} → scv u → (Δ : Con) → scv (u ++V Δ)
u ++scv ● = u
u ++scv (Δ , A) = (u ++scv Δ) +scv A



{-
  Main lemma:
  The fact that strong computability implies termination of quote is actually
  not obvious. The proof requires to simultaneously prove the converse for
  neutral values.
-}
-- Main direction: strong computability implies termination of quote.
scv-q : {Γ : Con} {A : Ty} {u : Val Γ A} →
        scv u → Σ (Nf Γ A) (λ n → q u ⇒ n)
-- Converse for neutral values.
q-scv : {Γ : Con} {A : Ty} {u : Ne Val Γ A} {n : Ne Nf Γ A} →
        qs u ⇒ n → scv (neu u)

-- The converse allows in particular to show that variables are sc.
scvvar : {Γ : Con} {A : Ty} {x : Var Γ A} → scv (neu (var x))
scvvar = q-scv qsvar


scv-q {A = o} scu = scu
-- For functions, we follow the definition of quote and apply
-- the function to vz. This is why sc of variables is required.
scv-q {A = A ⟶ B} scu =
  let uz ,, $uz ,, scuz = scu {Δ = ● , A} (scvvar {x = z}) in
  let nfuz ,, quz = scv-q scuz in
  lam nfuz ,, q⟶ $uz quz


q-scv {A = o} {n = n} qu = neu n ,, qo qu
-- For functions, since we are considering neutral values, application
-- to a value is trivial. Quote simply quotes the function and the value
-- separately, hence the proof would be simple if it was not for a few
-- weakenings and transports.
q-scv {A = A ⟶ pB} {u = f} {n = nf} qf {Δ = Δ} {u = u} scu =
  let fu = app (f ++NV Δ) u in
  let $fu = tr (λ x → (x $ u ⇒ neu fu))
               (++VNV {v = f} ⁻¹)
               ($app (f ++NV Δ) u)
  in
  let nfu ,, qu = scv-q scu in
  neu fu ,, $fu ,, q-scv (qsapp (qswks qf Δ) qu)


-- Extension of strong computability to environments.
sce : {Γ Δ : Con} → Env Γ Δ → Set
sce ε = ⊤
sce (ρ , u) = sce ρ  ×  scv u

-- Associated projections.
π₁sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → sce (π₁list ρ)
π₁sce {ρ = _ , _} = fst

π₂sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → scv (π₂list ρ)
π₂sce {ρ = _ , _} = snd

πηsce : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} (sceσ : sce σ) →
        (π₁sce sceσ ,, π₂sce sceσ) ≡[ ap sce πηlist ]≡ sceσ
πηsce {σ = σ , u} (sceσ ,, scvu) = refl


isSetsce : {Γ Δ : Con} {σ : Env Γ Δ} → isSet (sce σ)
isSetsce {Δ = ●} {ε} = PropisSet isProp⊤
isSetsce {Δ = Δ , A} {ρ , u} = isSet× isSetsce isSetscv


-- Weakenings.
_+sce_ : {Γ Δ : Con} {ρ : Env Γ Δ} → sce ρ → (A : Ty) → sce (ρ +E A)
_+sce_ {ρ = ε} tt A = tt
_+sce_ {ρ = ρ , u} (sceρ ,, scvu) A = sceρ +sce A ,, scvu +scv A

_++sce_ : {Γ Θ : Con} {σ : Env Γ Θ} → sce σ → (Δ : Con) → sce (σ ++E Δ)
σ ++sce ● = σ
σ ++sce (Δ , A) = (σ ++sce Δ) +sce A

-- The identity environment is strongly computable.
sceid : {Γ : Con} → sce (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +sce A ,, scvvar



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
      uσρ ,, evalu ,, scvuσρ = IHu sceσρ in
  uσρ ,, eval[] evalsσ evalu ,, scvuσρ
Methods.π₂ᴹ evalsce-methods IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  π₂list σρ ,, evalπ₂ evalsσ ,, π₂sce sceσρ
Methods.lamᴹ evalsce-methods {Δ} {A} {B} {u} IHu {Γ} {ρ} sceρ =
  -- Evaluation is trivial for functions.
  lam u ρ ,, evallam u ρ ,,
  -- Strong computability is not an immediate hypothesis.
  λ {Θ} {v} scvv →
  -- However, once given an argument to the function, it suffice to evaluate
  -- the function in the appropriate environment to get the result by induction
  -- hypothesis (with a few weakenings and transports, of course).
  let uρv ,, evalu ,, scvuρv = IHu (sceρ ++sce Θ ,, scvv)
      evallamu = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Θ}) ($lam evalu) in
  uρv ,, evallamu ,, scvuρv
Methods.appᴹ evalsce-methods IHu sceρ =
  let f ,, evalf ,, scvf = IHu (π₁sce sceρ)
      fρ ,, $fρ ,, scvfρ = scvf (π₂sce sceρ) in
  fρ ,, evalapp evalf $fρ ,, scvfρ

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
  π₁list σρ ,, evalsπ₁ evalsσ ,, π₁sce sceσρ

Methods.id∘ᴹ evalsce-methods IHσ i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals id∘
                   (evals∘ evalsσ evalsid) evalsσ i ,,
  sceσρ
Methods.∘idᴹ evalsce-methods IHσ i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals ∘id
                   (evals∘ evalsid evalsσ) evalsσ i ,,
  sceσρ
Methods.∘∘ᴹ evalsce-methods IHσ IHν IHδ i {ρ = ρ} sceρ =
  let δρ ,, evalsδ ,, sceδρ = IHδ sceρ
      νδρ ,, evalsν ,, sceνδρ = IHν sceδρ
      σνδρ ,, evalsσ ,, sceσνδρ = IHσ sceνδρ in
  σνδρ ,,
  isPropDependent {B = λ σ → evals σ > ρ ⇒ σνδρ} isPropevals ∘∘
                   (evals∘ evalsδ (evals∘ evalsν evalsσ))
                   (evals∘ (evals∘ evalsδ evalsν) evalsσ) i ,,
  sceσνδρ
Methods.εηᴹ evalsce-methods IHσ i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  envεη σρ i ,,
  isPropPath {B = λ i → evals εη i > _ ⇒ envεη σρ i} isPropevals
              evalsσ evalsε i ,,
  sceεη sceσρ i
  where envεη : {Γ : Con} (σ : Env Γ ●) → σ ≡ ε
        envεη ε = refl
        sceεη : {Γ : Con} {σ : Env Γ ●} (sceσ : sce σ) →
                sceσ ≡[ ap sce (envεη σ) ]≡ tt
        sceεη {σ = ε} tt = refl
Methods.π₁βᴹ evalsce-methods IHσ IHu i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      uρ ,, evalu ,, scvuρ = IHu sceρ in
  σρ ,,
  isPropDependent {B = λ σ → evals σ > _ ⇒ σρ} isPropevals π₁β
                   (evalsπ₁ (evals, evalsσ evalu)) evalsσ i ,,
  sceσρ
Methods.π₂βᴹ evalsce-methods IHσ IHu i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      uρ ,, evalu ,, scvuρ = IHu sceρ in
  uρ ,,
  isPropDependent {B = λ u → eval u > _ ⇒ uρ} isPropeval π₂β
                   (evalπ₂ (evals, evalsσ evalu)) evalu i ,,
  scvuρ
Methods.πηᴹ evalsce-methods IHσ i sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  πηlist {ρ = σρ} i  ,,
  isPropPath {B = λ i → evals πη i > _ ⇒ πηlist {ρ = σρ} i} isPropevals
              (evals, (evalsπ₁ evalsσ) (evalπ₂ evalsσ)) evalsσ i ,,
  πηsce sceσρ i
Methods.βᴹ evalsce-methods {u = u} IHu i {ρ = ρ} sceρ =
  let uρ ,, evalu ,, scvuρ = IHu sceρ
      uρ' ,, evalu' ,, scvuρ' = IHu {ρ = π₁list ρ , π₂list ρ}
                                    (π₁sce sceρ ,, π₂sce sceρ)
  in
  fst (IHu (πηsce sceρ i)) ,,
  isPropPath {B = λ i → eval β i > ρ ⇒ fst (IHu (πηsce sceρ i))} isPropeval
              -- This is just the result of evalsce on  app (lam u) ρ
              -- The transport does nothing, but is required to match
              -- the definition.
              (evalapp (evallam u (π₁list ρ))
                       (tr (λ u → u $ π₂list ρ ⇒ uρ')
                           ([]++V {Θ = ●})
                           ($lam evalu')))
              evalu i ,,
  snd (snd (IHu (πηsce sceρ i)))
Methods.ηᴹ evalsce-methods {f = f} IHf i {ρ = ρ} sceρ =
  let fρ ,, evalf ,, scvfρ = IHf sceρ
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
      fρ+ ,, evalf+ ,, scvfρ+ = IHf (sceρ ++sce Θ)
      fρv' ,, $fρv' ,, scvfρv' = scvfρ+ {Δ = ●} scvv
      evalfρv' = evalapp {ρ = ρ ++E Θ , v} evalf+ $fρv'
      $lamappfρv = tr (λ u → u $ v ⇒ fρv') ([]++V {Θ = Θ}) ($lam evalfρv')
      fρv'≡fρv : fρv' ≡ fρv
      fρv'≡fρv = veq (eval$≡ $fρv' ⁻¹
                     ∙ ap (λ x → x $ _)
                          (eval≡ evalf+ ⁻¹
                          ∙ ap (λ σ → f [ σ ]) (++E≡ {Θ = Θ} {σ = ρ})
                          ∙ []++
                          ∙ ap (λ x → x ++t Θ) (eval≡ evalf)
                          ∙ ++V≡ {Θ = Θ} ⁻¹)
                     ∙ eval$≡ $fρv)
      scvfρv'≡scvfρv : scvfρv' ≡[ ap scv fρv'≡fρv ]≡ scvfρv
      scvfρv'≡scvfρv = {!!}
  in
  fρv'≡fρv i ,,
  {!!} ,,
  scvfρv'≡scvfρv i
Methods.lam[]ᴹ evalsce-methods {u = u} {σ} IHu IHσ i {ρ = ρ} sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  {!!} ,, {!!} ,, {!!}
Methods.,∘ᴹ evalsce-methods IHσ IHν IHu i {ρ = ρ} sceρ =
  let νρ ,, evalsν ,, sceνρ = IHν sceρ
      σνρ ,, evalsσ ,, sceσνρ = IHσ sceνρ
      uνρ ,, evalu ,, scvuνρ = IHu sceνρ
      σuνρ = σνρ , uνρ in
  σuνρ ,,
  isPropDependent {B = λ σ → evals σ > ρ ⇒ σuνρ} isPropevals ,∘
                   (evals∘ evalsν (evals, evalsσ evalu))
                   (evals, (evals∘ evalsν evalsσ)
                           (eval[] evalsν evalu)) i ,,
  (sceσνρ ,, scvuνρ)

Methods.isSetTmᴹ evalsce-methods {Δ} {A} {u} p q i j {Γ} {ρ} sceρ =
  isset (λ k _ _ sceρ → p k sceρ)
        (λ k _ _ sceρ → q k sceρ)
        i j Γ ρ sceρ
  where
    -- Make all arguments explicit when proving that it is a set.
    isset : isSet ((Γ : Con) (ρ : Env Γ Δ) → sce ρ →
                   Σ[ uρ ∈ Val Γ A ] (eval u > ρ ⇒ uρ  ×  scv uρ))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetVal (isSet× (PropisSet isPropeval) isSetscv)

Methods.isSetTmsᴹ evalsce-methods {Δ} {Θ} {σ} p q i j {Γ} {ρ} sceρ =
  isset (λ k _ _ sceρ → p k sceρ)
        (λ k _ _ sceρ → q k sceρ)
        i j Γ ρ sceρ
  where
    -- Make all arguments explicit when proving that it is a set.
    isset : isSet ((Γ : Con) (ρ : Env Γ Δ) → sce ρ →
                   Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetEnv (isSet× (PropisSet isPropevals) isSetsce)


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
  let _ ,, evalsρ ,, sceρ = evalssce ⌜ ρ ⌝E (sceid {Γ}) in
  tr sce (evals-deterministic evalsρ (stable-env ρ)) sceρ


-- With those two results, it is easy to define eval, quote, norm...
-- as functions. Of course, those functions coincide with the relation.

eval : {Γ Δ : Con} {A : Ty} → Tm Δ A → Env Γ Δ → Val Γ A
eval u ρ = fst (evalsce u (env-sce ρ))

eval-is-eval : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} →
               eval u > ρ ⇒ (eval u ρ)
eval-is-eval {u = u} {ρ = ρ} = fst (snd (evalsce u (env-sce ρ)))


evals : {Γ Δ Θ : Con} → Tms Δ Θ → Env Γ Δ → Env Γ Θ
evals σ ρ = fst (evalssce σ (env-sce ρ))

evals-is-evals : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} →
               evals σ > ρ ⇒ (evals σ ρ)
evals-is-evals {σ = σ} {ρ = ρ} = fst (snd (evalssce σ (env-sce ρ)))


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
