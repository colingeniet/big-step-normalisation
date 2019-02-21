{-# OPTIONS --without-K #-}

module Normalisation.Termination where

open import Equality
open import Syntax
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Determinism
open import Normalisation.Stability

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)


-- Strongly computable values.
SCV : {Γ : Con} {A : Ty} → Val Γ A → Set
-- At the base type, a value is strongly computable if it can be normalized by q.
SCV {Γ = Γ} {A = o} u = Σ (Nf Γ o) λ n → q u ⇒ n
-- For function types, a value is strongly computable if for any SC argument value
-- in an extended context, the application of that function to that argument
-- gives a SCV.
SCV {Γ = Γ} {A = A ⟶ B} f =
  {Δ : Con} {u : Val (Γ ++ Δ) A} → SCV u →
  Σ (Val (Γ ++ Δ) B) λ fu →
  Σ ((f ++V Δ) $ u ⇒ fu) λ _ →
    SCV fu


-- Lemma : SCV is stable by context extension.
postulate
  _+SCV_ : {Γ : Con} {B : Ty} {u : Val Γ B} → SCV u → (A : Ty) → SCV (u +V A)
{-
_+SCV_ {B = o} (n ,, qu) A = n +N A ,, qwk qu A
_+SCV_ {B = B ⟶ C} {u = f} scvf A {Δ} {u} scvu =
  let u' = tr (λ Γ → Val Γ B) ,++ u in
  let u≡u' = trfill (λ Γ → Val Γ B) ,++ u in
  let scvu' = trd SCV u≡u' scvu in
  let fu' ,, $fu' ,, scvfu' = scvf scvu' in
  let fu = tr (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let fu'≡fu = trfill (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let scvfu = trd SCV fu'≡fu scvfu' in
  fu ,, {!!} ,, scvfu
-}

_++SCV_ : {Γ : Con} {B : Ty} {u : Val Γ B} → SCV u → (Δ : Con) → SCV (u ++V Δ)
u ++SCV ● = u
u ++SCV (Δ , A) = (u ++SCV Δ) +SCV A


-- Main lemma : SCV is ~ equivalent to the termination of q.
-- Main direction (actual goal).
scv-q : {Γ : Con} {A : Ty} {u : Val Γ A} →
        SCV u → Σ (Nf Γ A) (λ n → q u ⇒ n)
-- The reciprocal on neutral terms is required for the induction
q-scv : {Γ : Con} {A : Ty} {u : Ne Val Γ A} {n : Ne Nf Γ A} →
        qs u ⇒ n → SCV (vneu u)

-- The second part of the lemma allows to prove that variables are strongly computable.
scvvar : {Γ : Con} {A : Ty} {x : Var Γ A} → SCV (vneu (var x))
scvvar = q-scv qsvar

scv-q {A = o} scu = scu
scv-q {A = A ⟶ B} scu =
  let uz ,, $uz ,, scuz = scu {Δ = ● , A} (scvvar {x = z}) in
  let nfuz ,, quz = scv-q scuz in
  nlam nfuz ,, q⟶ $uz quz

q-scv {A = o} {n = n} qu = nneu n ,, qo qu
q-scv {A = A ⟶ B} {u = f} {n = nf} qf {Δ = Δ} {u = u} scu =
  let fu = app (f ++NV Δ) u in
  let $fu = tr (λ x → (x $ u ⇒ vneu fu))
               (vneu++V {u = f} ⁻¹)
               ($app (f ++NV Δ) u)
  in
  let nfu ,, qu = scv-q scu in
  vneu fu ,, $fu ,, q-scv (qsapp (qswks qf Δ) qu)
  where vneu++V : ∀ {Γ Δ : Con} {A : Ty} {u : Ne Val Γ A} →
                    (vneu u) ++V Δ ≡ vneu (u ++NV Δ)
        vneu++V {Δ = ●} = refl
        vneu++V {Δ = Δ , B} = ap (λ x → x +V B) (vneu++V {Δ = Δ})


-- Extension of strong computability to environments.
SCE : {Γ Δ : Con} → Env Γ Δ → Set
SCE ε = ⊤
SCE (ρ , u) = Σ (SCE ρ) λ _ → SCV u

π₁SCE : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        SCE ρ → SCE (π₁list ρ)
π₁SCE {ρ = _ , _} = fst

π₂SCE : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        SCE ρ → SCV (π₂list ρ)
π₂SCE {ρ = _ , _} = snd


_+SCE_ : {Γ Δ : Con} {ρ : Env Γ Δ} → SCE ρ → (A : Ty) → SCE (ρ +E A)
_+SCE_ {ρ = ε} tt A = tt
_+SCE_ {ρ = ρ , u} (sceρ ,, scvu) A = sceρ +SCE A ,, scvu +SCV A

_++SCE_ : {Γ Θ : Con} {σ : Env Γ Θ} → SCE σ → (Δ : Con) → SCE (σ ++E Δ)
σ ++SCE ● = σ
σ ++SCE (Δ , A) = (σ ++SCE Δ) +SCE A

sceid : {Γ : Con} → SCE (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +SCE A ,, scvvar



-- Main theorem : Evaluation in a strongly computable environment gives a
-- strongly computable result.
evalsce : {Γ Δ : Con} {A : Ty} (u : Tm Δ A) {ρ : Env Γ Δ} → SCE ρ →
          Σ (Val Γ A) λ uρ →
          Σ (eval u > ρ ⇒ uρ) λ _ →
            SCV uρ
evalssce : {Γ Δ Θ : Con} (σ : Tms Δ Θ) {ρ : Env Γ Δ} → SCE ρ →
           Σ (Env Γ Θ) λ σρ →
           Σ (evals σ > ρ ⇒ σρ) λ _ →
            SCE σρ

evalsce (u [ σ ]) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalssce σ sceρ in
  let uσρ ,, evalu ,, scvuσρ = evalsce u sceσρ in 
  uσρ ,, eval[] evalsσ evalu ,, scvuσρ
evalsce (π₂ σ) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalssce σ sceρ in
  π₂list σρ ,, evalπ₂ evalsσ ,, π₂SCE sceσρ
evalsce {Γ = Γ} {Δ = Δ} {A = A ⟶ B} (lam u) {ρ = ρ} sceρ =
  vlam u ρ ,, evallam u ρ ,,
  λ {Δ = Θ} {v = v} scvv →
  let uρv ,, evalu ,, scvuρv = evalsce u (sceρ ++SCE Θ ,, scvv) in
  let evallamu = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Θ}) ($lam evalu) in
  uρv ,, evallamu ,, scvuρv
evalsce (app u) sceρ =
  let f ,, evalf ,, scvf = evalsce u (π₁SCE sceρ) in
  let fρ ,, $fρ ,, scvfρ = scvf (π₂SCE sceρ) in
  fρ ,, evalapp evalf $fρ ,, scvfρ

evalssce id {ρ = ρ} sceρ =
  ρ ,, evalsid ,, sceρ
evalssce (σ ∘ ν) sceρ =
  let νρ ,, evalsν ,, sceνρ = evalssce ν sceρ in
  let σνρ ,, evalsσ ,, sceσνρ = evalssce σ sceνρ in
  σνρ ,, evals∘ evalsν evalsσ ,, sceσνρ
evalssce ε _ =
  ε ,, evalsε ,, tt
evalssce (σ , u) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalssce σ sceρ in
  let uρ ,, evalu ,, scvuρ = evalsce u sceρ in
  σρ , uρ ,, evals, evalsσ evalu ,, (sceσρ ,, scvuρ)
evalssce (π₁ σ) sceρ =
  let σρ ,, evalsσ ,, sceσρ = evalssce σ sceρ in
  π₁list σρ ,, evalsπ₁ evalsσ ,, π₁SCE sceσρ


-- Using that values evaluates to themselves, and determinism,
-- every value is strongly computable.
val-scv : {Γ : Con} {A : Ty} (v : Val Γ A) → SCV v
val-scv {Γ = Γ} v =
  let _ ,, evalv ,, scvv = evalsce ⌜ v ⌝V (sceid {Γ}) in
  tr SCV (eval-deterministic evalv (stable-val v)) scvv

env-sce : {Γ Δ : Con} (ρ : Env Γ Δ) → SCE ρ
env-sce {Γ = Γ} ρ =
  let _ ,, evalsρ ,, sceρ = evalssce ⌜ ρ ⌝E (sceid {Γ}) in
  tr SCE (evals-deterministic evalsρ (stable-env ρ)) sceρ


-- This allows to define eval, quote and nf as functions.
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

nf-is-norm : {Γ : Con} {A : Ty} (u : Tm Γ A) → norm u ⇒ (nf u)
nf-is-norm u = qeval eval-is-eval q-is-q



-- It is now possible to prove the recurrence relation for eval/...
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
