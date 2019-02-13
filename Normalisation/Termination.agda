{-# OPTIONS --cubical #-}

module Normalisation.Termination where

open import Equality
open import Syntax
open import Syntax.Equality
open import Normalisation.NormalForms
open import Normalisation.Evaluator

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

-- Strongly computable values.
SCV : {Γ : Con} {A : Ty} {u : Tm Γ A} → Val u → Set
-- At the base type, a value is strongly computable if it can be normalized by q.
SCV {A = o} {u = u} valu =
  Σ (Nf u) λ nfu →
    q valu ⇒ nfu
-- For function types, a value is strongly computable if for any SC argument value
-- in an extended context, the application of that function to that argument
-- gives a SCV.
SCV {Γ = Γ} {A = A ⟶ B} {u = f} valf =
  {Δ : Con} {u : Tm (Γ ++ Δ) A} {valu : Val u} → SCV valu →
  Σ (Val ((f ++t Δ) $ u)) λ valfu →
  Σ ((valf ++V Δ) $ valu ⇒ valfu) λ _ →
    SCV valfu


-- Lemma : SCV is stable by context extension.
postulate
  _+SCV_ : {Γ : Con} {B : Ty} {u : Tm Γ B} {valu : Val u} → SCV valu → (A : Ty) →
           SCV (valu +V A)
{-
_+SCV_ {B = o} (nfu  Σ., qu) A = (nfu +N A) Σ., (qwk qu A)
_+SCV_ {B = B ⟶ C} {u = f} {valu = valf} scf A {Δ = Δ} {u = u} {valu = valu} scu =
-}

_++SCV_ : {Γ : Con} {B : Ty} {u : Tm Γ B} {valu : Val u} → SCV valu → (Δ : Con) →
          SCV (valu ++V Δ)
u ++SCV ● = u
u ++SCV (Δ , A) = (u ++SCV Δ) +SCV A

-- Main lemma : SCV is ~ equivalent to the termination of q.
-- Main direction (actual goal).
scv-q : {Γ : Con} {A : Ty} {u : Tm Γ A} {valu : Val u} →
        SCV valu → Σ (Nf u) (λ nfu → q valu ⇒ nfu)
-- The reciprocal on neutral terms is required for the induction
q-scv : {Γ : Con} {A : Ty} {u : Tm Γ A} {neuu : Ne Val u} {nefu : Ne Nf u} →
        qs neuu ⇒ nefu → SCV (vneu neuu)

-- The second part of the lemma allows to prove that variables are strongly computable.
scvvar : {Γ : Con} {A : Ty} {u : Tm Γ A} {varu : Var u} → SCV (vneu (var varu))
scvvar = q-scv qsvar


scv-q {A = o} scvu = scvu
scv-q {A = A ⟶ B} scvu =
  let res = scvu {Δ = ● , A} scvvar in
  let valuz = fst res in
  let cuz = fst (snd res) in
  let scvuz = snd (snd res) in
  let res2 = scv-q scvuz in
  let nfappu = fst res2 in
  let cappu = snd res2 in
  tr Nf classicη (nlam nfappu) ,, qs⟶ cuz cappu

q-scv {A = o} {neuu = neuu} {nefu = nefu} cu = (nneu nefu) ,, qso cu
q-scv {A = A ⟶ B} {u = f} {neuu = neuf} {nefu = neff} qf {Δ = Δ} {u = u} {valu = valu} scvu =
  let neufu = app (neuf ++NV Δ) valu in
  let cfu = tr (λ x → (x $ valu ⇒ vneu neufu))
               (vneu++V {neuu = neuf} ⁻¹)
               ($app (neuf ++NV Δ) valu) in
  let nfu = fst (scv-q scvu) in
  let qu = snd (scv-q scvu) in
  vneu neufu
  ,, cfu
  ,, q-scv (qsapp (qswks qf Δ) qu)
  where vneu++V : ∀ {Γ Δ : Con} {A : Ty} {u : Tm Γ A} {neuu : Ne Val u} →
                    (vneu neuu) ++V Δ ≡ vneu (neuu ++NV Δ)
        vneu++V {Δ = ●} = refl
        vneu++V {Δ = Δ , B} = ap (λ x → x +V B) (vneu++V {Δ = Δ})

-- Extension of strong computability to environments.
SCE : {Γ Δ : Con} {ρ : Tms Γ Δ} → Env ρ → Set
SCE ε = ⊤
SCE (ρ , u) = Σ (SCE ρ) λ _ → SCV u

π₁SCE : {Γ Δ : Con} {A : Ty} {ρ : Tms Γ (Δ , A)} {envρ : Env ρ} (sceρ : SCE envρ) →
        SCE (π₁list envρ)
π₁SCE {envρ = ρ , u} (sceρ ,, valu) = trd SCE (trfill Env (π₁β ⁻¹) ρ) sceρ

π₂SCE : {Γ Δ : Con} {A : Ty} {ρ : Tms Γ (Δ , A)} {envρ : Env ρ} (sceρ : SCE envρ) →
        SCV (π₂list envρ)
π₂SCE {envρ = ρ , u} (sceρ ,, valu) = trd SCV (trfill Val (π₂β ⁻¹) u) valu


_+SCE_ : {Γ Δ : Con} {ρ : Tms Γ Δ} {envρ : Env ρ}
         (sceρ : SCE envρ) (A : Ty) → SCE (envρ +E A)
_+SCE_ {envρ = ε} .tt A = trd SCE (trfill Env (εη ⁻¹) ε) tt
_+SCE_ {envρ = envρ , valu} (sceρ ,, scvu) A =
  trd SCE
      (trfill Env (,∘ ⁻¹) ((envρ +E A) , (valu +V A)))
      ((sceρ +SCE A) ,, (scvu +SCV A))

_++SCE_ : {Γ Θ : Con} {σ : Tms Γ Θ} {envσ : Env σ} → SCE envσ → (Δ : Con) →
          SCE (envσ ++E Δ)
σ ++SCE ● = σ
σ ++SCE (Δ , A) = (σ ++SCE Δ) +SCE A


sceid : {Γ : Con} → SCE (idenv {Γ})
sceid {●} = trd SCE (trfill Env (εη ⁻¹) ε) tt
sceid {Γ , A} = 
  trd SCE
      (trfill Env πη (tr Env id∘ (idenv +E A) , vneu (var z)))
      (trd SCE (trfill Env id∘ (idenv +E A)) ((sceid {Γ}) +SCE A)
      ,, scvvar)



-- Main theorem : Evaluation in a strongly computable environment gives a
-- strongly computable result.
evalsce : {Γ Δ : Con} {A : Ty} {ρ : Tms Γ Δ} {envρ : Env ρ} (sceρ : SCE envρ) (u : Tm Δ A) →
          Σ (Val (u [ ρ ])) λ valu →
          Σ (eval u > envρ ⇒ valu) λ _ →
            SCV valu
evalssce : {Γ Δ Θ : Con} {ρ : Tms Γ Δ} {envρ : Env ρ} (sceρ : SCE envρ) (σ : Tms Δ Θ) →
           Σ (Env (σ ∘ ρ)) λ envσ →
           Σ (evals σ > envρ ⇒ envσ) λ _ →
             SCE envσ

evalsce sceρ (u [ σ ]) =
  let evalssceσ = evalssce sceρ σ in
  let envσ = fst evalssceσ in
  let evalsσ = fst (snd evalssceσ) in
  let sceσ = snd (snd evalssceσ) in
  let evalsceu = evalsce sceσ u in
  let valu = fst evalsceu in
  let evalu = fst (snd evalsceu) in
  let scvu = snd (snd evalsceu) in
  let valuσ = tr Val [][] valu in
  valuσ ,, eval[] evalsσ evalu ,, trd SCV (trfill Val [][] valu) scvu
evalsce sceρ (π₂ σ) =
  let evalssceσ = evalssce sceρ σ in
  let envσ = fst evalssceσ in
  let evalsσ = fst (snd evalssceσ) in
  let sceσ = snd (snd evalssceσ) in
  let valπ₂σ = tr Val π₂∘ (π₂list envσ) in
  valπ₂σ ,, evalπ₂ evalsσ ,, trd SCV (trfill Val π₂∘ (π₂list envσ)) (π₂SCE sceσ)
evalsce {A = A ⟶ B} {ρ = ρ} {envρ = envρ} sceρ (lam u) =
  let vallamu = vlam u envρ in
  vallamu ,, evallam ,,
  λ {Δ = Δ} {u = v} {valu = valv} scvv →
  let sceρv = (sceρ ++SCE Δ) ,, scvv in
  let evalsceu = evalsce sceρv u in
  let valu = fst evalsceu in
  let evalu = fst (snd evalsceu) in
  let scvu = snd (snd evalsceu) in
  let u≡ = clos[] ⁻¹ ∙ ap (λ x → x $ v) []++ in
  tr Val u≡ valu
  ,, {!$lam evalu!} ,, {!!}
evalsce sceρ (app f) = {!!}
evalsce sceρ (π₂β i) = {!!}
evalssce = {!!}
