{-# OPTIONS --cubical #-}

module Normalisation.Termination where

open import Equality
open import Syntax
open import Syntax.Equality
open import Syntax.Eliminator
open import Normalisation.NormalForms
open import Normalisation.Evaluator

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
π₁SCE {ρ = ρ , _} (sceρ ,, _) = sceρ

π₂SCE : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        SCE ρ → SCV (π₂list ρ)
π₂SCE {ρ = _ , u} (_ ,, valu) = valu


_+SCE_ : {Γ Δ : Con} {ρ : Env Γ Δ} → SCE ρ → (A : Ty) → SCE (ρ +E A)
_+SCE_ {ρ = ε} tt A = tt
_+SCE_ {ρ = ρ , u} (sceρ ,, scvu) A = sceρ +SCE A ,, scvu +SCV A

_++SCE_ : {Γ Θ : Con} {σ : Env Γ Θ} → SCE σ → (Δ : Con) → SCE (σ ++E Δ)
σ ++SCE ● = σ
σ ++SCE (Δ , A) = (σ ++SCE Δ) +SCE A

sceid : {Γ : Con} → SCE (idenv {Γ})
sceid {●} = tt --trd SCE (trfill Env (εη ⁻¹) ε) tt
sceid {Γ , A} = sceid +SCE A ,, scvvar



-- Main theorem : Evaluation in a strongly computable environment gives a
-- strongly computable result.
evalsceMo : Motives
Motives.Tmᴹ evalsceMo {Γ = Δ} {A = A} u =
  {Γ : Con} {ρ : Env Γ Δ} (sceρ : SCE ρ) →
  Σ (Val Γ A) λ uρ →
  Σ (eval u > ρ ⇒ uρ) λ _ →
    SCV uρ
Motives.Tmsᴹ evalsceMo {Γ = Δ} {Δ = Θ} σ =
  {Γ : Con} {ρ : Env Γ Δ} (sceρ : SCE ρ) →
  Σ (Env Γ Θ) λ σρ →
  Σ (evals σ > ρ ⇒ σρ) λ _ →
    SCE σρ

open Motives evalsceMo

evalsceMe : Methods evalsceMo

Methods._[_]ᴹ evalsceMe IHu IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  let uσρ ,, evalu ,, scvuσρ = IHu sceσρ in 
  uσρ ,, eval[] evalsσ evalu ,, scvuσρ
Methods.π₂ᴹ evalsceMe IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  π₂list σρ ,, evalπ₂ evalsσ ,, π₂SCE sceσρ
Methods.lamᴹ evalsceMe {A = A} {u = u} IHu {Γ = Γ} {ρ = ρ} sceρ =
  vlam u ρ ,, evallam u ρ ,,
  λ {Δ : Con} {v : Val (Γ ++ Δ) A} scvv →
  let uρv ,, evalu ,, scvuρv = IHu (sceρ ++SCE Δ ,, scvv) in
  let evallamu = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Δ}) ($lam evalu) in
  uρv ,, evallamu ,, scvuρv
Methods.appᴹ evalsceMe IHf sceρ =
  let f ,, evalf ,, scvf = IHf (π₁SCE sceρ) in
  let fρ ,, $fρ ,, scvfρ = scvf (π₂SCE sceρ) in
  fρ ,, evalapp evalf $fρ ,, scvfρ

Methods.idᴹ evalsceMe {ρ = ρ} sceρ =
  ρ ,, evalsid ,, sceρ
Methods._∘ᴹ_ evalsceMe IHσ IHν sceρ =
  let νρ ,, evalsν ,, sceνρ = IHν sceρ in
  let σνρ ,, evalsσ ,, sceσνρ = IHσ sceνρ in
  σνρ ,, evals∘ evalsν evalsσ ,, sceσνρ
Methods.εᴹ evalsceMe sceρ =
  ε ,, evalsε ,, tt
Methods._,ᴹ_ evalsceMe IHσ IHu sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  let uρ ,, evalu ,, scvuρ = IHu sceρ in
  σρ , uρ ,, evals, evalsσ evalu ,, (sceσρ ,, scvuρ)
Methods.π₁ᴹ evalsceMe IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  π₁list σρ ,, evalsπ₁ evalsσ ,, π₁SCE sceσρ
