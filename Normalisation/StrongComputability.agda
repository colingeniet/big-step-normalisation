{-# OPTIONS --safe --cubical #-}

{-
  Definition of the notion of strong computability, which is central in the
  proof of termination.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

module Normalisation.StrongComputability where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.Weakening
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



-- Definition of strongly computable values.
scv : {Γ : Con} {A : Ty} → Val Γ A → Set
-- At the base type, a value is strongly computable if quote is defined on it.
scv {Γ = Γ} {A = o} u = Σ (Nf Γ o) λ n → q u ⇒ n
-- For function types, a function is strongly computable if for any sc argument,
-- the application of that function to that argument gives a scv.
-- Furthermore, the argument may come from an extended environment, in which
-- case the function is to be weakened.
scv {Γ = Γ} {A = A ⟶ B} f =
  {Δ : Con} (σ : Wk Δ Γ) {v : Val Δ A} → scv v →
  Σ[ fv ∈ Val Δ B ] ((f +V σ) $ v ⇒ fv  ×  scv fv)


isSetscv : {Γ : Con} {A : Ty} {v : Val Γ A} → isSet (scv v)
isSetscv {A = o} {v} =
  isSetΣ isSetNf (PropisSet isPropq)
isSetscv {Γ} {A ⟶ B} {f} {x} {y} p q i j {Δ} σ {v} scvv =
  isset (λ k _ σ _ scvv → p k σ scvv)
        (λ k _ σ _ scvv → q k σ scvv)
        i j Δ σ v scvv
  where
    -- Make all arguments explicit.
    isset : isSet ((Δ : Con) (σ : Wk Δ Γ) (v : Val Δ A) → scv v →
                   Σ[ fv ∈ Val Δ B ] ((f +V σ) $ v ⇒ fv  ×  scv fv))
    isset = isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} → isSet⇒ λ {_} →
            isSetΣ isSetVal (isSet× (PropisSet isProp$) isSetscv)


-- Strong computablility is stable by weakening.
_+scv_ : {Γ Δ : Con} {A : Ty} {v : Val Δ A} →
         scv v → (σ : Wk Γ Δ) → scv (v +V σ)
_+scv_ {A = o} (n ,, qv) σ = n +N σ ,, qv +q σ
_+scv_ {Γ} {Δ} {A ⟶ B} {f} scvf σ {Θ} ν {v} scvv =
  let fv ,, $fv ,, scvfv = scvf (σ ∘w ν) scvv
      $fv = tr (λ x → x $ v ⇒ fv) (+V∘ {v = f} {σ = σ} {ν = ν}) $fv
  in fv ,, $fv ,, scvfv

-- For function types, weakening of SCV 'does nothing', that is whenever an
-- argument is applied, the result will be the same with and without weakening.
+scv≡ : {Γ Δ Θ : Con} {A B : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ}
        {f : Val Θ (A ⟶ B)} {scvf : scv f}
        {v : Val Γ A} {scvv : scv v} →
        (_+scv_ {v = f} (λ {Δ} → scvf {Δ}) σ) ν scvv
        ≡[ ap (λ x → Σ[ fv ∈ Val Γ B ] ((x $ v ⇒ fv) × scv fv))
              (+V∘ {v = f} {σ} {ν} ⁻¹) ]≡
        scvf {Γ} (σ ∘w ν) {v} scvv
+scv≡ {Γ} {Δ} {Θ} {A} {B} {σ} {ν} {f} {scvf} {v} {scvv} i =
  let fv ,, $fv ,, scvfv = scvf (σ ∘w ν) scvv
      $fv = trfill (λ x → x $ v ⇒ fv) (+V∘ {v = f} {σ = σ} {ν = ν}) $fv
  in fv ,, $fv (1- i) ,, scvfv


+scvid : {Γ : Con} {A : Ty} {v : Val Γ A} {scvv : scv v} →
         scvv +scv idw ≡[ ap scv +Vid ]≡ scvv
+scvid {A = o} {v} {n ,, qv} i =
  +Nid {n = n} i ,,
  isPropPath {B = λ i → q (+Vid {v = v} i) ⇒ (+Nid {n = n} i)}
             isPropq (qv +q idw) qv i
+scvid {A = A ⟶ B} {f} {scvf} i {Δ} σ {v} scvv =
  let fv ,, $fv ,, scvfv = scvf σ scvv
      fv' ,, $fv' ,, scvfv' = scvf (idw ∘w σ) scvv
      $fv'' = tr (λ x → x $ v ⇒ fv') (+V∘ {v = f} {σ = idw} {ν = σ}) $fv'
      fv'≡fv : fv' ≡ fv
      fv'≡fv = apd (λ σ → fst (scvf σ scvv)) id∘w
      scvfv'≡scvfv : scvfv' ≡[ ap scv fv'≡fv ]≡ scvfv
      scvfv'≡scvfv = apd (λ σ → snd (snd (scvf σ scvv))) id∘w
      $fv''≡$fv : $fv'' ≡[ (λ i → ((+Vid {v = f} i) +V σ) $ v ⇒ (fv'≡fv i)) ]≡ $fv
      $fv''≡$fv = isPropPath {B = λ i → ((+Vid {v = f} i) +V σ) $ v ⇒ (fv'≡fv i)}
                             isProp$ $fv'' $fv
  in fv'≡fv i ,, $fv''≡$fv i ,, scvfv'≡scvfv i

{-
+scv∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ}
        {v : Val Γ A} {scvv : scv v} →
        scvv +scv (σ ∘w ν) ≡[ ap scv +V∘ ]≡ (scvv +scv σ) +scv ν
-}

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

πηsce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} (sceρ : sce ρ) →
        (π₁sce sceρ ,, π₂sce sceρ) ≡[ ap sce πηlist ]≡ sceρ
πηsce {ρ = ρ , u} (sceρ ,, scvu) = refl


isSetsce : {Γ Δ : Con} {ρ : Env Γ Δ} → isSet (sce ρ)
isSetsce {Δ = ●} {ε} = PropisSet isProp⊤
isSetsce {Δ = Δ , A} {ρ , u} = isSet× isSetsce isSetscv


-- Weakenings.
_+sce_ : {Γ Δ Θ : Con} {ρ : Env Δ Θ} → sce ρ → (σ : Wk Γ Δ) → sce (ρ +E σ)
_+sce_ {ρ = ε} tt σ = tt
_+sce_ {ρ = ρ , u} (sceρ ,, scvu) σ = sceρ +sce σ ,, scvu +scv σ

+sceid : {Γ Δ : Con} {ρ : Env Γ Δ} {sceρ : sce ρ} →
         sceρ +sce idw ≡[ ap sce +Eid ]≡ sceρ
+sceid {ρ = ε} = refl
+sceid {ρ = ρ , v} {sceρ ,, scvv} i = +sceid {ρ = ρ} {sceρ} i ,, +scvid {v = v} {scvv} i


π₁sce+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₁sce (sceρ +sce σ) ≡[ ap sce (π₁+ {ρ = ρ}) ]≡ (π₁sce sceρ) +sce σ
π₁sce+ {ρ = _ , _} = refl
π₂sce+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₂sce (sceρ +sce σ) ≡[ ap scv (π₂+ {ρ = ρ}) ]≡ (π₂sce sceρ) +scv σ
π₂sce+ {ρ = _ , _} = refl



{-
  Main lemma:
  The fact that strong computability implies termination of quote is actually
  not obvious. The proof requires to simultaneously prove the converse for
  neutral values.
-}
-- Main direction: strong computability implies termination of quote.
scv-q : {Γ : Con} {A : Ty} {v : Val Γ A} →
        scv v → Σ (Nf Γ A) (λ n → q v ⇒ n)
-- Converse for neutral values.
q-scv : {Γ : Con} {A : Ty} {v : Ne Val Γ A} {n : Ne Nf Γ A} →
        qs v ⇒ n → scv (neu v)

-- The converse allows in particular to show that variables are sc.
scvvar : {Γ : Con} {A : Ty} {x : Var Γ A} → scv (neu (var x))
scvvar = q-scv qsvar


scv-q {A = o} scvv = scvv
-- For functions, we follow the definition of quote and apply
-- the function to vz. This is why sc of variables is required.
scv-q {A = A ⟶ B} scvf =
  let fz ,, $fz ,, scvfz = scvf (drop A idw) (scvvar {x = z}) in
  let nfz ,, qfz = scv-q scvfz in
  lam nfz ,, q⟶ $fz qfz


q-scv {A = o} {n = n} qv = neu n ,, qo qv
-- For functions, since we are considering neutral values, application
-- to a value is trivial. Quote simply quotes the function and the value
-- separately, hence the proof would be simple if it was not for a few
-- weakenings and transports.
q-scv {A = A ⟶ B} {f} {n} qf {Δ} σ {v} scvv =
  neu (app (f +NV σ) v) ,,
  $app (f +NV σ) v ,,
  q-scv (qsapp (qf +qs σ) (snd (scv-q scvv)))



-- The identity environment is strongly computable.
sceid : {Γ : Con} → sce (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +sce (drop A idw) ,, scvvar
