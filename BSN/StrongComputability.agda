{-# OPTIONS --safe --cubical #-}

{-
  Definition of the notion of strong computability, which is central in the
  proof of termination.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

module BSN.StrongComputability where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.Types.Sets
open import Weakening.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import Value.Sets
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import NormalForm.Sets
open import Evaluator.Evaluator
open import Evaluator.Weakening
open import BSN.Completeness
open import BSN.Stability
open import BSN.Soundness



-- Definition of strongly computable values.
scv : {Γ : Con} {A : Ty} → Val Γ A → Set
-- At the base type, a value is strongly computable if quote is defined on it.
scv {Γ} {o} v = Σ[ n ∈ Nf Γ o ] q v ⇒ n
-- For function types, a function is strongly computable if for any sc argument,
-- the application of that function to that argument gives a scv.
-- Furthermore, the argument may come from an extended environment, in which
-- case the function is to be weakened.
scv {Γ} {A ⟶ B} f =
  {Δ : Con} (σ : Wk Δ Γ) {v : Val Δ A} → scv v →
  Σ[ fv ∈ Val Δ B ] ((f +V σ) $ v ⇒ fv  ×  scv fv)


isPropscv : {Γ : Con} {A : Ty} {v : Val Γ A} → isProp (scv v)
isPropscv {A = o} {v} (n ,, qn) (m ,, qm) i =
  let n≡m : n ≡ m
      n≡m = q-sound qn qm
  in n≡m i ,, isPropDependent isPropq n≡m qn qm i
isPropscv {Γ} {A ⟶ B} {f} x y i σ {v} scvv =
  let fv ,, $fv ,, scvfv = x σ scvv
      fv' ,, $fv' ,, scvfv' = y σ scvv
      fv≡fv' : fv ≡ fv'
      fv≡fv' = $-sound $fv $fv'
  in fv≡fv' i ,,
     isPropDependent {B = λ x → (f +V σ) $ v ⇒ x} isProp$
                     fv≡fv' $fv $fv' i ,,
     isPropDependent {B = scv} (isPropscv {A = B})
                     fv≡fv' scvfv scvfv' i

_+scv_ : {Γ Δ : Con} {A : Ty} {v : Val Δ A} → scv v → (σ : Wk Γ Δ) → scv (v +V σ)
_+scv_ {A = o} (n ,, qn) σ = n +N σ ,, qn +q σ
_+scv_ {A = A ⟶ B} {f} scvf σ δ {v} scvv =
  let fv ,, $fv ,, scvfv = scvf (σ ∘w δ) scvv
      $fv = tr (λ x → x $ _ ⇒ _) (+V∘ {v = f}) $fv
  in fv ,, $fv ,, scvfv


-- Extension of strong computability to environments.
sce : {Γ Δ : Con} → Env Γ Δ → Set
sce ε = ⊤
sce (ρ , u) = sce ρ  ×  scv u

-- Associated projections.
π₁sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → sce (π₁E ρ)
π₁sce {ρ = _ , _} = fst

π₂sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → scv (π₂E ρ)
π₂sce {ρ = _ , _} = snd

πηsce : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} (sceσ : sce σ) →
        (π₁sce sceσ ,, π₂sce sceσ) ≡[ ap sce πηE ]≡ sceσ
πηsce {σ = σ , u} (sceσ ,, scvu) = refl

sceεη : {Γ : Con} {σ : Env Γ ●} (sceσ : sce σ) →
        sceσ ≡[ ap sce (envεη σ) ]≡ tt
sceεη {σ = ε} tt = refl



isPropsce : {Γ Δ : Con} {σ : Env Γ Δ} → isProp (sce σ)
isPropsce {Δ = ●} {ε} = isProp⊤
isPropsce {Δ = Δ , A} {ρ , u} = isProp× isPropsce isPropscv

-- Weakenings.
_+sce_ : {Γ Δ Θ : Con} {ρ : Env Δ Θ} → sce ρ → (σ : Wk Γ Δ) → sce (ρ +E σ)
_+sce_ {ρ = ε} tt A = tt
_+sce_ {ρ = ρ , u} (sceρ ,, scvu) σ = sceρ +sce σ ,, scvu +scv σ


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
        scv v → Σ[ n ∈ Nf Γ A ] (q v ⇒ n)
-- Converse for neutral values.
q-scv : {Γ : Con} {A : Ty} {v : NV Γ A} →
        Σ[ n ∈ NN Γ A ] (qs v ⇒ n) → scv (neu v)

-- The converse allows in particular to show that variables are sc.
scvvar : {Γ : Con} {A : Ty} {x : Var Γ A} → scv (neu (var x))
scvvar {x = x} = q-scv (var x ,, qsvar)

scv-q {A = o} scvv = scvv
-- For functions, we follow the definition of quote and apply
-- the function to vz. This is why sc of variables is required.
scv-q {A = A ⟶ B} {f} scvf =
  let fz ,, $fz ,, scvfz = scvf (wkwk A idw) {neu (var z)} scvvar
      nfz ,, qfz = scv-q scvfz
  in lam nfz ,, q⟶ $fz qfz

q-scv {A = o} (n ,, qn) = neu n ,, qo qn
-- For functions, since we are considering neutral values, application
-- to a value is trivial. Quote simply quotes the function and the value
-- separately.
q-scv {A = A ⟶ B} {f} (nf ,, qsf) σ {v} scvv =
  let fv = app (f +NV σ) v
      $fv = $app (f +NV σ) v
      n ,, qv = scv-q scvv
      nfv = app (nf +NN σ) n
      qfv = qsapp (qsf +qs σ) qv
  in neu fv ,, $fv ,, q-scv (nfv ,, qfv)

-- The identity environment is strongly computable.
sceid : {Γ : Con} → sce (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +sce (wkwk A idw) ,, scvvar
