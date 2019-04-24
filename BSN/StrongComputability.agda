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
open import Syntax.Types.Sets
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


-- Termination and soundness of quote.
-- This could be defined without an inductive type, but somehow agda is
-- better at infering implicit arguments this way.
data Norm {Γ : Con} {A : Ty} (u : Val Γ A) : Set where
  norm : {n : Nf Γ A} → q u ⇒ n →
         ({Δ : Con} {m : Nf (Γ ++ Δ) A} →
                    q (u ++V Δ) ⇒ m → m ≡ (n ++N Δ)) →
         Norm u

isPropNorm : {Γ : Con} {A : Ty} {u : Val Γ A} → isProp (Norm u)
isPropNorm {Γ} {A} {u} (norm {n = n} qn x) (norm {n = m} qm y) i =
  let n≡m = y {Δ = ●} qn
      qn≡qm = isPropDependent {B = λ n → q u ⇒ n} isPropq
                              n≡m qn qm
  in norm (qn≡qm i) λ {Δ} q j →
    ouc (isSetFillSquare isSetNf (x q) (y q) refl (λ i → (n≡m i) ++N Δ) i j)

_+norm_ : {Γ : Con} {B : Ty} {u : Val Γ B} → Norm u → (A : Ty) → Norm (u +V A)
_+norm_ {Γ} {B} {u} (norm {n = n} qn p) A =
  norm (qwk qn A) λ {Δ} {m} qm →
  let u≡u' = V+-++ {Δ = Δ} {B = A} {u = u}
      n≡n' = N+-++ {Δ = Δ} {B = A} {n = n}
      m' = tr (λ Γ → Nf Γ B) (,++ {Δ = Δ}) m
      m≡m' = trfill (λ Γ → Nf Γ B) (,++ {Δ = Δ}) m
      qm' = (λ i → q (u≡u' i) ⇒ (m≡m' i)) * qm
      m≅n : m ≅⟨(λ Γ → Nf Γ B)⟩ (n +N A) ++N Δ
      m≅n = ≡[]-to-≅ m≡m'
            ∙≅ ≡-to-≅ (p qm')
            ∙≅ ≡[]-to-≅ n≡n' ≅⁻¹
  in ≅-to-≡ isSetCon m≅n


-- Definition of strongly computable values.
scv : {Γ : Con} {A : Ty} → Val Γ A → Set
-- At the base type, a value is strongly computable if quote is defined on it.
scv {A = o} = Norm
-- For function types, a function is strongly computable if for any sc argument,
-- the application of that function to that argument gives a scv.
-- Furthermore, the argument may come from an extended environment, in which
-- case the function is to be weakened.
scv {Γ} {A ⟶ B} f =
  {Δ : Con} {u : Val (Γ ++ Δ) A} → scv u →
  Σ[ fu ∈ Val (Γ ++ Δ) B ] ((f ++V Δ) $ u ⇒ fu  ×  scv fu)


isPropscv : {Γ : Con} {A : Ty} {u : Val Γ A} → isProp (scv u)
isPropscv {A = o} = isPropNorm
isPropscv {Γ} {A ⟶ B} {f} x y i {Δ} {u} scvu =
  let v ,, $fu ,, scvv = x scvu
      v' ,, $fu' ,, scvv' = y scvu
      v≡v' : v ≡ v'
      v≡v' = veq (eval$≡ $fu ⁻¹ ∙ eval$≡ $fu')
  in v≡v' i ,,
     isPropPath {B = λ i → (f ++V Δ) $ u ⇒ (v≡v' i)} isProp$
                $fu $fu' i ,,
     isPropDependent {B = scv} (isPropscv {A = B}) v≡v' scvv scvv' i


-- Strong computablility is stable by weakening.
_+scv_ : {Γ : Con} {B : Ty} {u : Val Γ B} → scv u → (A : Ty) → scv (u +V A)
_+scv_ {B = o} = _+norm_
_+scv_ {B = B ⟶ C} {u = f} scvf A {Δ} {u} scvu =
  let u' = tr (λ Γ → Val Γ B) ,++ u in
  let u≡u' = trfill (λ Γ → Val Γ B) ,++ u in
  let scvu' = trd scv u≡u' scvu in
  let fu' ,, $fu' ,, scvfu' = scvf scvu' in
  let fu = tr (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let fu'≡fu = trfill (λ Γ → Val Γ C) (,++ {Δ = Δ} ⁻¹) fu' in
  let scvfu = trd scv fu'≡fu scvfu' in
  fu ,,
  (λ i → (V+-++ {Δ = Δ} {B = A} {u = f} (1- i)) $ (u≡u' (1- i)) ⇒
    (fu'≡fu i))
  * $fu' ,,
  scvfu

_++scv_ : {Γ : Con} {B : Ty} {u : Val Γ B} → scv u → (Δ : Con) → scv (u ++V Δ)
u ++scv ● = u
u ++scv (Δ , A) = (u ++scv Δ) +scv A



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


isPropsce : {Γ Δ : Con} {σ : Env Γ Δ} → isProp (sce σ)
isPropsce {Δ = ●} {ε} = isProp⊤
isPropsce {Δ = Δ , A} {ρ , u} = isProp× isPropsce isPropscv


-- Weakenings.
_+sce_ : {Γ Δ : Con} {ρ : Env Γ Δ} → sce ρ → (A : Ty) → sce (ρ +E A)
_+sce_ {ρ = ε} tt A = tt
_+sce_ {ρ = ρ , u} (sceρ ,, scvu) A = sceρ +sce A ,, scvu +scv A

_++sce_ : {Γ Θ : Con} {σ : Env Γ Θ} → sce σ → (Δ : Con) → sce (σ ++E Δ)
σ ++sce ● = σ
σ ++sce (Δ , A) = (σ ++sce Δ) +sce A


π₁sce+ : {Γ Δ : Con} {A B : Ty} {σ : Env Γ (Δ , A)} {sceσ : sce σ} →
         π₁sce (sceσ +sce B) ≡[ ap sce (π₁+ {Δ = ●} {σ = σ}) ]≡ (π₁sce sceσ) +sce B
π₁sce+ {σ = _ , _} = refl
π₂sce+ : {Γ Δ : Con} {A B : Ty} {σ : Env Γ (Δ , A)} {sceσ : sce σ} →
         π₂sce (sceσ +sce B) ≡[ ap scv (π₂+ {Δ = ●} {σ = σ}) ]≡ (π₂sce sceσ) +scv B
π₂sce+ {σ = _ , _} = refl

π₁sce++ : {Γ Δ Θ : Con} {A : Ty} {σ : Env Γ (Δ , A)} {sceσ : sce σ} →
          π₁sce (sceσ ++sce Θ) ≡[ ap sce (π₁++ {σ = σ}) ]≡ (π₁sce sceσ) ++sce Θ
π₁sce++ {Θ = ●} = refl
π₁sce++ {Θ = Θ , B} {sceσ = σ} =
  ≅-to-≡[] {B = sce} isSetEnv
           (≡[]-to-≅ {B = sce} (π₁sce+ {sceσ = σ ++sce Θ})
           ∙≅ ≡[]-to-≅ (apd (λ σ → σ +sce B) (π₁sce++ {Θ = Θ} {sceσ = σ})))
π₂sce++ : {Γ Δ Θ : Con} {A : Ty} {σ : Env Γ (Δ , A)} {sceσ : sce σ} →
          π₂sce (sceσ ++sce Θ) ≡[ ap scv (π₂++ {σ = σ}) ]≡ (π₂sce sceσ) ++scv Θ
π₂sce++ {Θ = ●} = refl
π₂sce++ {Θ = Θ , B} {sceσ = σ} =
  ≅-to-≡[] {B = scv} isSetVal
           (≡[]-to-≅ {B = scv} (π₂sce+ {sceσ = σ ++sce Θ})
           ∙≅ ≡[]-to-≅ (apd (λ u → u +scv B) (π₂sce++ {Θ = Θ} {sceσ = σ})))


{-
{-
  Main lemma:
  The fact that strong computability implies termination of quote is actually
  not obvious. The proof requires to simultaneously prove the converse for
  neutral values.
-}
-- Main direction: strong computability implies termination of quote.
scv-q : {Γ : Con} {A : Ty} {u : Val Γ A} →
        scv u → Norm u
-- Converse for neutral values.
q-scv : {Γ : Con} {A : Ty} {u : Ne Val Γ A} →
        Norms u → scv (neu u)

-- The converse allows in particular to show that variables are sc.
scvvar : {Γ : Con} {A : Ty} {x : Var Γ A} → scv (neu (var x))
scvvar = q-scv (norms qsvar)


scv-q {A = o} scvu = scvu
-- For functions, we follow the definition of quote and apply
-- the function to vz. This is why sc of variables is required.
scv-q {Γ} {A ⟶ B} {u = u} scvu =
  match (scv-q (snd (snd (scvu scvvar))))
  where uz : Val (Γ , A) B
        uz = fst (scvu scvvar)
        $uz : (u +V A) $ (neu (var z)) ⇒ uz
        $uz = fst (snd (scvu scvvar))
        match : Norm uz → Norm u
        match (norm quz) = norm (q⟶ $uz quz)
        match (isPropNorm x y i) = isPropNorm (match x) (match y) i


q-scv {A = o} q = Norms-o→Norm q
-- For functions, since we are considering neutral values, application
-- to a value is trivial. Quote simply quotes the function and the value
-- separately, hence the proof would be simple if it was not for a few
-- weakenings and transports.
q-scv {A = A ⟶ B} {u = f} (norms qf) {Δ = Δ} {u = u} scu =
  let fu = app (f ++NV Δ) u
      $fu = tr (λ x → (x $ u ⇒ neu fu))
               (++VNV {v = f} ⁻¹)
               ($app (f ++NV Δ) u)
      normu = scv-q scu
  in neu fu ,, $fu ,, q-scv (match normu)
  where match : Norm u → Norms (app (f ++NV Δ) u)
        match (norm qu) = norms (qsapp (qswks qf Δ) qu)
        match (isPropNorm x y i) = isPropNorms (match x) (match y) i
q-scv {A = A ⟶ B} (isPropNorms x y i) =
  -- Without the η-expansion, agda tries to find some implicit arguments and
  -- thinks that SCV ≠ SCV because the implicit arguments are not there ...
  isPropscv (λ {Δ} → q-scv x {Δ}) (q-scv y) i



-- The identity environment is strongly computable.
sceid : {Γ : Con} → sce (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +sce A ,, scvvar
-}
