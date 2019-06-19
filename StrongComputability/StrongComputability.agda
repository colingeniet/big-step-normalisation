{-# OPTIONS --cubical #-}

{-
  Definition of the notion of strong computability, which is central in the
  proof of termination.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

module StrongComputability.StrongComputability where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import Evaluator.Evaluator
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Evaluator


{- The definition of strong computability depends on the type,
   which is why it uses evaluated types.

   Alternative: define it as an inductive family ?
   The skeleton would be required anyway to prove that the definition is sound.
-}

scvTV : {S : TSk} {Γ : Con} (A : TV S Γ) → Val Γ ⌜ A ⌝T → Set
-- Strong computability is termination for the base types.
scvTV {Γ = Γ} U v = Σ[ n ∈ Nf Γ U ] q v ⇒ n
scvTV {Γ = Γ} (El u) v = Σ[ n ∈ Nf Γ (El u) ] q v ⇒ n
-- For function types, it is defined through the application of a SC argument.
scvTV {Π S T} {Γ} (Π A B) f =
  {Δ : Con} (σ : Wk Δ Γ) {v : Val Δ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T} → scvTV (A [ ⌜ σ ⌝w ]TV) v →
  Σ[ C ∈ TV T Δ ] Σ[ fv ∈ Val Δ ⌜ C ⌝T ]
  ((tr (Val Δ) Π[] (f +V σ)) $ (tr (Val Δ) (⌜[]TV⌝ ⁻¹) v) ⇒ fv  ×  scvTV C fv)

-- Strong computability for regular types: simply evaluate the type first.
scv : {Γ : Con} {A : Ty Γ} → Val Γ A → Set
scv {A = A} v = scvTV (evalT A) (tr (Val _) ⌜evalT⌝ v)

-- Extension of strong computability to environments.
sce : {Γ Δ : Con} → Env Γ Δ → Set
sce ε = ⊤
sce (ρ , v) = sce ρ  ×  scv v

-- Associated projections.
π₁sce : {Γ Δ : Con} {A : Ty Δ} {ρ : Env Γ (Δ , A)} →
        sce ρ → sce (π₁E ρ)
π₁sce {ρ = _ , _} = fst

π₂sce : {Γ Δ : Con} {A : Ty Δ} {ρ : Env Γ (Δ , A)} →
        sce ρ → scv (π₂E ρ)
π₂sce {ρ = _ , _} = snd

πηsce : {Γ Δ : Con} {A : Ty Δ} {σ : Env Γ (Δ , A)} (sceσ : sce σ) →
        (π₁sce sceσ ,, π₂sce sceσ) ≡[ ap sce πηE ]≡ sceσ
πηsce {σ = σ , u} (sceσ ,, scvu) = refl

sceεη : {Γ : Con} {σ : Env Γ ●} (sceσ : sce σ) →
        sceσ ≡[ ap sce (envεη σ) ]≡ tt
sceεη {σ = ε} tt = refl
