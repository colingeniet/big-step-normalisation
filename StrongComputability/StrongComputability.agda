{-# OPTIONS --cubical #-}

{-
  Definition of the notion of strong computability, which is central in the
  proof of termination.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

module StrongComputability.StrongComputability where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import Value.Sets
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator
open import Evaluator.Weakening
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Sets
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

abstract
  -- 'Constructor' for function types (the base constructors should not be needed).
  scvΠ : {Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Val Δ (Π A B)} →
         ({Γ : Con} (σ : Wk Γ Δ) {v : Val Γ (A [ ⌜ σ ⌝w ]T)} → scv v →
          Σ[ C ∈ Ty Γ ] Σ[ fv ∈ Val Γ C ] (tr (Val _) Π[] (f +V σ) $ v ⇒ fv  ×  scv fv)) →
         scv f
  scvΠ {Δ} {A} {B} {f} H {Γ} σ {v} scvv =
    let v' : Val Γ (A [ ⌜ σ ⌝w ]T)
        v' = tr (Val Γ) (⌜evalT⌝ ⁻¹) v
        v'' : Val Γ ⌜ evalT A [ ⌜ σ ⌝w ]TV ⌝T
        v'' = tr (Val Γ) ⌜evalT⌝ v'
        v≡v'' : v ≡ v''
        v≡v'' = ≅-to-≡ {B = Val Γ} isSetTy (
                  v   ≅⟨ trfill (Val Γ) (⌜evalT⌝ ⁻¹) v ⟩
                  v'  ≅⟨ trfill (Val Γ) ⌜evalT⌝ v' ⟩
                  v'' ≅∎)
        C ,, fv ,, $fv ,, scvfv = H σ {v = v'} (tr (scvTV _) v≡v'' scvv)
        C≡B' : C ≡ B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ v' ⌝V > ]T
        C≡B' = fst (eval$≡ $fv) ⁻¹
        skC≡skB : skeleton C ≡ skeleton B
        skC≡skB i = skeleton (C≡B' i)
        C' : TV (skeleton B) Γ
        C' = tr (λ x → TV x Γ) skC≡skB (evalT C)
        P : evalT C ≡[ ap (λ x → TV x Γ) skC≡skB ]≡ C'
        P = trfill (λ x → TV x Γ) skC≡skB (evalT C)
        C≡C' : C ≡ ⌜ C' ⌝T
        C≡C' = C           ≡⟨ ⌜evalT⌝ ⟩
               ⌜ evalT C ⌝T ≡⟨ apd ⌜_⌝T P ⟩
               ⌜ C' ⌝T      ∎
        fv' : Val Γ ⌜ C' ⌝T
        fv' = tr (Val Γ) C≡C' fv
        fv≡fv' : fv ≡[ ap (Val Γ) C≡C' ]≡ fv'
        fv≡fv' = trfill (Val Γ) C≡C' fv
        p : tr (Val _) ⌜evalT⌝ fv ≅[ Val _ ] fv'
        p = tr (Val _) ⌜evalT⌝ fv ≅⟨ trfill (Val Γ) ⌜evalT⌝ fv ⁻¹ ⟩
            fv                   ≅⟨ fv≡fv' ⟩
            fv'                  ≅∎
        scvfv' : scvTV C' fv'
        scvfv' = (λ i → scvTV (P i) (≅-to-≡[] isSetTy p {P = apd ⌜_⌝T P} i))
                 * scvfv
        $fv' : tr (Val Γ) Π[] (tr (Val Δ) ⌜evalT⌝ f +V σ) $ ? ⇒ fv'
        $fv' = ?
    in {!C' ,, fv' ,, $fv' ,, scvfv'!}


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
