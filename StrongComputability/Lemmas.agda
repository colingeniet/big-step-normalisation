{-# OPTIONS --cubical --allow-unsolved-meta #-}

module StrongComputability.Lemmas where

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
open import StrongComputability.StrongComputability


abstract
  -- 'Constructor' for function types (the base constructors should not be needed).
  scvΠ-intro : {Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Val Δ (Π A B)} →
               ({Γ : Con} (σ : Wk Γ Δ) {v : Val Γ (A [ ⌜ σ ⌝w ]T)} → scv v →
               Σ[ C ∈ Ty Γ ] Σ[ fv ∈ Val Γ C ] (tr (Val _) Π[] (f +V σ) $ v ⇒ fv  ×  scv fv)) →
               scv f
  scvΠ-intro {Δ} {A} {B} {f} H {Γ} σ {v} scvv = {!!}
{-    let v' : Val Γ (A [ ⌜ σ ⌝w ]T)
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
        v''' : Val Γ (⌜ evalT A ⌝T [ ⌜ σ ⌝w ]T)
        v''' = tr (Val Γ) (⌜[]TV⌝ ⁻¹) v
        f+ : Val Γ (Π (A [ ⌜ σ ⌝w ]T) (B [ ⌜ σ ⌝w ↑ A ]T))
        f+ = tr (Val Γ) Π[] (f +V σ)
        f+' : Val Γ (Π (⌜ evalT A ⌝T [ ⌜ σ ⌝w ]T) (? [ ⌜ σ ⌝w ↑ _ ]T))
        f+' = tr (Val Γ) Π[] (tr (Val Δ) ⌜evalT⌝ f +V σ)
        $fv' : f+' $ v''' ⇒ fv'
        $fv' = {!!}
    in C' ,, fv' ,, $fv' ,, scvfv'-}
    
  -- 'Eliminator' for function types.
  scvΠ-elim : {Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Val Δ (Π A B)} → scv f →
              {Γ : Con} (σ : Wk Γ Δ) {v : Val Γ (A [ ⌜ σ ⌝w ]T)} → scv v →
              Σ[ C ∈ Ty Γ ] Σ[ fv ∈ Val Γ C ] (tr (Val _) Π[] (f +V σ) $ v ⇒ fv  ×  scv fv)
  scvΠ-elim {Δ} {A} {B} {f} scvf {Γ} σ {v} scvv = {!!}
