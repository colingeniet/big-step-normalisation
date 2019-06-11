{-# OPTIONS --cubical #-}

module StrongComputability.Weakening where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator
open import Evaluator.Weakening
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Evaluator
open import StrongComputability.StrongComputability


abstract
  _+scvTV_ : {S : TSk} {Γ Δ : Con} {A : TV S Δ} {v : Val Δ ⌜ A ⌝T} →
             scvTV A v → (σ : Wk Γ Δ) → scvTV (A [ ⌜ σ ⌝w ]TV) (tr (Val Γ) ⌜[]TV⌝ (v +V σ))
  _+scvTV_ {A = U} {v} (n ,, qn) σ =
   tr (Nf _) (⌜[]TV⌝ {A = U}) (n +N σ) ,,
   (λ i → q trfill (Val _) (⌜[]TV⌝ {A = U}) (v +V σ) i
          ⇒ trfill (Nf _) (⌜[]TV⌝ {A = U}) (n +N σ) i)
   * (qn +q σ)
  _+scvTV_ {A = El u} {v} (n ,, qn) σ =
   tr (Nf _) (⌜[]TV⌝ {A = El u}) (n +N σ) ,,
   (λ i → q trfill (Val _) (⌜[]TV⌝ {A = El u}) (v +V σ) i
          ⇒ trfill (Nf _) (⌜[]TV⌝ {A = El u}) (n +N σ) i)
   * (qn +q σ)
  _+scvTV_ {Π S T} {Γ} {Δ} {Π A B} {f} scvf σ {Θ} δ {v} scvv =
    let A+ = A [ ⌜ σ ⌝w ]TV [ ⌜ δ ⌝w ]TV
        A+' = A [ ⌜ σ ∘w δ ⌝w ]TV
        P : A+ ≡ A+'
        P = A [ ⌜ σ ⌝w ]TV [ ⌜ δ ⌝w ]TV ≡⟨ [][]TV ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ δ ⌝w ]TV     ≡⟨ ap (A [_]TV) (⌜∘⌝w ⁻¹) ⟩
            A [ ⌜ σ ∘w δ ⌝w ]TV        ∎
        v' : Val Θ ⌜ A+' ⌝T
        v' = tr (λ x → Val Θ ⌜ x ⌝T) P v
        v≡v' = trfill (λ x → Val Θ ⌜ x ⌝T) P v
        scvv' : scvTV A+' v'
        scvv' = (λ i → scvTV (P i) (v≡v' i)) * scvv
        C ,, fv ,, $fv ,, scvfv = scvf (σ ∘w δ) scvv'
        p : tr (Val Θ) Π[] (f +V (σ ∘w δ))
            ≅[ Val Θ ] tr (Val Θ) Π[] (tr (Val Γ) ⌜[]TV⌝ (f +V σ) +V δ)
        p = tr (Val Θ) Π[] (f +V (σ ∘w δ))
              ≅⟨ trfill (Val Θ) Π[] (f +V (σ ∘w δ)) ⁻¹ ⟩
            f +V (σ ∘w δ)
              ≅⟨ +V∘ {v = f} ⟩
            (f +V σ) +V δ
              ≅⟨ apd (_+V δ) (trfill (Val Γ) ⌜[]TV⌝ (f +V σ)) ⟩
            (tr (Val Γ) ⌜[]TV⌝ (f +V σ)) +V δ
              ≅⟨ trfill (Val Θ) Π[] _ ⟩
            tr (Val Θ) Π[] (tr (Val Γ) ⌜[]TV⌝ (f +V σ) +V δ) ≅∎
        q : tr (Val Θ) (⌜[]TV⌝ ⁻¹) v' ≅[ Val  Θ ] tr (Val Θ) (⌜[]TV⌝ ⁻¹) v
        q = tr (Val Θ) (⌜[]TV⌝ ⁻¹) v' ≅⟨ trfill (Val Θ) (⌜[]TV⌝ ⁻¹) v' ⁻¹ ⟩
            v'                       ≅⟨ trfill (λ x → Val Θ ⌜ x ⌝T) P v ⁻¹ ⟩
            v                        ≅⟨ trfill (Val Θ) (⌜[]TV⌝ ⁻¹) v ⟩
            tr (Val Θ) (⌜[]TV⌝ ⁻¹) v  ≅∎
        Q : ⌜ A ⌝T [ ⌜ σ ∘w δ ⌝w ]T ≡ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T [ ⌜ δ ⌝w ]T
        Q = ⌜ A ⌝T [ ⌜ σ ∘w δ ⌝w ]T       ≡⟨ ap (⌜ A ⌝T [_]T) ⌜∘⌝w ⟩
            ⌜ A ⌝T [ ⌜ σ ⌝w ∘ ⌜ δ ⌝w ]T    ≡⟨ [][]T ⟩
            ⌜ A ⌝T [ ⌜ σ ⌝w ]T [ ⌜ δ ⌝w ]T ≡⟨ ap (_[ ⌜ δ ⌝w ]T) ⌜[]TV⌝ ⟩
            ⌜ A [ ⌜ σ ⌝w ]TV ⌝T [ ⌜ δ ⌝w ]T ∎
        R : ⌜ B ⌝T [ ⌜ σ ∘w δ ⌝w ↑ ⌜ A ⌝T ]T ≅[ Ty ]
            ⌜ tr (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) ⌝T [ ⌜ δ ⌝w ↑ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T ]T
        R = ⌜ B ⌝T [ ⌜ σ ∘w δ ⌝w ↑ ⌜ A ⌝T ]T
              ≅⟨ apd (λ x → ⌜ B ⌝T [ x ↑ ⌜ A ⌝T ]T) (⌜∘⌝w {σ = σ} {δ}) ⟩
            ⌜ B ⌝T [ (⌜ σ ⌝w ∘ ⌜ δ ⌝w) ↑ ⌜ A ⌝T ]T
              ≅⟨ ap≅ (⌜ B ⌝T [_]T) ↑∘↑ ≅⁻¹ ⟩'
            ⌜ B ⌝T [ (⌜ σ ⌝w ↑ ⌜ A ⌝T) ∘ (⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T) ]T
              ≅⟨ [][]T ⟩
            ⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T
              ≅⟨ apd (λ x → x [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T) (⌜[]TV⌝ {A = B} {⌜ σ ⌝w ↑ ⌜ A ⌝T})  ⟩
            ⌜ B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV ⌝T [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T
              ≅⟨ (λ i → ⌜ trfill (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) i ⌝T
                        [ ⌜ δ ⌝w ↑ (⌜[]TV⌝ {A = A} i) ]T) ⟩
            ⌜ tr (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) ⌝T [ ⌜ δ ⌝w ↑ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T ]T ≅∎
        $fv' = (λ i → (≅-to-≡[] isSetTy p {P = λ i → Π (Q i) (≅-to-≡[] isSetCon R {P = ap (Θ ,_) Q} i)} i)
                      $ (≅-to-≡[] isSetTy q {P = Q} i)
                      ⇒ fv)
               * $fv
    in C ,, fv ,, $fv' ,, scvfv


  _+scv_ : {Γ Δ : Con} {A : Ty Δ} {v : Val Δ A} → scv v → (σ : Wk Γ Δ) → scv (v +V σ)
  _+scv_ {A = A} {v} scvv σ =
    let p : tr (Val _) ⌜[]TV⌝ (tr (Val _) ⌜evalT⌝ v +V σ)
            ≡ tr (Val _) ⌜evalT⌝ (v +V σ)
        p = ≅-to-≡ {B = Val _} isSetTy (
              tr (Val _) ⌜[]TV⌝ (tr (Val _) ⌜evalT⌝ v +V σ)
                ≅⟨ trfill (Val _) ⌜[]TV⌝ _ ⁻¹ ⟩
              tr (Val _) ⌜evalT⌝ v +V σ ≅⟨ apd (_+V σ) (trfill (Val _) ⌜evalT⌝ v) ⁻¹ ⟩
              v +V σ                   ≅⟨ trfill (Val _) ⌜evalT⌝ (v +V σ) ⟩
              tr (Val _) ⌜evalT⌝ (v +V σ) ≅∎)
    in tr (scvTV _) p (scvv +scvTV σ)

  _+sce_ : {Γ Δ Θ : Con} {ρ : Env Δ Θ} → sce ρ → (σ : Wk Γ Δ) → sce (ρ +E σ)
  _+sce_ {ρ = ε} tt A = tt
  _+sce_ {ρ = ρ , v} (sceρ ,, scvv) σ =
    sceρ +sce σ ,, trd scv (trfill (Val _) ([+E] ⁻¹) (v +V σ)) (_+scv_ {v = v} scvv σ)

{-
-- Weakenings lemmas.
π₁sce+ : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₁sce (sceρ +sce σ) ≡[ ap sce (π₁+ {ρ = ρ}) ]≡ (π₁sce sceρ) +sce σ
π₁sce+ {ρ = _ , _} = refl

π₂sce+ : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₂sce {ρ = ρ +E σ} (_+sce_ {ρ = ρ} sceρ σ)
         ≅[ {!!} ] _+scv_ {v = π₂E ρ} (π₂sce {ρ = ρ} sceρ) σ
π₂sce+ {ρ = _ , _} = {!!}
-}

