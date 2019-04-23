{-# OPTIONS --safe --cubical #-}

module NBE.Quote where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Syntax.List
open import Weakening.Presheaf
open import Weakening.Presheaf.Category
open import Weakening.Presheaf.Model
open import Weakening.Presheaf.List
open import Weakening.Variable
open import Syntax.Terms.Presheaf
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import NormalForm.Presheaf


NfPshModel : PshModel
NfPshModel = record { ⟦o⟧ = Nf' o }

open PshModel NfPshModel


-- Definition of quote and unquote.
q : (A : Ty) → Natw ⟦ A ⟧T (Nf' A)
u : (A : Ty) → Natw (NN' A) ⟦ A ⟧T

q o = idn

act (q (A ⟶ B)) Γ θ =
  let uz = act (u A) (Γ , A) (var z)
      xuz = act θ (Γ , A) (wkwk A idw ,, uz)
  in lam (act (q B) (Γ , A) xuz)
nat (q (A ⟶ B)) {Γ} {Δ} {σ} {θ} =
  let θ+ = θ +⟨ ⟦ A ⟶ B ⟧T ⟩ σ
      aθ = λ {Γ} → act θ Γ
      aθ+ = λ {Γ} → act θ+ Γ
      aβ = λ {Γ} → act (q B) Γ
      aα = λ {Γ} → act (u A) Γ
      p : σ ∘w wkwk A idw ≡ wkwk A idw ∘w wk↑ A σ
      p = σ ∘w wkwk A idw       ≡⟨ wkwk∘w ⁻¹ ⟩
          wkwk A σ ∘w idw       ≡⟨ ∘idw ⟩
          wkwk A σ              ≡⟨ ap (wkwk A) (id∘w ⁻¹) ⟩
          wkwk A (idw ∘w σ)     ≡⟨ wk∘↑w ⟩
          wkwk A idw ∘w wk↑ A σ ∎
  in ap lam
     (aβ (aθ+ (wkwk A idw ,, aα (var z)))
        ≡⟨ refl ⟩
      aβ (aθ (σ ∘w wkwk A idw ,, aα (var z)))
        ≡⟨ ap (λ ν → aβ (aθ (ν ,, aα (var z)))) p ⟩
      aβ (aθ (wkwk A idw ∘w wk↑ A σ ,, aα (var z)))
        ≡⟨ ap (λ x → aβ (aθ (wkwk A idw ∘w wk↑ A σ ,, x))) (nat (u A)) ⟩
      aβ (aθ (wkwk A idw ∘w wk↑ A σ ,, (aα (var z)) +⟨ ⟦ A ⟧T ⟩ (wk↑ A σ)))
        ≡⟨ ap aβ (nat θ) ⟩
      aβ (aθ (wkwk A idw ,, aα (var z)) +⟨ ⟦ B ⟧T ⟩ (wk↑ A σ))
        ≡⟨ nat (q B) ⟩
      (aβ (aθ (wkwk A idw ,, aα (var z)))) +N (wk↑ A σ)
        ∎)


act (u o) _ x = neu x
nat (u o) = refl

act (act (u (A ⟶ B)) Γ n) Δ (σ ,, x) =
  act (u B) Δ (app (n +NN σ) (act (q A) Δ x))
nat (act (u (A ⟶ B)) Θ n) {Γ} {Δ} {σ} {ν ,, x} =
  let aβ = λ {Γ} → act (u B) Γ
      aα = λ {Γ} → act (q A) Γ
  in aβ (app (n +NN (ν ∘w σ)) (aα (x +⟨ ⟦ A ⟧T ⟩ σ)))
        ≡⟨ ap (λ x → aβ (app x (aα _))) +NN∘ ⟩
     aβ (app ((n +NN ν) +NN σ) (aα (x +⟨ ⟦ A ⟧T ⟩ σ)))
        ≡⟨ ap (λ x → aβ (app _ x)) (nat (q A)) ⟩
     aβ ((app (n +NN ν) (aα x)) +⟨ NN' B ⟩ σ)
        ≡⟨ nat (u B) ⟩
     (aβ (app (n +NN ν) (aα x))) +⟨ ⟦ B ⟧T ⟩ σ
        ∎
nat (u (A ⟶ B)) {Δ} {Θ} {σ} {n} =
  nat≡ λ {i Γ (ν ,, x) →
          let aβ = λ {Γ} → act (u B) Γ
              aα = λ {Γ} → act (q A) Γ
              aαβ = λ {Γ} → act (u (A ⟶ B)) Γ
              p : act (act (u (A ⟶ B)) Δ (n +NN σ)) Γ (ν ,, x)
                  ≡ act ((act (u (A ⟶ B)) Θ n) +⟨ ⟦ A ⟶ B ⟧T ⟩ σ) Γ (ν ,, x)
              p = aβ (app ((n +NN σ) +NN ν) (aα x)) ≡⟨ ap (λ n → aβ (app n (aα x))) (+NN∘ ⁻¹) ⟩
                  aβ (app (n +NN (σ ∘w ν)) (aα x)) ∎
          in p i}


-- Unquoting and quoting allows to transform neutral normal forms into normal forms.
-- Effectively, it performs appropriate η-expansions.
uq : (A : Ty) → Natw (NN' A) (Nf' A)
uq A = (q A) ∘n (u A)

-- Normalising requires to unquote the identity substitution.
us : (Γ : Con) → Natw (NNs' Γ) ⟦ Γ ⟧C
us Γ = mapn (λ {A} → u A)

us-wk : (Γ : Con) → Natw (Wk' Γ) ⟦ Γ ⟧C
us-wk Γ = us Γ ∘n varsp

uid : {Γ : Con} → ⟦ Γ ⟧C $o Γ
uid {Γ} = act (us-wk Γ) Γ idw


norm : ∀ {Γ} {A} → Tm Γ A → Nf Γ A
norm {Γ} {A} u = act (q A) Γ (act ⟦ u ⟧ Γ uid)
