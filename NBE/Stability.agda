{-# OPTIONS --safe --cubical #-}

module NBE.Stability where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Weakening.Variable
open import Weakening.Presheaf
open import Weakening.Presheaf.Cartesian
open import Weakening.Presheaf.List
open import Weakening.Presheaf.Model
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import NBE.Quote

open PshModel NfPshModel


-- Modulo the appropriate unquotings, the action of the interpretation of a variable
-- on a weakening is simply the weakening of that variable.
var-u : ∀ {Γ} {Δ} {A} {x : Var Δ A} {σ : Wk Γ Δ} →
          act ⟦ ⌜ x ⌝v ⟧ Γ (act (us-wk Δ) Γ σ) ≡ act (u A) Γ (var (x +v σ))
var-u {x = z} = refl
var-u {x = s x} {σ ,, _} = var-u {x = x} {σ}

-- As a special case, the action of the interpretation of a variable
-- on the (unquoted) indentity is just this very variable, unquoted.
-- This is the base case for the proof of stability.
u-var-stable : ∀ {Γ} {A} {x : Var Γ A} →
                 act ⟦ ⌜ x ⌝v ⟧ Γ uid ≡ act (u A) Γ (var x)
u-var-stable {Γ} {A} {x} =
  act ⟦ ⌜ x ⌝v ⟧ Γ uid          ≡⟨ var-u {x = x} ⟩
  act (u A) Γ (var (x +v idw)) ≡⟨ ap (λ x → act (u A) Γ (var x)) +vid ⟩
  act (u A) Γ (var x)          ∎



-- The lambda case of stability requires to prove an alternative inductive
-- definition of the unquoted identity environment.
uid-expand-nat : ∀ {Γ} {A} →
                   (uid {Γ}) +⟨ ⟦ Γ ⟧C ⟩ (wkwk A idw)
                   ≡ act (us-wk Γ) (Γ , A) (wkwk A idw)
uid-expand-nat {Γ} {A} =
  (act (us-wk Γ) Γ idw) +⟨ ⟦ Γ ⟧C ⟩ (wkwk A idw)
    ≡⟨ nat (us-wk Γ) ⁻¹ ⟩
  act (us-wk Γ) (Γ , A) (idw +⟨ Wk' Γ ⟩ (wkwk A idw))
    ≡⟨ ap (act (us-wk Γ) (Γ , A)) id∘w ⟩
  act (us-wk Γ) (Γ , A) (wkwk A idw) ∎

uid-expand : ∀ {Γ} {A} →
               ((uid {Γ}) +⟨ ⟦ Γ ⟧C ⟩ (wkwk A idw) ,, act (u A) (Γ , A) (var z))
               ≡ uid {Γ , A}
uid-expand {Γ} {A} =
  ap (λ x → x ,, act (u A) (Γ , A) (var z)) uid-expand-nat



-- Stability of normalisation on normal forms.
norm-nf-stable : ∀ {Γ} {A} {n : Nf Γ A} → norm ⌜ n ⌝N ≡ n
u-nn-stable : ∀ {Γ} {A} {n : NN Γ A} → act ⟦ ⌜ n ⌝NN ⟧ Γ uid ≡ act (u A) Γ n

norm-nf-stable {n = lam {Γ} {A} {B} n} =
  let aq = λ {Γ} {A} → act (q A) Γ
      au = λ {Γ} {A} → act (u A) Γ
  in lam (aq (act ⟦ ⌜ n ⌝N ⟧ (Γ , A)
                  (uid +⟨ ⟦ Γ ⟧C ⟩ (wkwk A idw) ,, act (u A) (Γ , A) (var z))))
       ≡⟨ ap (λ σ → lam (aq (act ⟦ ⌜ n ⌝N ⟧ (Γ , A) σ))) uid-expand ⟩
     lam (aq (act ⟦ ⌜ n ⌝N ⟧ (Γ , A) uid))
       ≡⟨ ap lam (norm-nf-stable {n = n}) ⟩
     lam n ∎
norm-nf-stable {n = neu n} =
  ap (act (q _) _) (u-nn-stable {n = n})

u-nn-stable {n = var x} =
  u-var-stable {x = x}
u-nn-stable {n = app {Γ} {A} {B} f n} =
  act (act ⟦ ⌜ f ⌝NN ⟧ Γ uid) Γ (idw ,, act ⟦ ⌜ n ⌝N ⟧ Γ uid)
      ≡⟨ ap (λ x → act x Γ _) (u-nn-stable {n = f}) ⟩
  act (act (u (A ⟶ B)) Γ f) Γ (idw ,, act ⟦ ⌜ n ⌝N ⟧ Γ uid)
      ≡⟨ refl ⟩
  act (u B) Γ (app (f +NN idw) (norm ⌜ n ⌝N))
      ≡⟨ ap2 (λ f n → act (u B) Γ (app f n)) +NNid norm-nf-stable ⟩
  act (u B) Γ (app f n) ∎



⌜⌝N-injective : ∀ {Γ} {A} {n m : Nf Γ A} → ⌜ n ⌝N ≡ ⌜ m ⌝N → n ≡ m
⌜⌝N-injective {n = n} {m} p =
  n ≡⟨ norm-nf-stable ⁻¹ ⟩
  norm ⌜ n ⌝N ≡⟨ ap norm p ⟩
  norm ⌜ m ⌝N ≡⟨ norm-nf-stable ⟩
  m ∎
