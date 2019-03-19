{-# OPTIONS --safe --cubical #-}

module Normalisation.NormalForms.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Normalisation.Variables.Weakening
open import Normalisation.NormalForms

-- Weakenings:
-- - below a context.
nfgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Nf (Γ ++ Δ) B → (A : Ty) →
          Nf ((Γ , A) ++ Δ) B
nefgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Nf (Γ ++ Δ) B → (A : Ty) →
           Ne Nf ((Γ , A) ++ Δ) B
nfgenwk {B = B ⟶ C} Δ (lam u) A = lam (nfgenwk (Δ , B) u A)
nfgenwk Δ (neu u) A = neu (nefgenwk Δ u A)
nefgenwk Δ (var x) A = var (varwk Δ x A)
nefgenwk Δ (app f u) A = app (nefgenwk Δ f A) (nfgenwk Δ u A)

-- - simple.
_+N_ : {Γ : Con} {B : Ty} → Nf Γ B → (A : Ty) → Nf (Γ , A) B
u +N A = nfgenwk ● u A
_+NN_ : {Γ : Con} {B : Ty} → Ne Nf Γ B → (A : Ty) → Ne Nf (Γ , A) B
u +NN A = nefgenwk ● u A

-- - by a context.
_++N_ : {Γ : Con} {A : Ty} → Nf Γ A → (Δ : Con) → Nf (Γ ++ Δ) A
u ++N ● = u
u ++N (Δ , A) = (u ++N Δ) +N A
_++NN_ : {Γ : Con} {A : Ty} → Ne Nf Γ A → (Δ : Con) → Ne Nf (Γ ++ Δ) A
u ++NN ● = u
u ++NN (Δ , A) = (u ++NN Δ) +NN A


N+-++ : {Γ Δ : Con} {A B : Ty} {n : Nf Γ A} →
        (n +N B) ++N Δ ≡[ ap (λ Γ → Nf Γ A) ,++ ]≡ n ++N ((● , B) ++ Δ)
N+-++ {Δ = ●} = refl
N+-++ {Δ = Δ , C} = apd (λ n → n +N C) (N+-++ {Δ = Δ})
