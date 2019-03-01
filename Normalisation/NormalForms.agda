{-# OPTIONS --safe --cubical #-}

{-
  Definition of normal forms.
-}

module Normalisation.NormalForms where

open import Syntax.Terms
open import Normalisation.NeutralForms


-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : Tm-like where
  nlam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  nneu : {Γ : Con} → Ne Nf Γ o → Nf Γ o

-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty} → Ne Nf Γ A → Tm Γ A
⌜ nlam u ⌝N = lam ⌜ u ⌝N
⌜ nneu n ⌝N = ⌜ n ⌝NN
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N

-- Weakenings:
-- - below a context.
nfgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Nf (Γ ++ Δ) B → (A : Ty) →
          Nf ((Γ , A) ++ Δ) B
nefgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Nf (Γ ++ Δ) B → (A : Ty) →
           Ne Nf ((Γ , A) ++ Δ) B
nfgenwk {B = B ⟶ C} Δ (nlam u) A = nlam (nfgenwk (Δ , B) u A)
nfgenwk Δ (nneu u) A = nneu (nefgenwk Δ u A)
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
