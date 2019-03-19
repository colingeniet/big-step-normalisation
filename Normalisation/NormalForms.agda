{-# OPTIONS --safe --cubical #-}

{-
  Definition of normal forms.
-}

module Normalisation.NormalForms where

open import Syntax.Terms
open import Normalisation.TermLike
open import Normalisation.Variables
open import Normalisation.NeutralForms public


-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : Tm-like where
  lam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  neu : {Γ : Con} → Ne Nf Γ o → Nf Γ o

-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty} → Ne Nf Γ A → Tm Γ A
⌜ lam u ⌝N = lam ⌜ u ⌝N
⌜ neu n ⌝N = ⌜ n ⌝NN
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N
