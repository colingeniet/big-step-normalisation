{-# OPTIONS --safe --cubical #-}

{-
  Definition of normal forms.
-}

module NormalForm.NormalForm where

open import Syntax.Terms
open import Weakening.Variable.Base


-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : Con → Ty → Set
data NN : Con → Ty → Set

data Nf where
  lam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  neu : {Γ : Con} → NN Γ o → Nf Γ o

data NN where
  var : {Γ : Con} {A : Ty} → Var Γ A → NN Γ A
  app : {Γ : Con} {A B : Ty} → NN Γ (A ⟶ B) → Nf Γ A → NN Γ B


-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty} → NN Γ A → Tm Γ A
⌜ lam u ⌝N = lam ⌜ u ⌝N
⌜ neu n ⌝N = ⌜ n ⌝NN
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N
