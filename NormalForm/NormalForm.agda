{-# OPTIONS --cubical #-}

{-
  Definition of normal forms.
-}

module NormalForm.NormalForm where

open import Library.Sets
open import Syntax.Terms
open import Variable.Variable


-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : (Γ : Con) → Ty Γ → Set
data NN : (Γ : Con) → Ty Γ → Set

-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty Γ} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty Γ} → NN Γ A → Tm Γ A

data Nf where
  lam : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Nf (Γ , A) B → Nf Γ (Π A B)
  neuU : {Γ : Con} → NN Γ U → Nf Γ U
  neuEl : {Γ : Con} {u : Tm Γ U} → NN Γ (El u) → Nf Γ (El u)

data NN where
  var : {Γ : Con} {A : Ty Γ} → Var Γ A → NN Γ A
  app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
        NN Γ (Π A B) → (n : Nf Γ A) → NN Γ (B [ < ⌜ n ⌝N > ])


⌜ lam u ⌝N = lam ⌜ u ⌝N
⌜ neuU n ⌝N = ⌜ n ⌝NN
⌜ neuEl n ⌝N = ⌜ n ⌝NN
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N
