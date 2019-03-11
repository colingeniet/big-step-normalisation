{-# OPTIONS --safe --cubical #-}

{-
  Definition of variables.
-}

module Normalisation.Variables where

open import Syntax.Terms
open import Normalisation.TermLike

data Var : Tm-like where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v
