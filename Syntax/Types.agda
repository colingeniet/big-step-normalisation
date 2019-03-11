{-# OPTIONS --safe --without-K #-}

{-
  Type and context definitions for the simply typed λ-calculus.
-}

module Syntax.Types where

infixr 15 _⟶_
data Ty : Set where
  o : Ty
  _⟶_ : Ty → Ty → Ty

infixr 10 _,_
data Con : Set where
  ● : Con
  _,_ : Con → Ty → Con


-- Context extension.
_++_ : Con → Con → Con
Γ ++ ● = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A
