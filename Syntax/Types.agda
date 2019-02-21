{-# OPTIONS --safe --without-K #-}

module Syntax.Types where

infixr 15 _⟶_
data Ty : Set where
  o : Ty
  _⟶_ : Ty → Ty → Ty

infixr 10 _,_
data Con : Set where
  ● : Con
  _,_ : Con → Ty → Con
