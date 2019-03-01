{-# OPTIONS --safe --without-K #-}

module Library.Pairs where

{-
  Dependent sum and cartesian product types.
-}

open import Agda.Primitive
-- Unit is often used together with pairs, and it does not cost much.
open import Agda.Builtin.Unit public
open import Agda.Builtin.Sigma public
  -- _,_ is used for contexts and substitutions throughout this project with
  -- a different precedence.
  renaming (_,_ to _,,_)

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    fst : A
    snd : B

open _×_ public

infixr 4 _,,_ _×_
