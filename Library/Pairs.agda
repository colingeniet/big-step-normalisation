{-# OPTIONS --safe --cubical #-}

module Library.Pairs where

{-
  Dependent sum and cartesian product types.
-}

open import Agda.Primitive
-- Unit is often used together with pairs, and it does not cost much.
open import Agda.Builtin.Unit public
open import Agda.Builtin.Sigma public
  renaming (_,_ to _,,_)
open import Library.Equality

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    fst : A
    snd : B

open _×_ public

-- It can be convenient to have a unit type at an arbitrary level.
record ⊤l {l} : Set l where
  constructor tt

open ⊤l public


_,,≡_ : ∀ {a b} {A : Set a} {B : A → Set b} {a1 a2 : A} {b1 : B a1} {b2 : B a2} →
          (p : a1 ≡ a2) → b1 ≡[ ap B p ]≡ b2 → _≡_ {A = Σ A B} (a1 ,, b1) (a2 ,, b2)
(p ,,≡ q) i = p i ,, q i


infixr 4 _,,_ _×_ _,,≡_
