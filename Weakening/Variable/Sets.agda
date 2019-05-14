{-# OPTIONS --safe --cubical #-}

module Weakening.Variable.Sets where

open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.Negation
open import Library.NotEqual
open import Library.Pairs
open import Library.Maybe
open import Syntax.Types
open import Syntax.Types.Sets
open import Syntax.List
open import Weakening.Variable.Base
open import Agda.Builtin.Nat
open import Library.Nat.Sets

{-
  The indexing of variables by contexts and types makes deciding equality
  suprisingly annoying: even the seemingly obvious base case
    discreteVar z z = yes refl
  fails because the duplicated constraints  Γ = Γ' , A  can not be unified
  without K.
  A way to avoid this problem is to define untyping of variables, decide
  equality of untyped variables (i.e. natural numbers), then re-type.
-}

untype-var : {Γ : Con} {A : Ty} → Var Γ A → Nat
untype-var z = zero
untype-var (s x) = suc (untype-var x)

-- Note that typing of variables is only a partial function.
type-var : (Γ : Con) → Nat → Maybe (Σ[ A ∈ Ty ] Var Γ A)
type-var ● n = no
type-var (Γ , B) zero = yes (B ,, z)
type-var (Γ , B) (suc n) =
  maybe-lift (λ {(A ,, x) → A ,, s x}) (type-var Γ n)

-- However, type-var is a left inverse of untype-var.
type-var-inverse : {Γ : Con} {A : Ty} {x : Var Γ A} →
                   type-var Γ (untype-var x) ≡ yes (A ,, x)
type-var-inverse {x = z} = refl
type-var-inverse {Γ , _} {x = s x} =
  ap (maybe-lift (λ {(A ,, x) → A ,, s x}))
     (type-var-inverse {Γ = Γ} {x = x})

-- Thus untype-var is injective.
untype-var-injective : {Γ : Con} {A : Ty} {x y : Var Γ A} →
                       untype-var x ≡ untype-var y → x ≡ y
untype-var-injective {Γ} p =
  let p' = yes-injective (type-var-inverse ⁻¹
                         ∙ ap (type-var Γ) p
                         ∙ type-var-inverse)
  in make-non-dependent {B = λ A → Var Γ A} isSetTy (apd snd p')

-- Using injectivity, it suffice to decide equality of untyped variables.
discreteVar : {Γ : Con} {A : Ty} → Discrete (Var Γ A)
discreteVar x y with discreteNat (untype-var x) (untype-var y)
...                | yes p = yes (untype-var-injective p)
...                | no n = no λ p → n (ap untype-var p)

isSetVar : {Γ : Con} {A : Ty} → isSet (Var Γ A)
isSetVar = DiscreteisSet discreteVar


discreteWk : {Γ Δ : Con} → Discrete (Wk Γ Δ)
discreteWk = discreteList discreteVar

isSetWk : {Γ Δ : Con} → isSet (Wk Γ Δ)
isSetWk = DiscreteisSet discreteWk
