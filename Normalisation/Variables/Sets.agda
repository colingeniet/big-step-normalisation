{-# OPTIONS --safe --cubical #-}

module Normalisation.Variables.Sets where

open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.Negation
open import Library.NotEqual
open import Library.Pairs
open import Library.Maybe
open import Syntax.Types
open import Syntax.Types.Sets
open import Normalisation.Variables
open import Agda.Builtin.Nat
open import Library.Nat.Sets


untype-var : {Γ : Con} {A : Ty} → Var Γ A → Nat
untype-var z = zero
untype-var (s x) = suc (untype-var x)

type-var : Nat → (Γ : Con) → Maybe (Σ[ A ∈ Ty ] Var Γ A)
type-var n ● = no
type-var zero (Γ , B) = yes (B ,, z)
type-var (suc n) (Γ , B) =
  maybe-lift (λ {(A ,, x) → A ,, s x}) (type-var n Γ)


type-var-inverse : {Γ : Con} {A : Ty} {x : Var Γ A} →
                   type-var (untype-var x) Γ ≡ yes (A ,, x)
type-var-inverse {x = z} = refl
type-var-inverse {Γ = Γ , B} {x = s x} =
  ap (maybe-lift (λ {(A ,, x) → A ,, s x}))
     (type-var-inverse {Γ = Γ} {x = x})

untype-var-injective : {Γ : Con} {A : Ty} {x y : Var Γ A} →
                   untype-var x ≡ untype-var y → x ≡ y
untype-var-injective {Γ = Γ} p =
  let p' = yes-injective (type-var-inverse ⁻¹
                         ∙ ap (λ x → type-var x Γ) p
                         ∙ type-var-inverse)
  in make-non-dependent {B = λ A → Var Γ A} isSetTy (apd snd p')


discreteVar : {Γ : Con} {A : Ty} → Discrete (Var Γ A)
discreteVar x y with discreteNat (untype-var x) (untype-var y)
...                | yes p = yes (untype-var-injective p)
...                | no n = no λ p → n (ap untype-var p)
