{-# OPTIONS --safe --cubical #-}

module Normalisation.Substitutions where

open import Library.Equality
open import Library.Negation
open import Library.Decidable
open import Syntax.Types
open import Syntax.Types.Sets
open import Syntax.Weakening
open import Normalisation.Variables
open import Normalisation.Variables.Eliminator
open import Normalisation.Variables.Sets
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Weakening


_-_ : (Γ : Con) {A : Ty} → Var Γ A → Con
(Γ , A) - z = Γ
(Γ , A) - (s x) = (Γ - x) , A

-- If two variables are not equal, then the second is still here after removing
-- the first from the context.
-- Case 1: the variables have different types.
stillHere1 : {Γ : Con} {A B : Ty} (x : Var Γ A) →
             Var Γ B → ¬ (A ≡ B) → Var (Γ - x) B
stillHere1 z z n = ⊥-elim (n refl)
stillHere1 z (s x) _ = x
stillHere1 (s x) z _ = z
stillHere1 {Γ , A} (s x) (s y) n = s (stillHere1 x y n)
-- Case 2: the variables are different, of the same type.
stillHere2 : {Γ : Con} {A : Ty} (x : Var Γ A) →
             (y : Var Γ A) → ¬ (x ≡ y) → Var (Γ - x) A
stillHere2 {Γ , A} z = elimVar (λ y → ¬ (z ≡ y) → Var Γ A)
                               (λ p → ⊥-elim (p refl))
                               (λ y _ → y)
stillHere2 (s x) z _ = z
stillHere2 {Γ , A} (s x) (s y) n =
  let n' : ¬ (x ≡ y)
      n' = λ p → n (ap s p)
  in s (stillHere2 x y n')

-- The two together, using heterogeneous equality.
stillHere : {Γ : Con} {A B : Ty} (x : Var Γ A) (y : Var Γ B) →
            ¬ (x ≅⟨ Var Γ ⟩ y) → Var (Γ - x) B
stillHere {Γ} {A} {B} x y n
  with discreteTy A B
...  | yes p = J (λ {B} p → (y : Var Γ B) → ¬ (x ≡[ ap (Var Γ) p ]≡ y) → Var (Γ - x) B)
                 (stillHere2 x) p y (λ q → n (p ,≅ q))
...  | no n' = stillHere1 x y n'


_[_↦_]N : {Γ : Con} {A B : Ty} → Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B
_[_↦_]Ne : {Γ : Con} {A B : Ty} → Ne Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B
_[_↦_]Sp : {Γ : Con} {A B C : Ty} → Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C
appNf : {Γ : Con} {A B : Ty} → Nf Γ (A ⟶ B) → Nf Γ A → Nf Γ B
appSp : {Γ : Con} {A B : Ty} → Nf Γ A → Sp Γ A B → Nf Γ B

(lam n) [ x ↦ m ]N = lam (n [ s x ↦ m +N (drop _ idw) ]N)
(neu n) [ x ↦ m ]N = n [ x ↦ m ]Ne
_[_↦_]Ne {Γ} {A} {B} (x # ns) y m
  with discreteHeterogeneousVar y x
...  | yes p = appSp m (tr (λ A → Sp (Γ - y) A B) (fst p ⁻¹) (ns [ y ↦ m ]Sp))
...  | no n = nenf (stillHere y x n # ns [ y ↦ m ]Sp)

nil [ _ ↦ _ ]Sp = nil
(n ∷ ns) [ x ↦ m ]Sp = n [ x ↦ m ]N ∷ ns [ x ↦ m ]Sp

appNf (lam n) m = n [ z ↦ m ]N

appSp n nil = n
appSp f (n ∷ ns) = appSp (appNf f n) ns
