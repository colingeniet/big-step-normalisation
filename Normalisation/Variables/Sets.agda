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
open import Normalisation.Variables.Eliminator


z≢s : {Γ : Con} {A : Ty} {x : Var Γ A} → ¬ (z ≡ s x)
z≢s {Γ} {A} p =
  ⊤≢⊥ (ap f p)
  where f : Var (Γ , A) A → Set
        f = elimVar (λ _ → Set) ⊤ (λ _ → ⊥)

s-injective : {Γ : Con} {A B : Ty} {x y : Var Γ A} →
              s {B = B} x ≡ s y → x ≡ y
s-injective p = yes-injective (ap (λ {(s x) → yes x; z → no}) p)


discreteVar : {Γ : Con} {A : Ty} → Discrete (Var Γ A)
discreteVar z = elimVar (λ y → Decidable (z ≡ y))
                        (yes refl) (λ _ → no z≢s)
discreteVar (s x) z = no λ p → z≢s (p ⁻¹)
discreteVar (s x) (s y)
  with discreteVar x y
...  | yes p = yes (ap s p)
...  | no n = no λ p → n (s-injective p)



z≇s : {Γ : Con} {A B : Ty} {x : Var Γ B} →
      ¬ (z {A = A} ≅⟨ Var (Γ , A) ⟩ (s {B = A} x))
z≇s {Γ} {A} {B} p =
  ⊤≢⊥ (apd f (snd p))
  where f : {C : Ty} → Var (Γ , A) C → Set
        f z = ⊤
        f (s _) = ⊥

s-heterogeneousInjective : {Γ : Con} {A B C : Ty} {x : Var Γ A} {y : Var Γ B} →
                           s x ≅⟨ Var (Γ , C) ⟩ s y → x ≅⟨ Var Γ ⟩ y
s-heterogeneousInjective p =
  ≡[]-to-≅ (yes-injective (apd f (snd p)))
  where f : {Γ : Con} {A B : Ty} → Var (Γ , B) A → Maybe (Var Γ A)
        f (s x) = yes x
        f z = no

discreteHeterogeneousVar : {Γ : Con} {A B : Ty} (x : Var Γ A) (y : Var Γ B) →
                           Decidable (x ≅⟨ Var Γ ⟩ y)
discreteHeterogeneousVar z z = yes (≡-to-≅ refl)
discreteHeterogeneousVar z (s x) = no z≇s
discreteHeterogeneousVar (s x) z = no λ p → z≇s (p ≅⁻¹)
discreteHeterogeneousVar (s x) (s y)
  with discreteHeterogeneousVar x y
...  | yes p = yes (≡[]-to-≅ (apd s (snd p)))
...  | no n = no λ p → n (s-heterogeneousInjective p)
