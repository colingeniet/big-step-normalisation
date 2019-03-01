{-# OPTIONS --safe --cubical #-}

{-
  Definition of variables and neutral forms.
  This are used to define both values and normal forms.
-}

module Normalisation.NeutralForms where

open import Syntax.Terms
open import Syntax.Lemmas
open import Library.Equality


-- Variables, values, normal forms, ... all have this type.
Tm-like : Set₁
Tm-like = (Γ : Con) (A : Ty) → Set
Tms-like : Set₁
Tms-like = (Γ Δ : Con) → Set

-- Lifting from Tm-like to Tms-like (it's just a list).
infix 60 list
infixr 10 _,_
data list (X : Tm-like) : Tms-like where
  ε : {Γ : Con} → list X Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → list X Γ Δ → X Γ A → list X Γ (Δ , A)

-- Associated projections.
π₁list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → list X Γ Δ
π₁list (σ , _) = σ
π₂list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → X Γ A
π₂list (_ , u) = u

πηlist : {X : Tm-like} {Γ Δ : Con} {A : Ty} {ρ : list X Γ (Δ , A)} →
         (π₁list ρ , π₂list ρ) ≡ ρ
πηlist {ρ = ρ , u} = refl



-- Variables.
data Var : Tm-like where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

-- 's' is already the weakening of variables by a type.
-- Weakening by a context.
_++v_ : {Γ : Con} {A : Ty} → Var Γ A → (Δ : Con) → Var (Γ ++ Δ) A
x ++v ● = x
x ++v (Δ , B) = s (x ++v Δ)

-- Weakening below a context.
varwk : {Γ : Con} (Δ : Con) {B : Ty} → Var (Γ ++ Δ) B → (A : Ty) →
          Var ((Γ , A) ++ Δ) B
varwk ● x A = s x
varwk (Δ , C) z A = z
varwk (Δ , C) (s x) A = s (varwk Δ x A)

varwk≡ : {Γ Δ : Con} {A B : Ty} {x : Var (Γ ++ Δ) B} →
         ⌜ varwk Δ x A ⌝v ≡ tmgenwk Δ ⌜ x ⌝v A
varwk≡ {Δ = ●} {x = x} = refl
varwk≡ {Δ = Δ , C} {A} {x = z} = π₂β ⁻¹ ∙ ap π₂ id∘ ⁻¹ ∙ π₂∘
varwk≡ {Δ = Δ , C} {A} {x = s x} =
  ap vs (varwk≡ {Δ = Δ} {A} {x = x})
  ∙ [][] ⁻¹
  ∙ ap (λ σ → ⌜ x ⌝v [ σ ])
       (π₁β ⁻¹ ∙ ap π₁ id∘ ⁻¹ ∙ π₁∘)
  ∙ [][]


-- Neutral forms : a variable applied to terms satisfying P.
-- This is used both for values and normal forms, hence the general definition.
data Ne (X : Tm-like) : Tm-like where
  var : {Γ : Con} {A : Ty} → Var Γ A → Ne X Γ A
  app : {Γ : Con} {A B : Ty} → Ne X Γ (A ⟶ B) → X Γ A → Ne X Γ B
