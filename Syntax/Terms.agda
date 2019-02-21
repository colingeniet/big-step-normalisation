{-# OPTIONS --safe --without-K #-}

module Syntax.Terms where

open import Syntax.Types

---- Terms Definition.
data Tm : Con → Ty → Set
data Tms : Con → Con → Set

infixr 10 _,_
infixr 20 _∘_
infixl 30 _[_]

data Tm where
  _[_] : {Γ Δ : Con} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  π₂ : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ , A) → Tm Γ A
  lam : {Γ : Con} {A B : Ty} → Tm (Γ , A) B → Tm Γ (A ⟶ B)
  app : {Γ : Con} {A B : Ty} → Tm Γ (A ⟶ B) → Tm (Γ , A) B
data Tms where
  id : {Γ : Con} → Tms Γ Γ
  _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  ε : {Γ : Con} → Tms Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)
  π₁ : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ , A) → Tms Γ Δ


---- Additional Constructions.

-- Weakening substitution.
wk : {Γ : Con} {A : Ty} → Tms (Γ , A) Γ
wk = π₁ id

-- Variables (De Brujin indices).
vz : {Γ : Con} {A : Ty} → Tm (Γ , A) A
vz = π₂ id
vs : {Γ : Con} {A B : Ty} → Tm Γ A → Tm (Γ , B) A
vs u = u [ wk ]

-- Weakening of terms, substitutions.
_+_ : {Γ : Con} {B : Ty} → Tm Γ B → (A : Ty) → Tm (Γ , A) B
u + A = u [ wk ]

_+s_ : {Γ Δ : Con} → Tms Γ Δ → (A : Ty) → Tms (Γ , A) Δ
σ +s A = σ ∘ wk

-- Context extension and corresponding weakenings.
_++_ : Con → Con → Con
Γ ++ ● = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

_++t_ : {Γ : Con} {A : Ty} → Tm Γ A → (Δ : Con) → Tm (Γ ++ Δ) A
u ++t ● = u
u ++t (Δ , A) = (u ++t Δ) + A

_++s_ : {Γ Δ : Con} → Tms Γ Δ → (Θ : Con) → Tms (Γ ++ Θ) Δ
σ ++s ● = σ
σ ++s (Θ , A) = (σ ++s Θ) +s A

-- Lifting of a substitution by a type.
_↑_ : {Γ Δ : Con} → Tms Γ Δ → (A : Ty) → Tms (Γ , A) (Δ , A)
σ ↑ A = σ ∘ wk , vz

-- Lifting by a context.
_↑↑_ : {Γ Δ : Con} → Tms Γ Δ → (Θ : Con) → Tms (Γ ++ Θ) (Δ ++ Θ)
σ ↑↑ ● = σ
σ ↑↑ (Θ , A) = (σ ↑↑ Θ) ↑ A

-- Regular application.
<_> : {Γ : Con} {A : Ty} → Tm Γ A → Tms Γ (Γ , A)
< u > = id , u

infixl 10 _$_
_$_ : {Γ : Con} {A B : Ty} → Tm Γ (A ⟶ B) → Tm Γ A → Tm Γ B
f $ u = (app f) [ < u > ]
