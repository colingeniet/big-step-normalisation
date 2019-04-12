{-# OPTIONS --safe --cubical #-}

{-
  General constructions on 'things that look like terms',
  e.g. values, normal forms...
-}

module Syntax.TermLike where

open import Library.Equality
open import Syntax.Terms


-- This type is common to all the above
Tm-like : Set₁
Tm-like = (Γ : Con) (A : Ty) → Set
Tms-like : Set₁
Tms-like = (Γ Δ : Con) → Set

-- Lifting from Tm-like to Tms-like (it's just a list).
infix 60 list
infixl 10 _,_
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
