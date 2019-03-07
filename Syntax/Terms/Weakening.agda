{-# OPTIONS --safe --cubical #-}

module Syntax.Terms.Weakening where

open import Syntax.Terms


genwk : {Γ Δ : Con} {A : Ty} → Tms ((Γ , A) ++ Δ) (Γ ++ Δ)
genwk {Δ = ●} = wk
genwk {Δ = Δ , B} = genwk ↑ B
           
tmgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Tm (Γ ++ Δ) B →
          (A : Ty) → Tm ((Γ , A) ++ Δ) B
tmgenwk Δ u A = u [ genwk ]

tmsgenwk : {Γ Θ : Con} (Δ : Con) → Tms (Γ ++ Δ) Θ →
           (A : Ty) → Tms ((Γ , A) ++ Δ) Θ
tmsgenwk Δ σ A = σ ∘ genwk

_+_ : {Γ : Con} {B : Ty} → Tm Γ B → (A : Ty) → Tm (Γ , A) B
u + A = tmgenwk ● u A

_+s_ : {Γ Δ : Con} → Tms Γ Δ → (A : Ty) → Tms (Γ , A) Δ
σ +s A = tmsgenwk ● σ A

_++t_ : {Γ : Con} {A : Ty} → Tm Γ A → (Δ : Con) → Tm (Γ ++ Δ) A
u ++t ● = u
u ++t (Δ , A) = (u ++t Δ) + A

_++s_ : {Γ Δ : Con} → Tms Γ Δ → (Θ : Con) → Tms (Γ ++ Θ) Δ
σ ++s ● = σ
σ ++s (Θ , A) = (σ ++s Θ) +s A
