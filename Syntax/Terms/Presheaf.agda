{-# OPTIONS --safe --cubical #-}

module Syntax.Terms.Presheaf where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Weakening
open import Weakening.Variable
open import Weakening.Presheaf


Tm' : Ty → Pshw
(Tm' A) $o Γ = Tm Γ A
isSetapply (Tm' A) = isSetTm
u +⟨ Tm' A ⟩ σ = u +t σ
+id (Tm' A) = +tid
+∘ (Tm' A) = +t∘

Tms' : Con → Pshw
(Tms' Δ) $o Γ = Tms Γ Δ
isSetapply (Tms' Δ) = isSetTms
σ +⟨ Tms' Δ ⟩ ν = σ +s ν
+id (Tms' Δ) = +sid
+∘ (Tms' Δ) = +s∘
