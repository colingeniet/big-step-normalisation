{-# OPTIONS --safe --cubical #-}

{-
  Definition of variables and weakenings.
  Weakenings are defined in the very broad sense of lists of variables
  (aka renamings).
-}

module Weakening.Variable where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.List
open import Syntax.Terms.Presheaf
open import Weakening.Presheaf
open import Weakening.Presheaf.List
open import Weakening.Variable.Sets

-- The basic definition is separated to avoid mutual dependency with presheaves.
-- It should not be imported manually.
open import Weakening.Variable.Base public

-- Variables laws.
+vwk : {Γ Δ : Con} {A B : Ty} {x : Var Δ A} {σ : Wk Γ Δ} →
       x +v (wkwk B σ) ≡ s (x +v σ)
+vwk {x = z} {σ = _ , _} = refl
+vwk {x = s x} {σ = σ , _} = +vwk {x = x} {σ = σ}

+vid : {Γ : Con} {A : Ty} {x : Var Γ A} → x +v idw ≡ x
+vid {x = z} = refl
+vid {x = s x} = +vwk {x = x} {σ = idw} ∙ ap s (+vid {x = x})

+v∘ : {Γ Δ Θ : Con} {A : Ty} {x : Var Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      x +v (σ ∘w ν) ≡ (x +v σ) +v ν
+v∘ {x = z} {σ = _ , _} = refl
+v∘ {x = s x} {σ = σ , _} = +v∘ {x = x} {σ = σ}

-- Associated presheaf.
Var' : Ty → Pshw
(Var' A) $o Γ = Var Γ A
isSetapply (Var' A) = isSetVar
x +⟨ Var' A ⟩ σ = x +v σ
+id (Var' A) = +vid
+∘ (Var' A) {x = x} = +v∘ {x = x}


embv : {A : Ty} → Natw (Var' A) (Tm' A)
act embv _ = ⌜_⌝v
nat embv = ⌜⌝+v


-- Lifting to weakenings.
Wk' : Con → Pshw
Wk' = listp Var'

embw : {Γ : Con} → Natw (Wk' Γ) (Tms' Γ)
embw = mapnt embv


-- One of the categorical identity laws must be proved manually.
wkwk∘w : {Γ Δ Θ : Con} {A : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ} {x : Var Γ A} →
         (wkwk A σ) ∘w (ν , x) ≡ σ ∘w ν
wkwk∘w {σ = ε} = refl
wkwk∘w {σ = σ , y} = ap (λ x → x , _) wkwk∘w

wk∘↑w : {Γ Δ Θ : Con} {A : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       wkwk A (σ ∘w ν) ≡ (wkwk A σ) ∘w (wk↑ A ν)
wk∘↑w {σ = ε} = refl
wk∘↑w {σ = σ , x} = ap2 _,_ (wk∘↑w {σ = σ}) (+vwk {x = x} ⁻¹)

id∘w : {Γ Δ : Con} {σ : Wk Γ Δ} → idw ∘w σ ≡ σ
id∘w {Δ = ●} {σ = ε} = refl
id∘w {Δ = Δ , A} {σ , x} = ap (λ x → x , _) (wkwk∘w ∙ id∘w)

-- The other one, and associativity, are given by the presheaf lifting.
∘idw : {Γ Δ : Con} {σ : Wk Γ Δ} → σ ∘w idw ≡ σ
∘idw = +id (Wk' _)

∘∘w : {Γ Δ Θ Ψ : Con} {σ : Wk Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
∘∘w = +∘ (Wk' _) ⁻¹
