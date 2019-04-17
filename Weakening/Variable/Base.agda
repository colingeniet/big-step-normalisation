{-# OPTIONS --safe --cubical #-}

{-
  Definition of variables and weakenings.
  Weakenings are defined in the very broad sense of lists of variables
  (aka renamings).
  
  Because I'm lazy, presheaves are only defined on the category of weakenings.
  Below are the definitions required to define presheaves in the first place.
  The remaining function/lemmas are in Weakening.Variable
-}

module Weakening.Variable.Base where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.List

-- Definition
data Var : Con → Ty → Set where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

Wk : Con → Con → Set
Wk Γ = list (Var Γ)

infixl 15 _+v_
-- Composition
_+v_ : {Γ Δ : Con} {A : Ty} → Var Δ A → Wk Γ Δ → Var Γ A
z +v (_ , x) = x
(s x) +v (σ , _) = x +v σ

infixr 20 _∘w_
_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ
σ ∘w ν = mapl (λ x → x +v ν) σ


wkwk : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) Δ
wkwk A ε = ε
wkwk A (σ , x) = wkwk A σ , s x

wk↑ : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) (Δ , A)
wk↑ A σ = wkwk A σ , z

idw : {Γ : Con} → Wk Γ Γ
idw {●} = ε
idw {Γ , A} = wk↑ A idw


-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ
⌜_⌝w = mapt ⌜_⌝v

⌜wkwk⌝w : {Γ Δ : Con} {A : Ty} {σ : Wk Γ Δ} →
          ⌜ wkwk A σ ⌝w ≡ ⌜ σ ⌝w ∘ wk
⌜wkwk⌝w {σ = ε} = εη ⁻¹
⌜wkwk⌝w {σ = σ , x} = ap (λ x → x , _) ⌜wkwk⌝w ∙ ,∘ ⁻¹

⌜id⌝w : {Γ : Con} → ⌜ idw {Γ} ⌝w ≡ id
⌜id⌝w {Γ = ●} = εη ⁻¹
⌜id⌝w {Γ = Γ , A} = ap (λ x → x , vz)
                       (⌜wkwk⌝w ∙ ap (λ x → x ∘ wk) ⌜id⌝w)
                    ∙ ↑id

⌜⌝+v : {Γ Δ : Con} {A : Ty} {x : Var Δ A} {σ : Wk Γ Δ} →
       ⌜ x +v σ ⌝v ≡ ⌜ x ⌝v [ ⌜ σ ⌝w ]
⌜⌝+v {x = z} {σ = _ , _} = vz[,] ⁻¹
⌜⌝+v {x = s x} {σ = σ , _} = ⌜⌝+v {x = x} {σ = σ}
                             ∙ ap (λ x → _ [ x ]) (wk, ⁻¹) ∙ [][]

⌜∘⌝w : {Γ Δ Θ : Con} {σ : Wk Δ Θ} {ν : Wk Γ Δ} → 
       ⌜ σ ∘w ν ⌝w ≡ ⌜ σ ⌝w ∘ ⌜ ν ⌝w
⌜∘⌝w {σ = ε} = εη ⁻¹
⌜∘⌝w {σ = σ , x} = ap2 _,_ ⌜∘⌝w ⌜⌝+v ∙ ,∘ ⁻¹
