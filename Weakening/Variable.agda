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
open import Syntax.TermLike

-- Definition
data Var : Con → Ty → Set where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

Wk : Con → Con → Set
Wk = list Var

infixl 15 _+v_
-- Composition
_+v_ : {Γ Δ : Con} {A : Ty} → Var Δ A → Wk Γ Δ → Var Γ A
z +v (_ , x) = x
(s x) +v (σ , _) = x +v σ

infixr 20 _∘w_
_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ
ε ∘w σ = ε
(σ , x) ∘w ν = σ ∘w ν , x +v ν


wkwk : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) Δ
wkwk A ε = ε
wkwk A (σ , x) = wkwk A σ , s x

idw : {Γ : Con} → Wk Γ Γ
idw {●} = ε
idw {Γ , A} = wkwk A idw , z


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


∘idw : {Γ Δ : Con} {σ : Wk Γ Δ} → σ ∘w idw ≡ σ
∘idw {σ = ε} = refl
∘idw {σ = σ , x} = ap2 _,_ ∘idw +vid

wkwk∘w : {Γ Δ Θ : Con} {A : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ} {x : Var Γ A} →
         (wkwk A σ) ∘w (ν , x) ≡ σ ∘w ν
wkwk∘w {σ = ε} = refl
wkwk∘w {σ = σ , y} = ap (λ x → x , _) wkwk∘w

id∘w : {Γ Δ : Con} {σ : Wk Γ Δ} → idw ∘w σ ≡ σ
id∘w {Δ = ●} {σ = ε} = refl
id∘w {Δ = Δ , A} {σ , x} = ap (λ x → x , _) (wkwk∘w ∙ id∘w)

∘∘w : {Γ Δ Θ Ψ : Con} {σ : Wk Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
      (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
∘∘w {σ = ε} = refl
∘∘w {σ = σ , x} = ap2 _,_ (∘∘w {σ = σ}) (+v∘ {x = x} ⁻¹)


-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ
⌜ ε ⌝w = ε
⌜ σ , x ⌝w = ⌜ σ ⌝w , ⌜ x ⌝v


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
