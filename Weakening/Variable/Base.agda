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
z +v (_ ,, x) = x
(s x) +v (σ ,, _) = x +v σ

infixr 20 _∘w_
_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ
σ ∘w ν = mapl (λ x → x +v ν) σ


wkwk : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) Δ
wkwk {Δ = ●} A _ = tt
wkwk {Δ = Δ , B} A (σ ,, x) = wkwk A σ ,, s x

wk↑ : {Γ Δ : Con} (A : Ty) → Wk Γ Δ → Wk (Γ , A) (Δ , A)
wk↑ A σ = wkwk A σ ,, z

idw : {Γ : Con} → Wk Γ Γ
idw {●} = tt
idw {Γ , A} = wk↑ A idw


-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ
⌜_⌝w = mapt ⌜_⌝v

-- Embedding equations.
⌜wkwk⌝w : {Γ Δ : Con} {A : Ty} {σ : Wk Γ Δ} →
          ⌜ wkwk A σ ⌝w ≡ ⌜ σ ⌝w ∘ wk
⌜wkwk⌝w {Δ = ●} =
  ε          ≡⟨ εη ⁻¹ ⟩
  ⌜ tt ⌝w ∘ wk ∎
⌜wkwk⌝w {Δ = Δ , B} {A = A} {σ = σ ,, x} =
  ⌜ wkwk A σ ⌝w , ⌜ x ⌝v [ wk ] ≡⟨ ap (λ x → x , _) ⌜wkwk⌝w ⟩
  ⌜ σ ⌝w ∘ wk , ⌜ x ⌝v [ wk ]   ≡⟨ ,∘ ⁻¹ ⟩
  (⌜ σ ⌝w , ⌜ x ⌝v) ∘ wk        ∎

⌜id⌝w : {Γ : Con} → ⌜ idw {Γ} ⌝w ≡ id
⌜id⌝w {Γ = ●} =
  ε  ≡⟨ εη ⁻¹ ⟩
  id ∎
⌜id⌝w {Γ = Γ , A} =
  ⌜ wkwk A idw ⌝w , vz ≡⟨ ap (λ x → x , vz) ⌜wkwk⌝w ⟩
  ⌜ idw ⌝w ∘ wk , vz   ≡⟨ ap (λ σ → σ ↑ A) ⌜id⌝w ⟩
  (id ↑ A)             ≡⟨ ↑id ⟩
  id                   ∎

⌜⌝+v : {Γ Δ : Con} {A : Ty} {x : Var Δ A} {σ : Wk Γ Δ} →
       ⌜ x +v σ ⌝v ≡ ⌜ x ⌝v [ ⌜ σ ⌝w ]
⌜⌝+v {x = z} {σ = σ ,, y} =
  ⌜ y ⌝v                ≡⟨ vz[,] ⁻¹ ⟩
  vz [ ⌜ σ ⌝w , ⌜ y ⌝v ] ∎
⌜⌝+v {A = A} {x = s x} {σ = σ ,, y} =
  ⌜ x +v σ ⌝v                     ≡⟨ ⌜⌝+v ⟩
  ⌜ x ⌝v [ ⌜ σ ⌝w ]                ≡⟨ ap (λ x → _ [ x ]) wk, ⁻¹ ⟩
  ⌜ x ⌝v [ wk ∘ (⌜ σ ⌝w , ⌜ y ⌝v) ] ≡⟨ [][] ⟩
  ⌜ x ⌝v [ wk ] [ ⌜ σ ⌝w , ⌜ y ⌝v ] ∎

⌜∘⌝w : {Γ Δ Θ : Con} {σ : Wk Δ Θ} {ν : Wk Γ Δ} → 
       ⌜ σ ∘w ν ⌝w ≡ ⌜ σ ⌝w ∘ ⌜ ν ⌝w
⌜∘⌝w {Θ = ●} {ν = ν} =
  ε              ≡⟨ εη ⁻¹ ⟩
  ⌜ tt ⌝w ∘ ⌜ ν ⌝w ∎
⌜∘⌝w {Θ = Θ , A} {σ = σ ,, x} {ν} =
  ⌜ σ ∘w ν ⌝w , ⌜ x +v ν ⌝v          ≡⟨ ap2 _,_ ⌜∘⌝w ⌜⌝+v ⟩
  ⌜ σ ⌝w ∘ ⌜ ν ⌝w , ⌜ x ⌝v [ ⌜ ν ⌝w ] ≡⟨ ,∘ ⁻¹ ⟩
  (⌜ σ ⌝w , ⌜ x ⌝v) ∘ ⌜ ν ⌝w          ∎
