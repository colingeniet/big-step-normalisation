{-# OPTIONS --cubical #-}

module Normalisation.NormalForms where

open import Equality
open import Syntax
open import Syntax.Equality


-- All predicates on terms have this type, and there are quite a few of them.
Tm-predicate : Set₁
Tm-predicate = {Γ : Con} {A : Ty} → Tm Γ A → Set
Tms-predicate : Set₁
Tms-predicate = {Γ Δ : Con} → Tms Γ Δ → Set

-- Lift a predicate on terms to substitutions
infix 60 list
infixr 10 _,_
data list (P : Tm-predicate) : Tms-predicate where
  ε : {Γ : Con} → list P (ε {Γ})
  _,_ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → list P σ → P u → list P (σ , u)

π₁list : {P : Tm-predicate} {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} → list P σ → list P (π₁ σ)
π₁list {P = P} (σ , _) = tr (list P) (π₁β ⁻¹) σ
π₂list : {P : Tm-predicate} {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} → list P σ → P (π₂ σ)
π₂list {P = P} (_ , u) = tr P (π₂β ⁻¹) u

-- Variables.
data Var : Tm-predicate where
  z : {Γ : Con} {A : Ty} → Var (vz {Γ = Γ} {A = A})
  s : {Γ : Con} {A B : Ty} {u : Tm Γ A} → Var u → Var (vs {B = B} u)

-- Neutral forms : a variable applied to terms satisfying P.
-- This is used both for values and normal forms, so here is a generic definition.
data Ne (P : Tm-predicate) : Tm-predicate where
  var : {Γ : Con} {A : Ty} {u : Tm Γ A} → Var u → Ne P u
  app : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} {u : Tm Γ A} → Ne P f → P u → Ne P (f $ u)


data Val : Tm-predicate

Env : Tms-predicate
Env = list Val

data Val where
  vlam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) {ρ : Tms Γ Δ} (envρ : Env ρ) → Val ((lam u) [ ρ ])
  vneu : {Γ : Con} {A : Ty} {u : Tm Γ A} → Ne Val u → Val u

data Nf : Tm-predicate where
  nlam : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} → Nf u → Nf (lam u)
  nneu : {Γ : Con} {u : Tm Γ o} → Ne Nf u → Nf u
  
Nfs : Tms-predicate
Nfs = list Nf


-- Weakening for values / environments.
_+V_ : {Γ : Con} {B : Ty} {u : Tm Γ B} → Val u → (A : Ty) → Val (u + A)
_+NV_ : {Γ : Con} {B : Ty} {u : Tm Γ B} → Ne Val u → (A : Ty) → Ne Val (u + A)
_+E_ : {Γ Δ : Con} {σ : Tms Γ Δ} → Env σ → (A : Ty) → Env (σ +s A)
(vlam u ρ) +V A = tr Val [][] (vlam u (ρ +E A))
(vneu u) +V A = vneu (u +NV A)
(var x) +NV A   = var (s x)
(app f u) +NV A = tr (Ne Val) ($[] ⁻¹) (Ne.app (f +NV A) (u +V A))
ε +E A       = tr Env (εη ⁻¹) ε
(σ , u) +E A = tr Env (,∘ ⁻¹) (σ +E A , u +V A)


-- Weakening of variables below a context.
varlift : {Γ : Con} (Δ : Con) {B : Ty} {u : Tm (Γ ++ Δ) B} → Var u → (A : Ty) →
          Var (u [ (wk {A = A}) ↑↑ Δ ])
varlift ● u A = s u
varlift (Δ , C) z A = tr Var (vz[,] ⁻¹) z
varlift (Δ , C) (s {u = u} varu) A = tr Var
                                        ([][] ⁻¹ ∙ ap (λ σ → u [ σ ]) wk, ⁻¹ ∙ [][])
                                        (s (varlift Δ varu A))

-- Weakening for normal forms must be done at an arbitrary position in the context
-- for the induction.
nfgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Tm (Γ ++ Δ) B} →
          Nf u → (A : Ty) → Nf (u [ (wk {A = A}) ↑↑ Δ ])
nefgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Tm (Γ ++ Δ) B} →
           Ne Nf u → (A : Ty) → Ne Nf (u [ (wk {A = A}) ↑↑ Δ ])
nfgenwk {B = B ⟶ C} Δ (nlam u) A = tr Nf (lam[] ⁻¹) (nlam (nfgenwk (Δ , B) u A)) 
nfgenwk Δ (nneu u) A = nneu (nefgenwk Δ u A)
nefgenwk Δ (var x) A = var (varlift Δ x A)
nefgenwk Δ (app f u) A = tr (Ne Nf) ($[] ⁻¹) (Ne.app (nefgenwk Δ f A) (nfgenwk Δ u A))

_+N_ : {Γ : Con} {B : Ty} {u : Tm Γ B} → Nf u → (A : Ty) → Nf (u + A)
_+NN_ : {Γ : Con} {B : Ty} {u : Tm Γ B} → Ne Nf u → (A : Ty) → Ne Nf (u + A)
u +N A = nfgenwk ● u A
u +NN A = nefgenwk ● u A

-- Weakenings by context extension.
_++V_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Val u → (Δ : Con) → Val (u ++t Δ)
u ++V ● = u
u ++V (Δ , A) = (u ++V Δ) +V A
_++E_ : {Γ Δ : Con} {σ : Tms Γ Δ} → Env σ → (Θ : Con) → Env (σ ++s Θ)
σ ++E ● = σ
σ ++E (Δ , A) = (σ ++E Δ) +E A
_++NV_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Ne Val u → (Δ : Con) → Ne Val (u ++t Δ)
u ++NV ● = u
u ++NV (Δ , A) = (u ++NV Δ) +NV A
_++N_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Nf u → (Δ : Con) → Nf (u ++t Δ)
u ++N ● = u
u ++N (Δ , A) = (u ++N Δ) +N A
_++NN_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Ne Nf u → (Δ : Con) → Ne Nf (u ++t Δ)
u ++NN ● = u
u ++NN (Δ , A) = (u ++NN Δ) +NN A


postulate
  []++V : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {envρ : Env ρ} →
          vlam u (envρ ++E Θ) ≡[ ap Val []++ ]≡ (vlam u envρ) ++V Θ
{-
[]++V {Θ = ●} = refl
[]++V {Θ = Θ , C} {u = u} {ρ = ρ} {envρ = envρ} =
  {!
  trfill Val [][] (vlam u ((envρ ++E Θ) +E C))
  d∙ apd (λ v → v +V C) ([]++V {Θ = Θ} {u = u} {envρ = envρ})!}
-}

-- The identity is an environment.
idenv : {Γ : Con} → Env (id {Γ})
idenv {●} = tr Env (εη ⁻¹) ε
idenv {Γ , A} = tr Env πη (tr Env id∘ (idenv +E A) , vneu (var z))
