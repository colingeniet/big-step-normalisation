{-# OPTIONS --cubical --allow-unsolved-meta #-}

{-
  Definition of values and environments.
-}

module Normalisation.Values where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Normalisation.NeutralForms public


-- Values and environments (list of values) are mutually defined.
data Val : Tm-like

Env : Tms-like
Env = list Val

⌜_⌝V : {Γ : Con} {A : Ty} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty} → Ne Val Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ

-- A value is a λ-closure or a neutral value.
data Val where
  lam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ (A ⟶ B)
  neu : {Γ : Con} {A : Ty} → Ne Val Γ A → Val Γ A
  veq : {Γ : Con} {A : Ty} {u v : Val Γ A} → ⌜ u ⌝V ≡ ⌜ v ⌝V → u ≡ v
  isSetVal : {Γ : Con} {A : Ty} → isSet (Val Γ A)

-- Embeddings.
⌜ lam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ neu n ⌝V = ⌜ n ⌝NV
⌜ veq p i ⌝V = p i
⌜ isSetVal p q i j ⌝V = isSetTm (λ k → ⌜ p k ⌝V) (λ k → ⌜ q k ⌝V) i j
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V



-- Weakening.
valgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Val (Γ ++ Δ) B →
           (A : Ty) → Val ((Γ , A) ++ Δ) B
nvgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Val (Γ ++ Δ) B →
          (A : Ty) → Ne Val ((Γ , A) ++ Δ) B
envgenwk : {Γ Θ : Con} (Δ : Con) → Env (Γ ++ Δ) Θ →
           (A : Ty) → Env ((Γ , A) ++ Δ) Θ

-- Weakening must be proved together with the fact that it commutes with
-- embedding for the veq constructor.
valgenwk≡ : {Γ Δ : Con} {A B : Ty} {u : Val (Γ ++ Δ) B} →
            ⌜ valgenwk Δ u A ⌝V ≡ tmgenwk Δ (⌜ u ⌝V) A
nvgenwk≡ : {Γ Δ : Con} {A B : Ty} {u : Ne Val (Γ ++ Δ) B} →
            ⌜ nvgenwk Δ u A ⌝NV ≡ tmgenwk Δ (⌜ u ⌝NV) A
envgenwk≡ : {Γ Δ Θ : Con} {A : Ty} {σ : Env (Γ ++ Δ) Θ} →
            ⌜ envgenwk Δ σ A ⌝E ≡ tmsgenwk Δ (⌜ σ ⌝E) A


valgenwk Δ (lam u ρ) A = lam u (envgenwk Δ ρ A)
valgenwk Δ (neu u) A   = neu (nvgenwk Δ u A)
valgenwk Δ (veq {u = u} {v} p i) A = veq {u = valgenwk Δ u A} {valgenwk Δ v A}
                                         (valgenwk≡ {u = u}
                                         ∙ ap (λ u → tmgenwk Δ u A) p
                                         ∙ valgenwk≡ {u = v} ⁻¹) i
valgenwk Δ (isSetVal p q i j) A = isSetVal (λ k → valgenwk Δ (p k) A)
                                           (λ k → valgenwk Δ (q k) A)
                                           i j
nvgenwk Δ (var x) A   = var (varwk Δ x A)
nvgenwk Δ (app f u) A = app (nvgenwk Δ f A) (valgenwk Δ u A)
envgenwk Δ ε A       = ε
envgenwk Δ (σ , u) A = envgenwk Δ σ A , valgenwk Δ u A

valgenwk≡ {u = lam u ρ} = ap (λ σ → _ [ σ ]) envgenwk≡ ∙ [][]
valgenwk≡ {u = neu n} = nvgenwk≡ {u = n}
valgenwk≡ {Δ = Δ} {A = A} {u = veq {u = u} {v} p j} i =
  let IHu = valgenwk≡ {Δ = Δ} {A = A} {u = u} in
  let IHv = valgenwk≡ {Δ = Δ} {A = A} {u = v} in
  let p+ = ap (λ u → tmgenwk Δ u A) p in
  hcomp (λ k → λ {(i = i0) → transitivity-square IHu (p+ ∙ IHv ⁻¹) j k;
                  (i = i1) → p+ (j ∧ k);
                  (j = i0) → IHu i;
                  (j = i1) → transitivity-square p+ (IHv ⁻¹) k (1- i)})
        (IHu (i ∨ j))
valgenwk≡ {u = isSetVal p q i j} k = {!isSetTm (λ j → valgenwk≡ {u = p j} k) (λ j → valgenwk≡ {u = q j} k) i j!}
nvgenwk≡ {u = var x} = varwk≡
nvgenwk≡ {u = app n u} = ap2 _$_ (nvgenwk≡ {u = n}) (valgenwk≡ {u = u}) ∙ $[] ⁻¹
envgenwk≡ {σ = ε} = εη ⁻¹
envgenwk≡ {σ = σ , u} = ap2 _,_ (envgenwk≡ {σ = σ}) (valgenwk≡ {u = u}) ∙ ,∘ ⁻¹



-- Simple weakening.
_+V_ : {Γ : Con} {B : Ty} → Val Γ B → (A : Ty) → Val (Γ , A) B
u +V A = valgenwk ● u A
_+NV_ : {Γ : Con} {B : Ty} → Ne Val Γ B → (A : Ty) → Ne Val (Γ , A) B
u +NV A = nvgenwk ● u A
_+E_ : {Γ Δ : Con} → Env Γ Δ → (A : Ty) → Env (Γ , A) Δ
σ +E A = envgenwk ● σ A

-- Weakening by a context.
_++V_ : {Γ : Con} {A : Ty} → Val Γ A → (Δ : Con) → Val (Γ ++ Δ) A
u ++V ● = u
u ++V (Δ , A) = (u ++V Δ) +V A
_++E_ : {Γ Δ : Con} → Env Γ Δ → (Θ : Con) → Env (Γ ++ Θ) Δ
σ ++E ● = σ
σ ++E (Δ , A) = (σ ++E Δ) +E A
_++NV_ : {Γ : Con} {A : Ty} → Ne Val Γ A → (Δ : Con) → Ne Val (Γ ++ Δ) A
u ++NV ● = u
u ++NV (Δ , A) = (u ++NV Δ) +NV A

+V≡ : {Γ : Con} {A B : Ty} {u : Val Γ B} → ⌜ u +V A ⌝V ≡ ⌜ u ⌝V + A
+V≡ {u = u} = valgenwk≡ {u = u}
+NV≡ : {Γ : Con} {A B : Ty} {u : Ne Val Γ B} → ⌜ u +NV A ⌝NV ≡ ⌜ u ⌝NV + A
+NV≡ {u = u} = nvgenwk≡ {u = u}
+E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ Δ} → ⌜ σ +E A ⌝E ≡ ⌜ σ ⌝E +s A
+E≡ {σ = σ} = envgenwk≡ {σ = σ}

-- Weakening can be pushed inside a λ-closure.T
[]++V : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} →
        lam u (ρ ++E Θ) ≡ (lam u ρ) ++V Θ
[]++V {Θ = ●} = refl
[]++V {Θ = Θ , C} {u = u} {ρ = ρ} =
  ap (λ u → u +V C) ([]++V {Θ = Θ} {u = u} {ρ = ρ})

-- Embedding and projections commute.
π₁E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₁list σ ⌝E ≡ π₁ ⌜ σ ⌝E
π₁E≡ {σ = _ , _} = π₁β ⁻¹
π₂E≡ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₂list σ ⌝V ≡ π₂ ⌜ σ ⌝E
π₂E≡ {σ = _ , _} = π₂β ⁻¹

-- Weakening and projections commute.
π₁+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₁list (envgenwk Δ σ A) ≡ envgenwk Δ (π₁list σ) A
π₁+ {σ = _ , _} = refl
π₂+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₂list (envgenwk Δ σ A) ≡ valgenwk Δ (π₂list σ) A
π₂+ {σ = _ , _} = refl

-- Weakening and environment extension commute.
,++E : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Γ Δ} {v : Val Γ A} →
       (ρ , v) ++E Θ ≡ (ρ ++E Θ , v ++V Θ)
,++E {Θ = ●} = refl
,++E {Θ = Θ , B} = ap (λ u → u +E B) (,++E {Θ = Θ})

-- Weakening and constructors commute.
++var : {Γ Δ : Con} {A : Ty} {x : Var Γ A} →
        (var x) ++NV Δ ≡ var (x ++v Δ)
++var {Δ = ●} = refl
++var {Δ = Δ , B} {x = x} = ap (λ u → u +NV B) (++var {Δ = Δ} {x = x})

++VNV : {Γ Δ : Con} {A : Ty} {v : Ne Val Γ A} →
        (neu v) ++V Δ ≡ neu (v ++NV Δ)
++VNV {Δ = ●} = refl
++VNV {Δ = Δ , B} {v = v} = ap (λ u → u +V B) (++VNV {Δ = Δ} {v = v})


-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E A , neu (var z)

idenv≡ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≡ id
idenv≡ {●} = εη ⁻¹
idenv≡ {Γ , A} = ap (λ σ → σ , vz)
                    (+E≡ ∙ ap (λ σ → σ ∘ wk) idenv≡)
                 ∙ ↑id
