{-# OPTIONS --safe --cubical #-}

module Normalisation.Values.Weakening where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Normalisation.TermLike
open import Normalisation.Variables.Weakening
open import Normalisation.Values


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
  let IHu = valgenwk≡ {Δ = Δ} {A = A} {u = u}
      IHv = valgenwk≡ {Δ = Δ} {A = A} {u = v}
      -- This is just  valgenwk Δ (veq p) A
      -- but the termination checker wants me to expand it.
      r = λ j → ⌜ veq {u = valgenwk Δ u A} {valgenwk Δ v A}
                      (valgenwk≡ {u = u}
                      ∙ ap (λ u → tmgenwk Δ u A) p
                      ∙ valgenwk≡ {u = v} ⁻¹) j ⌝V
      s = λ j → tmgenwk Δ (⌜ veq {u = u} {v} p j ⌝V) A
  in ouc (isSetFillSquare isSetTm r s IHu IHv i j)
valgenwk≡ {Γ} {Δ} {A} {B} {u = isSetVal {x = u} {v} p q i j} k =
  let f : Val (Γ ++ Δ) B → Tm ((Γ , A) ++ Δ) B
      f u = ⌜ valgenwk Δ u A ⌝V
      g : Val (Γ ++ Δ) B → Tm ((Γ , A) ++ Δ) B
      g u = tmgenwk Δ (⌜ u ⌝V) A
      IHu : f u ≡ g u
      IHu = valgenwk≡ {u = u}
      IHv : f v ≡ g v
      IHv = valgenwk≡ {u = v}
      IHp : IHu ≡[ ap _ p ]≡ IHv
      IHp j = valgenwk≡ {u = p j}
      IHq : IHu ≡[ ap _ q ]≡ IHv
      IHq j = valgenwk≡ {u = q j}
      fp = ap f p
      fq = ap f q
      fface : fp ≡ fq
      fface i j = f (isSetVal p q i j)
      gp = ap g p
      gq = ap g q
      gface1 : gp ≡ gq
      gface1 = isSetTm gp gq
      gface2 : gp ≡ gq
      gface2 i j = g (isSetVal p q i j)
      α : (i j : I) → fface i j ≡ gface1 i j
      α i j k = isSetTm (λ j → IHp j k) (λ j → IHq j k) i j
      gfill : gface1 ≡ gface2
      gfill = PropisSet isSetTm gface1 gface2
      β : (i j : I) → fface i j ≡ gface2 i j
      β i j = transp (λ k → fface i j ≡ gfill k i j) (i ∨ j ∨ 1- i ∨ 1- j) (α i j)
  in β i j k


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

++V≡ : {Γ Θ : Con} {B : Ty} {u : Val Γ B} → ⌜ u ++V Θ ⌝V ≡ ⌜ u ⌝V ++t Θ
++V≡ {Θ = ●} = refl
++V≡ {Θ = Θ , A} {u = u} = +V≡ {u = u ++V Θ}
                           ∙ ap (λ x → x + A) (++V≡ {Θ = Θ})
++NV≡ : {Γ Θ : Con} {B : Ty} {u : Ne Val Γ B} → ⌜ u ++NV Θ ⌝NV ≡ ⌜ u ⌝NV ++t Θ
++NV≡ {Θ = ●} = refl
++NV≡ {Θ = Θ , A} {u = u} = +NV≡ {u = u ++NV Θ}
                           ∙ ap (λ x → x + A) (++NV≡ {Θ = Θ})
++E≡ : {Γ Δ Θ : Con} {σ : Env Γ Δ} → ⌜ σ ++E Θ ⌝E ≡ ⌜ σ ⌝E ++s Θ
++E≡ {Θ = ●} = refl
++E≡ {Θ = Θ , A} {σ = σ} = +E≡ {σ = σ ++E Θ}
                           ∙ ap (λ σ → σ +s A) (++E≡ {Θ = Θ})
