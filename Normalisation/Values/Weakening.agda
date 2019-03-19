{-# OPTIONS --safe --cubical #-}

module Normalisation.Values.Weakening where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Normalisation.TermLike
open import Normalisation.Variables.Weakening
open import Normalisation.Values


_+V_ : {Γ Δ : Con} {A : Ty} → Val Δ A → Wk Γ Δ → Val Γ A
_+NV_ : {Γ Δ : Con} {A : Ty} → Ne Val Δ A → Wk Γ Δ → Ne Val Γ A
_+E_ : {Γ Δ Θ : Con} → Env Δ Θ → Wk Γ Δ → Env Γ Θ

⌜⌝+V : {Γ Δ : Con} {A : Ty} {v : Val Δ A} {σ : Wk Γ Δ} →
       ⌜ v +V σ ⌝V ≡ ⌜ v ⌝V +t σ
⌜⌝+NV : {Γ Δ : Con} {A : Ty} {v : Ne Val Δ A} {σ : Wk Γ Δ} →
       ⌜ v +NV σ ⌝NV ≡ ⌜ v ⌝NV +t σ
⌜⌝+E : {Γ Δ Θ : Con} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
       ⌜ ρ +E σ ⌝E ≡ ⌜ ρ ⌝E +s σ


(lam u ρ) +V σ = lam u (ρ +E σ)
(neu v) +V σ = neu (v +NV σ)
(veq {u = u} {v} p i) +V σ = veq {u = u +V σ} {v +V σ}
                                 (⌜⌝+V {v = u}
                                 ∙ ap (λ x → x +t σ) p
                                 ∙ ⌜⌝+V {v = v} ⁻¹) i
(isSetVal p q i j) +V σ = isSetVal (λ k → p k +V σ) (λ k → q k +V σ) i j
(var x) +NV σ = var (x +v σ)
(app f v) +NV σ = app (f +NV σ) (v +V σ)
ε +E σ = ε
(ρ , v) +E σ = ρ +E σ , v +V σ

⌜⌝+V {v = lam u ρ} = ap (λ σ → lam u [ σ ]) ⌜⌝+E ∙ [][]
⌜⌝+V {v = neu v} = ⌜⌝+NV {v = v}
⌜⌝+V {v = veq {u = u} {v} p j} {σ} i =
  let IHu = ⌜⌝+V {v = u} {σ}
      IHv = ⌜⌝+V {v = v} {σ}
      -- This is just  (veq p) +V σ
      -- but the termination checker wants it expanded.
      r = λ j → ⌜ veq {u = u +V σ} {v +V σ}
                      (⌜⌝+V {v = u}
                      ∙ ap (λ x → x +t σ) p
                      ∙ ⌜⌝+V {v = v} ⁻¹) j ⌝V
      s = λ j → ⌜ veq {u = u} {v} p j ⌝V +t σ
  in ouc (isSetFillSquare isSetTm r s IHu IHv i j)
⌜⌝+V {v = isSetVal {x = u} {v} p q i j} {σ} k =
  ouc (isSetPartial isSetTm
                    (λ j → ⌜⌝+V {v = p j} {σ} k)
                    (λ j → ⌜⌝+V {v = q j} {σ} k)
                    (λ {(k = i0) → λ i j →
                        ⌜ isSetVal (λ j → p j +V σ) (λ j → q j +V σ) i j ⌝V;
                        (k = i1) → λ i j →
                        ⌜ isSetVal p q i j ⌝V +t σ}))
      i j

⌜⌝+NV {v = var x} = ⌜⌝+v
⌜⌝+NV {v = app f v} = ap2 _$_ (⌜⌝+NV {v = f}) (⌜⌝+V {v = v}) ∙ $[] ⁻¹
⌜⌝+E {ρ = ε} = εη ⁻¹
⌜⌝+E {ρ = ρ , v} = ap2 _,_ (⌜⌝+E {ρ = ρ}) (⌜⌝+V {v = v}) ∙ ,∘ ⁻¹



+Vid : {Γ : Con} {A : Ty} {v : Val Γ A} → v +V idw ≡ v
+NVid : {Γ : Con} {A : Ty} {v : Ne Val Γ A} → v +NV idw ≡ v
+Eid : {Γ Δ : Con} {ρ : Env Γ Δ} → ρ +E idw ≡ ρ

+Vid {v = lam u ρ} = ap (lam u) +Eid
+Vid {v = neu v} = ap neu +NVid
+Vid {v = veq {u = u} {v} p j} i =
  let IHu = +Vid {v = u}
      IHv = +Vid {v = v}
      r = λ j → (veq {u = u} {v} p j) +V idw
      s = veq {u = u} {v} p
  in ouc (isSetFillSquare isSetVal r s IHu IHv i j)
+Vid {v = isSetVal {x = u} {v} p q i j} k =
  ouc (isSetPartial isSetVal
                    (λ j → +Vid {v = p j} k)
                    (λ j → +Vid {v = q j} k)
                    (λ {(k = i0) → λ i j →
                        (isSetVal p q i j) +V idw;
                        (k = i1) → isSetVal p q}))
      i j
+NVid {v = var x} = ap var +vid
+NVid {v = app f v} = ap2 app +NVid +Vid
+Eid {ρ = ε} = refl
+Eid {ρ = ρ , v} = ap2 _,_ +Eid +Vid


+V∘ : {Γ Δ Θ : Con} {A : Ty} {v : Val Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      v +V (σ ∘w ν) ≡ (v +V σ) +V ν
+NV∘ : {Γ Δ Θ : Con} {A : Ty} {v : Ne Val Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       v +NV (σ ∘w ν) ≡ (v +NV σ) +NV ν
+E∘ : {Γ Δ Θ Ψ : Con} {ρ : Env Θ Ψ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      ρ +E (σ ∘w ν) ≡ (ρ +E σ) +E ν

+V∘ {v = lam u ρ} = ap (lam u) +E∘
+V∘ {v = neu v} = ap neu +NV∘
+V∘ {v = veq {u = u} {v} p j} {σ} {ν} i =
  let IHu = +V∘ {v = u} {σ} {ν}
      IHv = +V∘ {v = v} {σ} {ν}
      r = λ j → (veq {u = u} {v} p j) +V (σ ∘w ν)
      s = λ j → ((veq {u = u} {v} p j) +V σ) +V ν
  in ouc (isSetFillSquare isSetVal r s IHu IHv i j)
+V∘ {v = isSetVal {x = u} {v} p q i j} {σ} {ν} k =
  ouc (isSetPartial isSetVal
                    (λ j → +V∘ {v = p j} {σ} {ν} k)
                    (λ j → +V∘ {v = q j} {σ} {ν} k)
                    (λ {(k = i0) → λ i j →
                        (isSetVal p q i j) +V (σ ∘w ν);
                        (k = i1) → λ i j →
                        ((isSetVal p q i j) +V σ) +V ν}))
      i j
+NV∘ {v = var x} = ap var +v∘
+NV∘ {v = app f v} {σ} {ν} = ap2 app (+NV∘ {v = f}) (+V∘ {v = v})
+E∘ {ρ = ε} = refl
+E∘ {ρ = ρ , v} = ap2 _,_ (+E∘ {ρ = ρ}) (+V∘ {v = v})
