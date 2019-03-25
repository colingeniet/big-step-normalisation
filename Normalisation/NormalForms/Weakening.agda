{-# OPTIONS --safe --cubical #-}

module Normalisation.NormalForms.Weakening where

open import Library.Equality
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Terms.Lemmas
open import Syntax.Terms.Weakening
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.NormalForms


_+N_ : {Γ Δ : Con} {A : Ty} → Nf Δ A → Wk Γ Δ → Nf Γ A
_+Ne_ : {Γ Δ : Con} {A : Ty} → Ne Δ A → Wk Γ Δ → Ne Γ A
_+Sp_ : {Γ Δ : Con} {A B : Ty} → Sp Δ A B → Wk Γ Δ → Sp Γ A B

(lam n) +N σ = lam (n +N (keep _ σ))
(neu n) +N σ = neu (n +Ne σ)
(x # ns) +Ne σ = (x +v σ) # (ns +Sp σ)
nil +Sp σ = nil
(n ∷ ns) +Sp σ = (n +N σ) ∷ (ns +Sp σ)


+Nid : {Γ : Con} {A : Ty} {n : Nf Γ A} → n +N idw ≡ n
+Neid : {Γ : Con} {A : Ty} {n : Ne Γ A} → n +Ne idw ≡ n
+Spid : {Γ : Con} {A B : Ty} {ns : Sp Γ A B} → ns +Sp idw ≡ ns
+Nid {n = lam n} = ap lam +Nid
+Nid {n = neu n} = ap neu +Neid
+Neid {n = x # ns} = ap2 _#_ +vid +Spid
+Spid {ns = nil} = refl
+Spid {ns = n ∷ ns} = ap2 _∷_ +Nid +Spid


+N∘ : {Γ Δ Θ : Con} {A : Ty} {n : Nf Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      n +N (σ ∘w ν) ≡ (n +N σ) +N ν
+Ne∘ : {Γ Δ Θ : Con} {A : Ty} {n : Ne Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       n +Ne (σ ∘w ν) ≡ (n +Ne σ) +Ne ν
+Sp∘ : {Γ Δ Θ : Con} {A B : Ty} {ns : Sp Θ A B} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      ns +Sp (σ ∘w ν) ≡ (ns +Sp σ) +Sp ν
+N∘ {n = lam n} = ap lam +N∘
+N∘ {n = neu n} = ap neu +Ne∘
+Ne∘ {n = x # ns} = ap2 _#_ +v∘ +Sp∘
+Sp∘ {ns = nil} = refl
+Sp∘ {ns = n ∷ ns} = ap2 _∷_ +N∘ +Sp∘


⌜⌝+N : {Γ Δ : Con} {A : Ty} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≡ ⌜ n ⌝N +t σ
⌜⌝+Ne : {Γ Δ : Con} {A : Ty} {n : Ne Δ A} {σ : Wk Γ Δ} →
        ⌜ n +Ne σ ⌝Ne ≡ ⌜ n ⌝Ne +t σ
⌜⌝+Sp : {Γ Δ : Con} {A B : Ty} {u : Tm Δ A} {ns : Sp Δ A B} {σ : Wk Γ Δ} →
        (u +t σ) ⌜ ns +Sp σ ⌝Sp ≡ (u ⌜ ns ⌝Sp) +t σ
⌜⌝+N {n = lam n} = ap lam (⌜⌝+N {n = n} {keep _ _}) ∙ lam[] ⁻¹
⌜⌝+N {n = neu n} = ⌜⌝+Ne {n = n}
⌜⌝+Ne {n = x # ns} = ap (λ x → x ⌜ ns +Sp _ ⌝Sp) (⌜⌝+v {x = x})
                       ∙ ⌜⌝+Sp {ns = ns}
⌜⌝+Sp {ns = nil} = refl
⌜⌝+Sp {u = u} {n ∷ ns} {σ} = ap (λ x → x ⌜ ns +Sp σ ⌝Sp)
                                (ap (λ x → (u +t σ) $ x) (⌜⌝+N {n = n}) ∙ $[] ⁻¹)
                             ∙ ⌜⌝+Sp {ns = ns}



_+E_ : {Γ Δ Θ : Con} → Env Δ Θ → Wk Γ Δ → Env Γ Θ
ε +E σ = ε
(ρ , n) +E σ = (ρ +E σ) , (n +N σ)


+Eid : {Γ Δ : Con} {ρ : Env Γ Δ} → ρ +E idw ≡ ρ
+Eid {ρ = ε} = refl
+Eid {ρ = ρ , n} = ap2 _,_ +Eid +Nid

+E∘ : {Γ Δ Θ Ψ : Con} {ρ : Env Θ Ψ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
      ρ +E (σ ∘w ν) ≡ (ρ +E σ) +E ν
+E∘ {ρ = ε} = refl
+E∘ {ρ = ρ , n} = ap2 _,_ +E∘ +N∘


⌜⌝+E : {Γ Δ Θ : Con} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
       ⌜ ρ +E σ ⌝E ≡ ⌜ ρ ⌝E +s σ
⌜⌝+E {ρ = ε} = εη ⁻¹
⌜⌝+E {ρ = ρ , n} = ap2 _,_ (⌜⌝+E {ρ = ρ}) (⌜⌝+N {n = n}) ∙ ,∘ ⁻¹



nenf : {Γ : Con} {A : Ty} → Ne Γ A → Nf Γ A
nenf {A = o} = neu
nenf {A = A ⟶ B} n = lam (nenf (appne (n +Ne (drop A idw))
                                      (nenf (var z))))

_↑env_ : {Γ Δ : Con} → Env Γ Δ → (A : Ty) → Env (Γ , A) (Δ , A)
ρ ↑env A = ρ +E (drop A idw) , nenf (var z)
