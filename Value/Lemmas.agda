{-# OPTIONS --safe --cubical #-}

module Value.Lemmas where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Variable.Variable
open import Syntax.Lemmas
open import Syntax.Weakening
open import Value.Value
open import Value.Weakening

-- Projection for lists.
π₁E : {Γ Δ : Con} {A : Ty Δ} → Env Γ (Δ , A) → Env Γ Δ
π₁E (ρ , _) = ρ
π₂E : {Γ Δ : Con} {A : Ty Δ} → (ρ : Env Γ (Δ , A)) → Val Γ (A [ ⌜ π₁E ρ ⌝E ]T)
π₂E (_ , v) = v

πηE : {Γ Δ : Con} {A : Ty Δ} {ρ : Env Γ (Δ , A)} → (π₁E ρ , π₂E ρ) ≡ ρ
πηE {ρ = _ , _} = refl

envεη : {Γ : Con} (σ : Env Γ ●) → σ ≡ ε
envεη ε = refl

abstract
  -- Embedding and projections commute.
  π₁E≡ : {Γ Δ : Con} {A : Ty Δ} {ρ : Env Γ (Δ , A)} → ⌜ π₁E ρ ⌝E ≡ π₁ ⌜ ρ ⌝E
  π₁E≡ {ρ = ρ , v} =
    ⌜ ρ ⌝E              ≡⟨ π₁β ⁻¹ ⟩
    π₁ (⌜ ρ ⌝E , ⌜ v ⌝V) ∎
  π₂E≡ : {Γ Δ : Con} {A : Ty Δ} {ρ : Env Γ (Δ , A)} →
         ⌜ π₂E ρ ⌝V ≅[ Tm Γ ] π₂ ⌜ ρ ⌝E
  π₂E≡ {ρ = ρ , v} =
    ⌜ v ⌝V              ≅⟨ π₂β ≅⁻¹ ⟩'
    π₂ (⌜ ρ ⌝E , ⌜ v ⌝V) ≅∎

  -- Weakening and projections commute.
  π₁+ : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
        π₁E (ρ +E σ) ≡ (π₁E ρ) +E σ
  π₁+ {ρ = _ , _} = refl
  π₂+ : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ (Θ , A)} {σ : Wk Γ Δ} →
        π₂E (ρ +E σ) ≅[ Val Γ ] (π₂E ρ) +V σ
  π₂+ {Γ} {ρ = _ , x} {σ} =
    tr (Val Γ) _ (x +V σ)
      ≅⟨ trfill (Val Γ) _ (x +V σ) ⁻¹ ⟩
    x +V σ ≅∎


-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv≡ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≡ id

private
  abstract
    ⌜id+Ewk⌝ : {Γ : Con} {A : Ty Γ} → ⌜ idenv {Γ} +E wkw {A = A} idw ⌝E ≡ wk
    ⌜id+Ewk⌝ {Γ} {A} =
      ⌜ idenv {Γ} +E wkw {A = A} idw ⌝E ≡⟨ ⌜⌝+E ⟩
      ⌜ idenv ⌝E +s wkw idw             ≡⟨ ap (_+s wkw idw) idenv≡ ⟩
      id ∘ ⌜ wkw idw ⌝w                 ≡⟨ id∘ ⟩
      ⌜ wkw idw ⌝w                      ≡⟨ ⌜wkid⌝ ⟩
      wk                               ∎

    [⌜id+E⌝] : {Γ : Con} {A : Ty Γ} → A [ wk ]T ≡ A [ ⌜ idenv {Γ} +E wkw {A = A} idw ⌝E ]T
    [⌜id+E⌝] {A = A} = ap (A [_]T) ⌜id+Ewk⌝ ⁻¹


idenv {●} = ε
idenv {Γ , A} =
  idenv +E (wkw idw) , tr (Val _) [⌜id+E⌝] (neu (var z))

abstract
  idenv≡ {●} =
    ε ≡⟨ εη ⁻¹ ⟩
    id ∎
  idenv≡ {Γ , A} =
    let p : ⌜ idenv +E wkw idw ⌝E ≡ wk
        p = ⌜id+Ewk⌝
        q : ⌜ tr (Val _) [⌜id+E⌝] (neu (var z)) ⌝V ≅[ Tm (Γ , A) ] vz
        q = ⌜ tr (Val _) [⌜id+E⌝] (neu (var z)) ⌝V
              ≅⟨ apd ⌜_⌝V (trfill (Val _) [⌜id+E⌝] (neu (var z)) ⁻¹) ⟩
            vz ≅∎
    in ≅-to-≡ {B = Tms (Γ , A)} isSetCon (
      ⌜ idenv +E wkw idw ⌝E , ⌜ tr (Val _) [⌜id+E⌝] (neu (var z)) ⌝V
        ≅⟨ (λ i → p i , ≅-to-≡[] isSetTy q {P = ap (A [_]T) p} i) ⟩
      wk , vz
        ≅⟨ πη ⟩
      id ≅∎)


  -- Dependent version of the value quotient constructor.
  veqdep : {Γ : Con} {A B : Ty Γ} {u : Val Γ A} {v : Val Γ B} →
           {P : A ≡ B} → ⌜ u ⌝V ≡[ ap (Tm Γ) P ]≡ ⌜ v ⌝V → u ≡[ ap (Val Γ) P ]≡ v
  veqdep {Γ} {u = u} {v} {P} p =
    let u' = tr (Val Γ) P u
        u≡u' : u ≡[ ap (Val Γ) P ]≡ u'
        u≡u' = trfill (Val Γ) P u
        p : ⌜ u' ⌝V ≅[ Tm Γ ] ⌜ v ⌝V
        p = ⌜ u' ⌝V ≅⟨ apd ⌜_⌝V u≡u' ⁻¹ ⟩
            ⌜ u ⌝V  ≅⟨ p ⟩
            ⌜ v ⌝V  ≅∎
        u'≡v : u' ≡ v
        u'≡v = veq (≅-to-≡ isSetTy p)
    in u≡u' d∙ u'≡v

  -- Since embedding of values is (by definition) injective,
  -- so is the embedding of environments.
  enveq : {Γ Δ : Con} {σ ν : Env Γ Δ} → ⌜ σ ⌝E ≡ ⌜ ν ⌝E → σ ≡ ν
  enveq {Δ = ●} {ε} {ε} _ = refl
  enveq {Γ} {Δ , A} {σ , u} {ν , v} p =
    let p1 : σ ≡ ν
        p1 = enveq (⌜ σ ⌝E       ≡⟨ π₁β ⁻¹ ⟩
                    π₁ ⌜ σ , u ⌝E ≡⟨ ap π₁ p ⟩
                    π₁ ⌜ ν , v ⌝E ≡⟨ π₁β ⟩
                    ⌜ ν ⌝E ∎)
        q : ⌜ u ⌝V ≅[ Tm Γ ] ⌜ v ⌝V
        q = ⌜ u ⌝V        ≅⟨ π₂β ≅⁻¹ ⟩'
            π₂ ⌜ σ , u ⌝E ≅⟨ apd π₂ p ⟩
            π₂ ⌜ ν , v ⌝E ≅⟨ π₂β ⟩'
            ⌜ v ⌝V        ≅∎
        p2 : u ≡[ ap (λ x → Val Γ (A [ ⌜ x ⌝E ]T)) p1 ]≡ v
        p2 = veqdep (≅-to-≡[] isSetTy q {P = ap (λ x → A [ ⌜ x ⌝E ]T) p1})
    in λ i → p1 i , p2 i
