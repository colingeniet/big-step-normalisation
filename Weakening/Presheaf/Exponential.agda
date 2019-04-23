{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.Exponential where

open import Agda.Primitive
open import Library.Equality
open import Syntax.Types
open import Weakening.Presheaf
open import Weakening.Presheaf.Category
open import Weakening.Presheaf.Cartesian
open import Weakening.Variable


private
  variable
    l m n k : Level
    F : Pshw {l}
    G : Pshw {m}
    H : Pshw {n}
    K : Pshw {k}


-- Exponential in the category of presheaves.
-- Definition
infixr 10 _⇒p_
_⇒p_ : ∀ {l m} → Pshw {l} → Pshw {m} → Pshw
(F ⇒p G) $o Γ = Natw (Wk' Γ ×p F) G
isSetapply (F ⇒p G) = isSetnat
act (θ +⟨ F ⇒p G ⟩ σ) Γ (ν ,, x) = act θ Γ (σ ∘w ν ,, x)
nat (θ +⟨ F ⇒p G ⟩ σ) {σ = ν} {δ ,, x} =
  ap (λ x → act θ _ (x ,, _)) (∘∘w ⁻¹)
  ∙ nat θ {σ = ν} {x = σ ∘w δ ,, x}
+id (F ⇒p G) {x = θ} =
  nat≡ λ {i Γ (σ ,, x) → act θ Γ (id∘w {σ = σ} i ,, x)}
+∘ (F ⇒p G) {x = θ} {σ} {ν} =
  nat≡ λ {i Γ (δ ,, x) → act θ Γ (∘∘w {σ = σ} {ν} {δ} i ,, x)}

-- Adjunction
lamp : Natw (F ×p G) H → Natw F (G ⇒p H)
act (act (lamp {F = F} θ) Δ x) Γ (σ ,, y) = act θ Γ (x +⟨ F ⟩ σ ,, y)
nat (act (lamp {F = F} θ) Δ x) =
  ap (λ x → act θ _ (x ,, _)) (+∘ F)
  ∙ nat θ
nat (lamp {F = F} θ) {σ = σ} {x} =
  nat≡ λ {i Γ (δ ,, y) → act θ Γ (+∘ F {x = x} {σ} {δ} (1- i) ,, y)}

appp : Natw F (G ⇒p H) → Natw (F ×p G) H
act (appp θ) Γ (x ,, y) = act (act θ Γ x) Γ (idw ,, y)
nat (appp {G = G} θ) {Γ} {Δ} {σ} {x ,, y} =
  ap (λ z → act z Γ (idw ,, y +⟨ G ⟩ σ))
      (nat θ {σ = σ} {x})
  ∙ ap (λ ν → act (act θ Δ x) Γ (ν ,, y +⟨ G ⟩ σ))
       (∘idw ∙ id∘w ⁻¹)
  ∙ nat (act θ Δ x) {σ = σ} {idw ,, y}

-- The adjunction is an isomorphism
βp : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw (F ×p G) H} →
     -- Adga does not seem to be able to infer the functors.
     appp {F = F} {G = G} {H = H} (lamp {F = F} {G = G} {H = H} θ) ≡ θ
βp {F = F} {θ = θ} =
  nat≡ λ {i Γ (x ,, y) → act θ Γ (+id F {x = x} i ,, y)}

ηp : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F (G ⇒p H)} →
     lamp {F = F} {G = G} {H = H} (appp {F = F} {G = G} {H = H} θ) ≡ θ
ηp {F = F} {G} {H} {θ} =
  let laθ = lamp {F = F} {G = G} {H = H} (appp {F = F} {G = G} {H = H} θ)
  in nat≡ λ {i Δ x →
             let p : act laθ Δ x ≡ act θ Δ x
                 p = nat≡ λ {i Γ (σ ,, y) →
                              let p : act (act θ Γ (x +⟨ F ⟩ σ)) Γ (idw ,, y)
                                      ≡ act (act θ Δ x) Γ (σ ,, y)
                                  p = ap (λ x → act x Γ (idw ,, y))
                                          (nat θ {σ = σ} {x})
                                      ∙ ap (λ ν → act (act θ Δ x) Γ (ν ,, y)) ∘idw
                              in p i}
             in p i}

-- Naturality of the adjunction
natlam : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {K : Pshw {k}}
         {θ : Natw (F ×p G) H} {α : Natw K F} →
         lamp {F = F} {G = G} {H = H} θ ∘n α ≡
         lamp {F = K} {G = G} {H = H} (θ ∘n (α ∘n (π₁n K G idn) ,n (π₂n K G idn)))
natlam {F = F} {G} {H} {K} {θ} {α} =
  let lθ = lamp {F = F} {G = G} {H = H} θ
      α↑ = α ∘n (π₁n K G idn) ,n (π₂n K G idn)
      lθα↑ = lamp {F = K} {G = G} {H = H} (θ ∘n α↑)
  in nat≡ λ {i Δ x →
              let p : act lθ Δ (act α Δ x)
                      ≡ act lθα↑ Δ x
                  p = nat≡ λ {i Γ (σ ,, y) →
                               let p : act θ Γ ((act α Δ x) +⟨ F ⟩ σ ,, y)
                                       ≡ act θ Γ (act α Γ (x +⟨ K ⟩ σ) ,, y)
                                   p = ap (λ x → act θ Γ (x ,, y)) (nat α ⁻¹)
                               in p i}
              in p i}
