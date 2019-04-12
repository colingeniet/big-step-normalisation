{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.Category where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Types
open import Weakening.Presheaf
open import Weakening.Variable
open import Weakening.Variable.Presheaf

private
  variable
    l m n k : Level
    F : Pshw {l}
    G : Pshw {m}
    H : Pshw {n}
    K : Pshw {k}

-- Category of presheaves and natural transformations.
-- Morphisms
idn : Natw F F
act idn _ x = x
nat idn = refl

_∘n_ : Natw G H → Natw F G → Natw F H
act (θ ∘n η) Γ x = act θ Γ (act η Γ x)
nat (θ ∘n η) = ap (act θ _) (nat η) ∙ nat θ

-- Laws
id∘n : {θ : Natw F G} → idn ∘n θ ≡ θ
id∘n = nat≡ refl

∘idn : {θ : Natw F G} → θ ∘n idn ≡ θ
∘idn = nat≡ refl

∘∘n : {θ : Natw H K} {η : Natw G H} {α : Natw F G} →
      (θ ∘n η) ∘n α ≡ θ ∘n (η ∘n α)
∘∘n = nat≡ refl


-- Terminal object.
𝟙p : Pshw
𝟙p $o Γ = ⊤
isSetapply 𝟙p = PropisSet isProp⊤
x +⟨ 𝟙p ⟩ σ = x
+id 𝟙p = refl
+∘ 𝟙p = refl

!p : ∀ {l} {F : Pshw {l}} → Natw F 𝟙p
act !p Γ x = tt
nat !p = refl

!pη : ∀ {l} {F : Pshw {l}} {θ : Natw F 𝟙p} → θ ≡ !p
!pη = nat≡ λ i Γ x → tt

-- Products
infixl 10 _×p_
_×p_ : ∀ {l m} → Pshw {l} → Pshw {m} → Pshw
(F ×p G) $o Γ = F $o Γ × G $o Γ
isSetapply (F ×p G) = isSet× (isSetapply F) (isSetapply G)
(x ,, y) +⟨ F ×p G ⟩ σ = x +⟨ F ⟩ σ ,, y +⟨ G ⟩ σ
+id (F ×p G) {x = x ,, y} i = +id F {x = x} i ,, +id G {x = y} i
+∘ (F ×p G) {x = x ,, y} {σ} {ν} i =
  +∘ F {x = x} {σ} {ν} i ,, +∘ G {x = y} {σ} {ν} i

-- Projections
-- Note that the two presheaves whose product is used must can not be
-- inferred in general.
π₁n : {F : Pshw {l}} (G : Pshw {m}) (H : Pshw {n}) → Natw F (G ×p H) → Natw F G
act (π₁n G H θ) Γ x = fst (act θ Γ x)
nat (π₁n G H θ) = ap fst (nat θ)

π₂n : {F : Pshw {l}} (G : Pshw {m}) (H : Pshw {n}) → Natw F (G ×p H) → Natw F H
act (π₂n G H θ) Γ x = snd (act θ Γ x)
nat (π₂n G H θ) = ap snd (nat θ)

<_,_> : Natw F G → Natw F H → Natw F (G ×p H)
act < θ , η > Γ x = act θ Γ x ,, act η Γ x
nat < θ , η > = ap2 _,,_ (nat θ) (nat η)

-- Laws
π₁nβ : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F G} {η : Natw F H} →
       π₁n G H < θ , η > ≡ θ
π₁nβ = nat≡ refl

π₂nβ : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F G} {η : Natw F H} →
       π₂n G H < θ , η > ≡ η
π₂nβ = nat≡ refl

πnη : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F (G ×p H)} →
      < π₁n G H θ , π₂n G H θ > ≡ θ
πnη {θ = θ} = nat≡ (λ i Γ x → act θ Γ x)

,∘n : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {K : Pshw {k}}
      {θ : Natw F G} {η : Natw F H} {α : Natw K F} →
      < θ , η > ∘n α ≡ < θ ∘n α , η ∘n α >
,∘n = nat≡ refl


-- Exponential
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
         {θ : Natw (F ×p G) H} {η : Natw K F} →
         lamp {F = F} {G = G} {H = H} θ ∘n η ≡
         lamp {F = K} {G = G} {H = H} (θ ∘n < η ∘n (π₁n K G idn) , (π₂n K G idn) >)
natlam {F = F} {G} {H} {K} {θ} {η} =
  let lθ = lamp {F = F} {G = G} {H = H} θ
      η↑ = < η ∘n (π₁n K G idn) , (π₂n K G idn) >
      lθη↑ = lamp {F = K} {G = G} {H = H} (θ ∘n η↑)
  in nat≡ λ {i Δ x →
              let p : act lθ Δ (act η Δ x)
                      ≡ act lθη↑ Δ x
                  p = nat≡ λ {i Γ (σ ,, y) →
                               let p : act θ Γ ((act η Δ x) +⟨ F ⟩ σ ,, y)
                                       ≡ act θ Γ (act η Γ (x +⟨ K ⟩ σ) ,, y)
                                   p = ap (λ x → act θ Γ (x ,, y)) (nat η ⁻¹)
                               in p i}
              in p i}

