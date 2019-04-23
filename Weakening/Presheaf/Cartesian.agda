{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.Cartesian where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Pairs public
open import Library.Pairs.Sets
open import Weakening.Variable.Base
open import Weakening.Presheaf
open import Weakening.Presheaf.Category


private
  variable
    l m n k : Level
    F : Pshw {l}
    G : Pshw {m}
    H : Pshw {n}
    K : Pshw {k}


-- Cartesian structure of the category of presheaves.
-- Terminal object.
𝟙p : ∀ {l} → Pshw {l}
(𝟙p {l}) $o Γ = ⊤l {l}
isSetapply 𝟙p = PropisSet isProp⊤l
x +⟨ 𝟙p ⟩ σ = x
+id 𝟙p = refl
+∘ 𝟙p = refl

!p : ∀ {l m} {F : Pshw {l}} → Natw F (𝟙p {m})
act !p Γ x = tt
nat !p = refl

!pη : ∀ {l m} {F : Pshw {l}} {θ : Natw F (𝟙p {m})} → θ ≡ !p
!pη = nat≡ λ i Γ x → tt

-- Products
infixl 10 _×p_ _,n_ _×n_

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

_,n_ : Natw F G → Natw F H → Natw F (G ×p H)
act (θ ,n α) Γ x = act θ Γ x ,, act α Γ x
nat (θ ,n α) = ap2 _,,_ (nat θ) (nat α)

-- Laws
π₁nβ : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F G} {α : Natw F H} →
       π₁n G H (θ ,n α) ≡ θ
π₁nβ = nat≡ refl

π₂nβ : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F G} {α : Natw F H} →
       π₂n G H (θ ,n α) ≡ α
π₂nβ = nat≡ refl

πnη : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {θ : Natw F (G ×p H)} →
      (π₁n G H θ ,n π₂n G H θ) ≡ θ
πnη {θ = θ} = nat≡ (λ i Γ x → act θ Γ x)

,∘n : {F : Pshw {l}} {G : Pshw {m}} {H : Pshw {n}} {K : Pshw {k}}
      {θ : Natw F G} {α : Natw F H} {β : Natw K F} →
      (θ ,n α) ∘n β ≡ (θ ∘n β ,n α ∘n β)
,∘n = nat≡ refl


_×n_ : Natw F G → Natw H K → Natw (F ×p H) (G ×p K)
_×n_ {F = F} {G = G} {H = H} {K = K} θ α =
  (θ ∘n (π₁n F H idn)) ,n (α ∘n (π₂n F H idn))
