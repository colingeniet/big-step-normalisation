{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.Category where

open import Agda.Primitive
open import Library.Equality
open import Syntax.Types
open import Weakening.Presheaf


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
