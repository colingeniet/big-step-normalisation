{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Syntax.Types
open import Weakening.Variable

{-
  Only presheaves over the category of weakenings are really required here,
  hence the custom definition and syntax.
  It is important to require the codomain of presheaves to be actual sets and
  not arbitrary types, to ensure e.g. the categorical laws for natural transformations.
-}
record Pshw {l : Level} : Set (lsuc l) where
  field
    apply : Con → Set l
    isSetapply : {Γ : Con} → isSet (apply Γ)
    map : ∀ {Γ Δ} → Wk Γ Δ → apply Δ → apply Γ
    +id : ∀ {Γ} {x : apply Γ} → map idw x ≡ x
    +∘ : ∀ {Γ Δ Θ} {x : apply Θ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
           map (σ ∘w ν) x ≡ map ν (map σ x)

  syntax apply F Γ = F $o Γ
  syntax map F σ x = x +⟨ F ⟩ σ

open Pshw public


-- Natural transformation between presheaves on weakenings.
record Natw {l m} (F : Pshw {l}) (G : Pshw {m}) : Set (l ⊔ m) where
  field
    act : (Γ : Con) → F $o Γ → G $o Γ
    nat : {Γ Δ : Con} {σ : Wk Γ Δ} {x : F $o Δ} →
          act Γ (x +⟨ F ⟩ σ) ≡ (act Δ x) +⟨ G ⟩ σ

open Natw public

private
  variable
    l m n k : Level
    F : Pshw {l}
    G : Pshw {m}


-- Because the codomain of presheaves are sets, it is never necessary to
-- prove the equality of the naturality conditions between transformations.
nat≡ : {θ η : Natw {l} {m} F G} → act θ ≡ act η → θ ≡ η
act (nat≡ p i) = p i
nat (nat≡ {F = F} {G} {θ} {η} p i) {Γ} {Δ} {σ} {x} j =
  ouc (isSetFillSquare (isSetapply G)
                       (nat θ {σ = σ} {x})
                       (nat η {σ = σ} {x})
                       (λ k → (p k) Γ (map F σ x))
                       (λ k → map G σ ((p k) Δ x))
                       i j)

isSetnat : isSet (Natw F G)
act (isSetnat {G = G} p q i j) Γ x =
  isSetapply G (λ j → act (p j) Γ x) (λ j → act (q j) Γ x) i j
nat (isSetnat {F = F} {G = G} p q i j) {Γ} {Δ} {σ} {x} k =
  ouc (isSetPartial (isSetapply G)
       (λ j → nat (p j) {σ = σ} {x} k) (λ j → nat (q j) {σ = σ} {x} k)
       λ {(k = i0) → λ i j →
          isSetapply G (λ j → act (p j) Γ (x +⟨ F ⟩ σ))
                       (λ j → act (q j) Γ (x +⟨ F ⟩ σ)) i j
         ;(k = i1) → λ i j →
          (isSetapply G (λ j → act (p j) Δ x) (λ j → act (q j) Δ x) i j)
           +⟨ G ⟩ σ})
      i j
