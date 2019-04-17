{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.List where

open import Agda.Primitive
open import Library.Equality
open import Syntax.Terms
open import Syntax.List
open import Weakening.Presheaf
open import Syntax.Terms.Presheaf


-- Lifting from presheaves indexed by types to presheaves indexed by contexts.
private
  variable
    l m : Level
    F : Ty → Pshw {l}
    G : Ty → Pshw {m}


listp : (Ty → Pshw {l}) → Con → Pshw {l}
(listp F Δ) $o Γ = list (λ A → F A $o Γ) Δ
isSetapply (listp F Δ) = isSetList (isSetapply (F _))
ρ +⟨ listp F Δ ⟩ σ = mapl (λ x → x +⟨ F _ ⟩ σ) ρ
+id (listp F ●) {x = ε} = refl
+id (listp F (Δ , A)) {x = ρ , x} =
  ap2 _,_ (+id (listp F Δ)) (+id (F A))
+∘ (listp F ●) {x = ε} = refl
+∘ (listp F (Δ , A)) {x = ρ , x} =
  ap2 _,_ (+∘ (listp F Δ)) (+∘ (F A))


-- Corresponding lifting of natural transformations.
mapn : ({A : Ty} → Natw (F A) (G A)) →
       {Γ : Con} → Natw (listp F Γ) (listp G Γ)
act (mapn θ) _ = mapl (act θ _)
nat (mapn θ {●}) {x = ε} = refl
nat (mapn θ {Δ , A}) {x = ρ , x} = ap2 _,_ (nat (mapn θ {Δ})) (nat θ)

-- And lifting of natural transformations with terms as codomain, for embeddings.
mapnt : ({A : Ty} → Natw (F A) (Tm' A)) →
        {Γ : Con} → Natw (listp F Γ) (Tms' Γ)
act (mapnt θ) _ = mapt (act θ _)
nat (mapnt θ {●}) {x = ε} = εη ⁻¹
nat (mapnt θ {Δ , A}) {x = ρ , x} =
  ap2 _,_ (nat (mapnt θ {Δ})) (nat θ)
  ∙ ,∘ ⁻¹
