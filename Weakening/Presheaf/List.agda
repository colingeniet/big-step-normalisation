{-# OPTIONS --safe --cubical #-}

module Weakening.Presheaf.List where

open import Agda.Primitive
open import Library.Equality
open import Syntax.Terms
open import Syntax.List public
open import Weakening.Variable.Base
open import Weakening.Presheaf
open import Weakening.Presheaf.Category
open import Weakening.Presheaf.Cartesian
open import Syntax.Terms.Weakening
open import Syntax.Terms.Presheaf


private
  variable
    l m : Level
    F : Ty → Pshw {l}
    G : Ty → Pshw {m}


-- List of presheaves.
listp : (Ty → Pshw {l}) → Con → Pshw {l}
(listp F Δ) $o Γ = list (λ A → (F A) $o Γ) Δ
isSetapply (listp F Δ) = isSetList (λ {A} → isSetapply (F A))
map (listp F Δ) σ = mapl (λ {A} → map (F A) σ)
+id (listp F ●) = refl
+id (listp F (Δ , A)) = ap2 _,,_ (+id (listp F Δ)) (+id (F A))
+∘ (listp F ●) = refl
+∘ (listp F (Δ , A)) = ap2 _,,_ (+∘ (listp F Δ)) (+∘ (F A))


-- Corresponding lifting of natural transformations.
mapn : {F : Ty → Pshw {l}} {G : Ty → Pshw {m}} →
       ({A : Ty} → Natw (F A) (G A)) →
       {Γ : Con} → Natw (listp F Γ) (listp G Γ)
mapn θ {●} = !p
mapn θ {Γ , A} = (mapn θ {Γ}) ×n (θ {A})


-- Lifting of natural transformations with terms as codomain, for embeddings.
mapnt : {F : Ty → Pshw {l}} →
        ({A : Ty} → Natw (F A) (Tm' A)) →
        {Γ : Con} → Natw (listp F Γ) (Tms' Γ)
act (mapnt θ) _ σ = mapt (λ {Γ} → act θ Γ) σ
nat (mapnt θ {●}) =
  ε ≡⟨ εη ⁻¹ ⟩
  ε +s _ ∎
nat (mapnt {F = F} θ {Ψ , A}) {Γ} {Δ} {σ} {x ,, y} =
  let aθ = λ {Δ} → act θ Δ
      aθs = λ {Δ} → act (mapnt θ) Δ
  in aθs (x +⟨ listp F Ψ ⟩ σ) , aθ (y +⟨ F A ⟩ σ) ≡⟨ ap2 _,_ (nat (mapnt θ)) (nat θ) ⟩
     (aθs x ∘ ⌜ σ ⌝w) , (aθ y) [ ⌜ σ ⌝w ]          ≡⟨ ,∘ ⁻¹ ⟩
     (aθs x , aθ y) ∘ ⌜ σ ⌝w ∎

