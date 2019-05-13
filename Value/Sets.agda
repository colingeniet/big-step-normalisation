{-# OPTIONS --safe --cubical #-}

module Value.Sets where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Value.Value
open import Value.Lemmas


isSetEnv : {Γ Δ : Con} → isSet (Env Γ Δ)
isSetEnv {Γ} {●} = PropisSet λ {ε ε → refl}
isSetEnv {Γ} {Δ , A} {σ , u} {ν , v} p q =
  let p1 : σ ≡ ν
      p1 j = π₁E (p j)
      q1 : σ ≡ ν
      q1 j = π₁E (q j)
      p2 : u ≡[ ap (λ x → Val Γ (A [ ⌜ x ⌝E ]T)) p1 ]≡ v
      p2 j = π₂E (p j)
      q2 : u ≡[ ap (λ x → Val Γ (A [ ⌜ x ⌝E ]T)) q1 ]≡ v
      q2 j = π₂E (q j)
      p' : σ Env., u ≡ ν , v
      p' i = p1 i , p2 i
      q' : σ Env., u ≡ ν , v
      q' i = q1 i , q2 i
      p≡p' : p ≡ p'
      p≡p' j i = πηE {ρ = p i} (1- j)
      p'≡q' : p' ≡ q'
      p'≡q' j i = isSetEnv p1 q1 j i ,
                  isSetDependent2 {B = λ x → Val Γ (A [ ⌜ x ⌝E ]T)} isSetEnv isSetVal p2 q2 j i
      q≡q' : q ≡ q'
      q≡q' j i = πηE {ρ = q i} (1- j)
  in p≡p' ∙ p'≡q' ∙ q≡q' ⁻¹
