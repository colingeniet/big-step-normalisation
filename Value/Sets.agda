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
  let p1 = λ j → π₁E (p j)
      q1 = λ j → π₁E (q j)
      p2 = λ j → π₂E (p j)
      q2 = λ j → π₂E (q j)
      p≡p1p2 = λ i j → πηE {ρ = p j} (1- i)
      q1q2≡q = λ i j → πηE {ρ = q j} i
      p1p2≡q1q2 = λ i j → isSetEnv p1 q1 i j , isSetVal p2 q2 i j
  in p≡p1p2 ∙ p1p2≡q1q2 ∙ q1q2≡q
