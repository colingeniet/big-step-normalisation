{-# OPTIONS --cubical #-}

module Syntax.Sets where

open import Library.Equality
open import Library.Sets
open import Library.Maybe
open import Library.Negation
open import Library.NotEqual
open import Syntax.Terms


abstract
  isSetCon : isSet Con
  isSetCon {●} {●} p q =
    let p≡refl : p ≡ refl
        p≡refl i j = ●η (p j) (λ k → p (j ∧ (1- k))) i
        q≡refl : q ≡ refl
        q≡refl i j = ●η (q j) (λ k → q (j ∧ (1- k))) i
    in p≡refl ∙ q≡refl ⁻¹
    -- The point of this function is that ●η ● p is refl no matter p.
    -- This is similar to the proof of Hedberg theorem.
    where ●η : (Θ : Con) (p : Θ ≡ ●) → Θ ≡ ●
          ●η ● _ = refl
          ●η (_ , _) p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p))
  isSetCon {●} {_ , _} p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
  isSetCon {_ , _} {●} p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p))
  isSetCon {Γ , A} {Δ , B} p q =
    let p1 : Γ ≡ Δ
        p1 i = π₁C (p i) (λ j → p (i ∧ (1- j)))
        p2 : A ≡[ ap Ty p1 ]≡ B
        p2 i = π₂C (p i) (λ j → p (i ∧ (1- j)))
        q1 : Γ ≡ Δ
        q1 i = π₁C (q i) (λ j → q (i ∧ (1- j)))
        q2 : A ≡[ ap Ty q1 ]≡ B
        q2 i = π₂C (q i) (λ j → q (i ∧ (1- j)))
        p≡p1p2 : p ≡ (λ i → (p1 i) , (p2 i))
        p≡p1p2 i j = πηC (p j) (λ k → p (j ∧ (1- k))) (1- i)
        q≡q1q2 : q ≡ (λ i → (q1 i) , (q2 i))
        q≡q1q2 i j = πηC (q j) (λ k → q (j ∧ (1- k))) (1- i)
        p1≡q1 : p1 ≡ q1
        p1≡q1 = isSetCon {Γ} {Δ} p1 q1
        p2≡q2 : p2 ≡[ ap (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 ]≡ q2
        p2≡q2 = trfill (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 p2
                d∙ isSetDependent {B = Ty} isSetTy (tr (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 p2) q2
    in p≡p1p2 ∙ (λ i j → p1≡q1 i j , p2≡q2 i j) ∙ q≡q1q2 ⁻¹
    -- Same remark as for the case of ●.
    where π₁C : (Θ : Con) → Θ ≡ Γ , A → Con
          π₁C ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          π₁C (Θ , _) _ = Θ
          π₂C : (Θ : Con) (p : Θ ≡ Γ , A) → Ty (π₁C Θ p)
          π₂C ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          π₂C (_ , C) _ = C
          πηC : (Θ : Con) (p : Θ ≡ Γ , A) → (π₁C Θ p) , (π₂C Θ p) ≡ Θ
          πηC ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          πηC (Θ , C) _ = refl


postulate
  isSetTm : {Γ : Con} {A : Ty Γ} → isSet (Tm Γ A)
  isSetTms : {Γ Δ : Con} → isSet (Tms Γ Δ)
