{-# OPTIONS --safe --cubical #-}

module Syntax.List where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Decidable
open import Syntax.Terms


-- Lifts a type indexed by types to a type indexed by contexts.
infixl 10 _,_
data list {l} (X : Ty → Set l) : Con → Set l where
  ε : list X ●
  _,_ : {Γ : Con} {A : Ty} → list X Γ → X A → list X (Γ , A)

private
  variable
    l m : Level
    X : Ty → Set l
    Y : Ty → Set m

π₁l : {Γ : Con} {A : Ty} → list X (Γ , A) → list X Γ
π₁l (σ , _) = σ
π₂l : {Γ : Con} {A : Ty} → list X (Γ , A) → X A
π₂l (_ , u) = u

πηl : {Γ : Con} {A : Ty} {ρ : list X (Γ , A)} →
      (π₁l ρ , π₂l ρ) ≡ ρ
πηl {ρ = _ , _} = refl


mapl : ({A : Ty} → X A → Y A) →
       {Γ : Con} → list X Γ → list Y Γ
mapl f ε = ε
mapl f (σ , u) = mapl f σ , f u

-- Lifting of (X → Tm) to (list X → Tms)
-- Tms is not (list Tm) !
mapt : {X : Con → Ty → Set l} →
       ({Γ : Con} {A : Ty} → X Γ A → Tm Γ A) →
       {Γ Δ : Con} → list (X Γ) Δ → Tms Γ Δ
mapt f ε = ε
mapt f (σ , u) = mapt f σ , f u


isSetList : ({A : Ty} → isSet (X A)) →
            {Γ : Con} → isSet (list X Γ)
isSetList isSetX {●} = PropisSet λ {ε ε → refl}
isSetList isSetX {Γ , A} {σ , u} {ν , v} p q =
  let p1 = λ j → π₁l (p j)
      q1 = λ j → π₁l (q j)
      p2 = λ j → π₂l (p j)
      q2 = λ j → π₂l (q j)
      p≡p1p2 = λ i j → πηl {ρ = p j} (1- i)
      q1q2≡q = λ i j → πηl {ρ = q j} i
      p1p2≡q1q2 = λ i j → isSetList isSetX p1 q1 i j , isSetX p2 q2 i j
  in p≡p1p2 ∙ p1p2≡q1q2 ∙ q1q2≡q

discreteList : ({A : Ty} → Discrete (X A)) →
               {Γ : Con} → Discrete (list X Γ)
discreteList discreteX ε ε = yes refl
discreteList discreteX (σ , u) (ν , v)
  with discreteList discreteX σ ν | discreteX u v
...  | no n  | _     = no λ p → n (ap π₁l p)
...  | yes _ | no n  = no λ p → n (ap π₂l p)
...  | yes p | yes q = yes (ap2 _,_ p q)

