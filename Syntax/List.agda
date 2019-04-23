{-# OPTIONS --safe --cubical #-}

module Syntax.List where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Decidable
open import Library.Pairs public
open import Library.Pairs.Sets
open import Syntax.Terms


-- Lifts a type indexed by types to a type indexed by contexts.
list : ∀ {l} (X : Ty → Set l) → Con → Set l
list X ● = ⊤l
list X (Γ , A) = list X Γ × X A


private
  variable
    l m : Level
    X : Ty → Set l
    Y : Ty → Set m

mapl : ({A : Ty} → X A → Y A) →
       {Γ : Con} → list X Γ → list Y Γ
mapl f {●} tt = tt
mapl f {_ , _} (σ ,, u) = mapl f σ ,, f u

-- Lifting of (X → Tm) to (list X → Tms)
-- Tms is not (list Tm) !
mapt : {X : Con → Ty → Set l} →
       ({Γ : Con} {A : Ty} → X Γ A → Tm Γ A) →
       {Γ Δ : Con} → list (X Γ) Δ → Tms Γ Δ
mapt f {Δ = ●} tt = ε
mapt f {Δ = _ , _} (σ ,, u) = mapt f σ , f u


isSetList : ({A : Ty} → isSet (X A)) →
            {Γ : Con} → isSet (list X Γ)
isSetList isSetX {●} = PropisSet isProp⊤l
isSetList isSetX {_ , _} = isSet× (isSetList isSetX) isSetX


discreteList : ({A : Ty} → Discrete (X A)) →
               {Γ : Con} → Discrete (list X Γ)
discreteList discreteX {●} _ _ = yes refl
discreteList discreteX {Γ , A} (σ ,, u) (ν ,, v)
  with discreteList discreteX σ ν | discreteX u v
...  | no n  | _     = no λ p → n (ap fst p)
...  | yes _ | no n  = no λ p → n (ap snd p)
...  | yes p | yes q = yes (ap2 _,,_ p q)
