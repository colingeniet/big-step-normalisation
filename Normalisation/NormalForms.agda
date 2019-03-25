{-# OPTIONS --safe --cubical #-}

{-
  Definition of normal forms.
-}

module Normalisation.NormalForms where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Normalisation.Variables


-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : Con → Ty → Set
data Ne : Con → Ty → Set
data Sp : Con → Ty → Ty → Set

data Nf where
  lam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  neu : {Γ : Con} → Ne Γ o → Nf Γ o

infix 12 _#_
data Ne where
  _#_ : {Γ : Con} {A B : Ty} → Var Γ A → Sp Γ A B → Ne Γ B

infixl 15 _∷_
data Sp where
  nil : {Γ : Con} {A : Ty} → Sp Γ A A
  _∷_ : {Γ : Con} {A B C : Ty} → Nf Γ A → Sp Γ B C → Sp Γ (A ⟶ B) C


append : {Γ : Con} {A B C : Ty} → Sp Γ A (B ⟶ C) → Nf Γ B → Sp Γ A C
append nil n = n ∷ nil
append (n ∷ ns) m = n ∷ (append ns m)

var : {Γ : Con} {A : Ty} → Var Γ A → Ne Γ A
var x = x # nil

appne : {Γ : Con} {A B : Ty} → Ne Γ (A ⟶ B) → Nf Γ A → Ne Γ B
appne (x # ns) n = x # append ns n


-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝Ne : {Γ : Con} {A : Ty} → Ne Γ A → Tm Γ A
_⌜_⌝Sp : {Γ : Con} {A B : Ty} → Tm Γ A → Sp Γ A B → Tm Γ B
⌜ lam n ⌝N = lam ⌜ n ⌝N
⌜ neu n ⌝N = ⌜ n ⌝Ne
⌜ x # ns ⌝Ne = ⌜ x ⌝v ⌜ ns ⌝Sp
u ⌜ nil ⌝Sp = u
u ⌜ n ∷ ns ⌝Sp = (u $ ⌜ n ⌝N) ⌜ ns ⌝Sp


infixr 10 _,_
data Env : Con → Con → Set where
  ε : {Γ : Con} → Env Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → Env Γ Δ → Nf Γ A → Env Γ (Δ , A)

⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ
⌜ ε ⌝E = ε
⌜ ρ , n ⌝E = ⌜ ρ ⌝E , ⌜ n ⌝N


π₁env : {Γ Δ : Con} {A : Ty} → Env Γ (Δ , A) → Env Γ Δ
π₁env (ρ , _) = ρ
π₂env : {Γ Δ : Con} {A : Ty} → Env Γ (Δ , A) → Nf Γ A
π₂env (_ , n) = n

πηenv : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} → (π₁env ρ , π₂env ρ) ≡ ρ
πηenv {ρ = ρ , u} = refl

εηenv : {Γ : Con} {ρ : Env Γ ●} → ρ ≡ ε
εηenv {ρ = ε} = refl
