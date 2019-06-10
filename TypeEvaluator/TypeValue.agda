{-# OPTIONS --cubical --safe #-}

module TypeEvaluator.TypeValue where

open import Library.Equality
open import Syntax.Terms
open import TypeEvaluator.Skeleton

-- Value (substitution free) types
data TV : TSk → Con → Set
⌜_⌝T : {S : TSk} {Γ : Con} → TV S Γ → Ty Γ

data TV where
  U : {Γ : Con} → TV U Γ
  El : {Γ : Con} → Tm Γ U → TV El Γ
  Π : {Γ : Con} {S T : TSk} (A : TV S Γ) (B : TV T (Γ , ⌜ A ⌝T)) → TV (Π S T) Γ

⌜ U ⌝T = U
⌜ El u ⌝T = El u
⌜ Π A B ⌝T = Π ⌜ A ⌝T ⌜ B ⌝T

-- Value contexts
data CV : TSks → Set
⌜_⌝C : {S : TSks} → CV S → Con

data CV where
  ● : CV ●
  _,_ : {S : TSks} {T : TSk} (Γ : CV S) → TV T ⌜ Γ ⌝C → CV (S , T)

⌜ ● ⌝C = ●
⌜ Γ , A ⌝C = ⌜ Γ ⌝C , ⌜ A ⌝T


skeleton⌜⌝T : {S : TSk} {Γ : Con} {A : TV S Γ} → skeleton ⌜ A ⌝T ≡ S
skeleton⌜⌝T {A = U} = refl
skeleton⌜⌝T {A = El u} = refl
skeleton⌜⌝T {A = Π A B} = ap2 Π (skeleton⌜⌝T {A = A}) (skeleton⌜⌝T {A = B})

skeletons⌜⌝C : {S : TSks} {Γ : CV S} → skeletons ⌜ Γ ⌝C ≡ S
skeletons⌜⌝C {Γ = ●} = refl
skeletons⌜⌝C {Γ = Γ , A} = ap2 _,_ (skeletons⌜⌝C {Γ = Γ}) (skeleton⌜⌝T {A = A})
