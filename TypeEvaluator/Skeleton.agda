{-# OPTIONS --safe --cubical #-}

module TypeEvaluator.Skeleton where

open import Library.Equality
open import Library.Sets
open import Library.Decidable
open import Library.Negation
open import Library.NotEqual
open import Library.Maybe
open import Syntax.Terms


{- The skeleton of a type is used as a size annotation for type values.
   Notably, it is invariant by substitution.
-}

data TSk : Set where
  U : TSk
  El : TSk
  Π : TSk → TSk → TSk

infixl 10 _,_
data TSks : Set where
  ● : TSks
  _,_ : TSks → TSk → TSks
  

discreteTSk : Discrete TSk
discreteTSk U U = yes refl
discreteTSk U El = no λ p → ⊤≢⊥ (ap (λ {U → ⊤; El → ⊥; (Π _ _) → ⊥}) p)
discreteTSk U (Π A B) = no λ p → ⊤≢⊥ (ap (λ {U → ⊤; El → ⊥; (Π _ _) → ⊥}) p)
discreteTSk El U = no λ p → ⊤≢⊥ (ap (λ {U → ⊥; El → ⊤; (Π _ _) → ⊥}) p)
discreteTSk El El = yes refl
discreteTSk El (Π A B) = no λ p → ⊤≢⊥ (ap (λ {U → ⊥; El → ⊤; (Π _ _) → ⊥}) p)
discreteTSk (Π A B) U = no λ p → ⊤≢⊥ (ap (λ {U → ⊥; El → ⊥; (Π _ _) → ⊤}) p)
discreteTSk (Π A B) El = no λ p → ⊤≢⊥ (ap (λ {U → ⊥; El → ⊥; (Π _ _) → ⊤}) p)
discreteTSk (Π A B) (Π C D)
  with discreteTSk A C | discreteTSk B D
...  | yes p | yes q = yes (ap2 Π p q)
...  | yes _ | no n  = no λ p → n (yes-injective (ap (λ {(Π _ A) → yes A; U → no; El → no}) p))
...  | no n  | _     = no λ p → n (yes-injective (ap (λ {(Π A _) → yes A; U → no; El → no}) p))

discreteTSks : Discrete TSks
discreteTSks ● ● = yes refl
discreteTSks ● (_ , _) = no λ p → ⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p)
discreteTSks (_ , _) ● = no λ p → ⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p)
discreteTSks (Γ , A) (Δ , B)
  with discreteTSks Γ Δ | discreteTSk A B
...  | yes p | yes q = yes (ap2 _,_ p q)
...  | yes _ | no n  = no λ p → n (yes-injective (ap (λ {(_ , A) → yes A; ● → no}) p))
...  | no n  | _     = no λ p → n (yes-injective (ap (λ {(Γ , _) → yes Γ; ● → no}) p))


isSetTSk : isSet TSk
isSetTSk = DiscreteisSet discreteTSk

isSetTSks : isSet TSks
isSetTSks = DiscreteisSet discreteTSks


skeleton : {Γ : Con} → Ty Γ → TSk
skeleton U = U
skeleton (El _) = El
skeleton (Π A B) = Π (skeleton A) (skeleton B)
skeleton (A [ _ ]T) = skeleton A
skeleton ([id]T {A = A} i) = skeleton A
skeleton ([][]T {A = A} i) = skeleton A
skeleton (U[] i) = U
skeleton (El[] i) = El
skeleton (Π[] {A = A} {B} i) = Π (skeleton A) (skeleton B)
skeleton (isSetTy p q i j) = isSetTSk (λ k → skeleton (p k)) (λ k → skeleton (q k)) i j

skeletons : Con → TSks
skeletons ● = ●
skeletons (Γ , A) = skeletons Γ , skeleton A
