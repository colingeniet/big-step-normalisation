{-# OPTIONS --safe --cubical #-}

module Variable.Sets where

open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.Negation
open import Library.NotEqual
open import Library.Pairs
open import Library.Maybe
open import Syntax.Terms
open import Variable.Variable
open import Agda.Builtin.Nat
open import Library.Nat.Sets

{- It is much easier to decide heterogeneous equality first,
   as otherwise agda get stuck on unsolved equality constraints on types
   Those could theoretically be solved 'by hand' since types form a set
   (at least I think so), but it would be very tedious.
-}
discreteVar' : {Γ : Con} {A B : Ty Γ} (x : Var Γ A) (y : Var Γ B) →
               Decidable (x ≅[ Var Γ ] y)
discreteVar' z z = yes refl≅
discreteVar' {Γ} z (s y) =
  no (λ p → let q : ⊤ ≅[ (λ (A : Ty Γ) → Set) ] ⊥
                q = ap≅ {f = λ A → A} f p
            in ⊤≢⊥ (snd q))
  where f : {A : Ty Γ} → Var Γ A → Set
        f z = ⊤
        f (s x) = ⊥
discreteVar' {Γ} (s x) z = 
  no (λ p → let q : ⊤ ≅[ (λ (A : Ty Γ) → Set) ] ⊥
                q = ap≅ {f = λ A → A} f p
            in ⊤≢⊥ (snd q))
  where f : {A : Ty Γ} → Var Γ A → Set
        f z = ⊥
        f (s x) = ⊤
discreteVar' {Γ , C} (s x) (s y)
  with discreteVar' x y
...  | yes p = yes (ap≅ s p)
...  | no n = no (λ p → let f : {A : Ty (Γ , C)} → Var (Γ , C) A →
                                Maybe (Σ[ B ∈ Ty Γ ] Var Γ B)
                            f = λ {(s x) → yes (_ ,, x); z → no}
                            q : (_ ,, x) ≡ (_ ,, y)
                            q = yes-injective (apd f (snd p))
                        in n (≡[]-to-≅ (apd snd q)))

-- Decidability of regular equality follows easily.
discreteVar : {Γ : Con} {A : Ty Γ} → Discrete (Var Γ A)
discreteVar x y with discreteVar' x y
...                | no n = no (λ p → n (≡-to-≅ p))
...                | yes p = yes (≅-to-≡ isSetTy p)

isSetVar : {Γ : Con} {A : Ty Γ} → isSet (Var Γ A)
isSetVar = DiscreteisSet discreteVar
