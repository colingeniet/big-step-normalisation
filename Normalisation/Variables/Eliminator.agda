{-# OPTIONS --safe --cubical #-}

module Normalisation.Variables.Eliminator where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Types.Sets
open import Normalisation.Variables

{-
  Eliminate a variable of type  Var (Γ , A) A
  Without K, agda can not do pattern matching because the case  z
  would introduce a loop A ≡ A.
  The fact that types form a set is required to avoid this issue.
-}
elimVar : ∀ {l} {Γ : Con} {A : Ty}
            (P : Var (Γ , A) A → Set l)
            (cz : P z) (cs : (x : Var Γ A) → P (s x)) →
            (x : Var (Γ , A) A) → P x
elimVar {Γ = Γ} {A} P cz cs x =
  trd P (trfill (Var (Γ , A)) refl x ⁻¹) (aux x refl)
  where aux : {B : Ty} (x : Var (Γ , A) B) (p : A ≡ B) →
              P (tr (Var (Γ , A)) (p ⁻¹) x)
        aux z = K isSetTy (trd P (trfill (Var (Γ , A)) refl z) cz)
        aux (s x) p = J (λ {B} p → (x : Var Γ B) → P (tr (Var (Γ , A)) (p ⁻¹) (s x)))
                        (λ x → trd P (trfill (Var (Γ , A)) refl (s x)) (cs x)) p x

-- The same, non-dependent.
recVar : ∀ {l} {Γ : Con} {A : Ty} {P : Set l}
           (cz : P) (cs : Var Γ A → P) →
           Var (Γ , A) A → P
recVar {Γ = Γ} {A} {P} cz cs x = aux x refl
  where aux : {B : Ty} → Var (Γ , A) B → A ≡ B → P
        aux z p = cz
        aux (s x) p = cs (tr (Var Γ) (p ⁻¹) x)


recVar≡z : ∀ {l} {Γ : Con} {A : Ty} {P : Set l}
             {cz : P} {cs : Var Γ A → P} →
             recVar cz cs z ≡ cz
recVar≡z = refl

recVar≡s : ∀ {l} {Γ : Con} {A : Ty} {P : Set l}
             {cz : P} {cs : Var Γ A → P} {x : Var Γ A} →
             recVar cz cs (s x) ≡ cs x
recVar≡s {Γ = Γ} {cs = cs} {x} = apd cs (trfill (Var Γ) refl x ⁻¹)
