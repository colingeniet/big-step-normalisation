{-# OPTIONS --allow-unsolved-meta --cubical #-}

module Normalisation.NormalForms.Sets where

open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.NotEqual
open import Library.Pairs
open import Library.Maybe
open import Syntax.Terms
open import Syntax.Types.Sets
open import Normalisation.Variables
open import Normalisation.Variables.Sets
open import Agda.Builtin.Nat
open import Library.Nat.Sets
open import Normalisation.NormalForms



discreteNf : {Γ : Con} {A : Ty} → Discrete (Nf Γ A)
discreteNe : {Γ : Con} {A : Ty} → Discrete (Ne Nf Γ A)

discreteNf {A = o} (neu u) (neu v)
  with discreteNe u v
...  | yes p = yes (ap neu p)
...  | no n  = no λ p → n (ap (λ {(neu u) → u}) p)
discreteNf {A = A ⟶ B} (lam u) (lam v)
  with discreteNf u v
...  | yes p = yes (ap lam p)
...  | no n  = no λ p → n (ap (λ {(lam u) → u}) p)

discreteNe (var x) (var y)
  with discreteVar x y
...  | yes p = yes (ap var p)
...  | no  n = let getvar = λ {(var x) → yes x; (app _ _) → no}
               in no λ p → n (yes-injective (ap getvar p))
discreteNe (var x) (app n u) = no λ p →
  ⊤≢⊥ (ap (λ {(var _) → ⊤; (app _ _) → ⊥}) p)
discreteNe (app n u) (var x) = no λ p →
  ⊤≢⊥ (ap (λ {(var _) → ⊥; (app _ _) → ⊤}) p)
discreteNe {Γ = Γ} (app {A = A1} {B = B} f u) (app {A = A2} g v)
  with discreteTy A1 A2
...  | no n  = no λ p → n (ap (λ {(app {A = A} _ _) → A;
                                  (var {A = A} _) → A})
                              p)
...  | yes p = {!!}
{-
...  | yes p = J (λ {A2 : Ty} (P : A1 ≡ A2) →
                    {f : Ne Nf Γ (A1 ⟶ B)} {g : Ne Nf Γ (A2 ⟶ B)}
                    {u : Nf Γ A1} {v : Nf Γ A2} →
                    Decidable (app f u ≡ app g v))
                 decApp p {f} {g} {u} {v}
  where decApp : {Γ : Con} {A B : Ty} {f g : Ne Nf Γ (A ⟶ B)} {u v : Nf Γ A} →
                 Decidable (Ne.app f u ≡ app g v)
        decApp {Γ} {A} {B} {f} {g} {u} {v}
          with discreteNe f g | discreteNf u v
        ...  | no n | _ = no λ p →
          n (make-non-dependent {B = λ A → Ne Nf Γ (A ⟶ B)} isSetTy
                                (apd snd (yes-injective (ap getfun p))))
          where getfun : Ne Nf Γ B → Maybe (Σ[ A ∈ Ty ] Ne Nf Γ (A ⟶ B))
                getfun (var _) = no
                getfun (app {A = A} f _) = yes (A ,, f)
        ... | yes p | no n = no λ p →
          n (make-non-dependent {B = λ A → Nf Γ A} isSetTy
                                (apd snd (yes-injective (ap getarg p))))
          where getarg : Ne Nf Γ B → Maybe (Σ[ A ∈ Ty ] Nf Γ A)
                getarg (var _) = no
                getarg (app {A = A} _ u) = yes (A ,, u)
        ... | yes p | yes q = yes (ap2 app p q)
-}

isSetNf : {Γ : Con} {A : Ty} → isSet (Nf Γ A)
isSetNf = DiscreteisSet discreteNf
