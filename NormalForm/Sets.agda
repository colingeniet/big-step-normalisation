{-# OPTIONS --safe --cubical #-}

module NormalForm.Sets where

open import Library.Equality
open import Library.Decidable
open import Library.Sets
open import Library.NotEqual
open import Library.Pairs
open import Library.Maybe
open import Syntax.Terms
open import Syntax.Types.Sets
open import Weakening.Variable
open import Weakening.Variable.Sets
open import Agda.Builtin.Nat
open import Library.Nat.Sets
open import NormalForm.NormalForm

{-
  Equality of normal forms is decided by untyping them, for the same reasons
  as for variables (see Normalisation.Variables.Sets for more details).
-}

-- Untyped normal forms.
data untyped-Nf : Set
data untyped-NN : Set

data untyped-Nf where
  lam : untyped-Nf → untyped-Nf
  neu : untyped-NN → untyped-Nf

data untyped-NN where
  var : Nat → untyped-NN
  app : untyped-NN → untyped-Nf → untyped-NN

untype-Nf : {Γ : Con} {A : Ty} → Nf Γ A → untyped-Nf
untype-NN : {Γ : Con} {A : Ty} → NN Γ A → untyped-NN
untype-Nf (lam n) = lam (untype-Nf n)
untype-Nf (neu n) = neu (untype-NN n)
untype-NN (var x) = var (untype-var x)
untype-NN (app f u) = app (untype-NN f) (untype-Nf u)


-- Somehow, the typing function is easier to define if the expected type
-- is given for normal forms but not for neutral normal forms.
type-Nf : (Γ : Con) (A : Ty) → untyped-Nf → Maybe (Nf Γ A)
type-NN : (Γ : Con) → untyped-NN → Maybe (Σ[ A ∈ Ty ] NN Γ A)

type-Nf-aux-neu : {Γ : Con} → Maybe (Σ[ A ∈ Ty ] NN Γ A) → Maybe (Nf Γ o)
type-Nf-aux-neu no = no
type-Nf-aux-neu (yes (_ ⟶ _ ,, _)) = no
type-Nf-aux-neu (yes (o ,, n)) = yes (neu n)

type-Nf Γ o (lam u) = no
type-Nf Γ (A ⟶ B) (lam u) = maybe-lift lam (type-Nf (Γ , A) B u)
type-Nf Γ o (neu u) =
  type-Nf-aux-neu (type-NN Γ u)
type-Nf Γ (_ ⟶ _) (neu _) = no

type-NN-aux-app1 : {Γ : Con} (A B : Ty) → NN Γ (A ⟶ B) →
                   Maybe (Nf Γ A) → Maybe (NN Γ B)
type-NN-aux-app1 A B n m = maybe-lift (app n) m
type-NN-aux-app2 : {Γ : Con} → untyped-Nf → Maybe (Σ[ A ∈ Ty ] NN Γ A) →
                   Maybe (Σ[ A ∈ Ty ] NN Γ A)
type-NN-aux-app2 _ no = no
type-NN-aux-app2 _ (yes (o ,, _)) = no
type-NN-aux-app2 {Γ} v (yes (A ⟶ B ,, n)) =
  maybe-lift (λ u → B ,, u)
             (type-NN-aux-app1 A B n (type-Nf Γ A v))

type-NN Γ (var x) = maybe-lift (λ {(A ,, x) → A ,, var x}) (type-var Γ x)
type-NN Γ (app u v) = type-NN-aux-app2 v (type-NN Γ u)



type-Nf-inverse : {Γ : Con} {A : Ty} {n : Nf Γ A} →
                  type-Nf Γ A (untype-Nf n) ≡ yes n
type-NN-inverse : {Γ : Con} {A : Ty} {n : NN Γ A} →
                  type-NN Γ (untype-NN n) ≡ yes (A ,, n)

type-Nf-inverse {n = lam n} = ap (maybe-lift lam) (type-Nf-inverse {n = n})
type-Nf-inverse {Γ} {n = neu n} =
  ap type-Nf-aux-neu (type-NN-inverse {n = n})

type-NN-inverse {n = var x} =
  ap (maybe-lift (λ {(A ,, x) → A ,, var x}))
     (type-var-inverse {x = x})
type-NN-inverse {Γ} {n = app {A = A} {B} f u} =
  ap (type-NN-aux-app2 (untype-Nf u)) (type-NN-inverse {n = f})
  ∙ ap (λ u → maybe-lift (λ x → B ,, x) (type-NN-aux-app1 A B f u))
       (type-Nf-inverse {n = u})


untype-Nf-injective : {Γ : Con} {A : Ty} {n m : Nf Γ A} →
                      untype-Nf n ≡ untype-Nf m → n ≡ m
untype-Nf-injective {Γ} {A} p =
  yes-injective (type-Nf-inverse ⁻¹
                ∙ ap (type-Nf Γ A) p
                ∙ type-Nf-inverse)

untype-NN-injective : {Γ : Con} {A : Ty} {n m : NN Γ A} →
                      untype-NN n ≡ untype-NN m → n ≡ m
untype-NN-injective {Γ} {A} {n} {m} p =
  let An≡Am : (A ,, n) ≡ (A ,, m)
      An≡Am = yes-injective (type-NN-inverse ⁻¹
                            ∙ (ap (type-NN Γ) p)
                            ∙ type-NN-inverse)
  in make-non-dependent {B = NN Γ} isSetTy (apd snd An≡Am)


discrete-untyped-Nf : Discrete untyped-Nf
discrete-untyped-NN : Discrete untyped-NN

discrete-untyped-Nf (lam u) (lam v)
  with discrete-untyped-Nf u v
...  | yes p = yes (ap lam p)
...  | no n  = no λ p → n (ap (λ {(lam n) → n; n → n}) p)
discrete-untyped-Nf (neu u) (neu v)
  with discrete-untyped-NN u v
...  | yes p = yes (ap neu p)
...  | no n  = no λ p → n (ap (λ {(neu n) → n; _ → var zero}) p)
discrete-untyped-Nf (lam _) (neu _) =
  no λ p → ⊤≢⊥ (ap (λ {(lam _) → ⊤; (neu _) → ⊥}) p)
discrete-untyped-Nf (neu _) (lam _) =
  no λ p → ⊤≢⊥ (ap (λ {(neu _) → ⊤; (lam _) → ⊥}) p)

discrete-untyped-NN (var x) (var y)
  with discreteNat x y
...  | yes p = yes (ap var p)
...  | no n  = no λ p → n (ap (λ {(var x) → x; _ → zero}) p)
discrete-untyped-NN (app f u) (app g v)
  with discrete-untyped-NN f g | discrete-untyped-Nf u v
...  | yes p | yes q = yes (ap2 app p q)
...  | yes _ | no n  = no λ p →
  n (yes-injective (ap (λ {(app _ u) → yes u; _ → no}) p))
...  | no n  | _     = no λ p → n (ap (λ {(app f _) → f; n → n}) p)
discrete-untyped-NN (var _) (app _ _) =
  no λ p → ⊤≢⊥ (ap (λ {(var _) → ⊤; (app _ _) → ⊥}) p)
discrete-untyped-NN (app _ _) (var _) =
  no λ p → ⊤≢⊥ (ap (λ {(app _ _) → ⊤; (var _) → ⊥}) p)



discreteNf : {Γ : Con} {A : Ty} → Discrete (Nf Γ A)
discreteNf u v with discrete-untyped-Nf (untype-Nf u) (untype-Nf v)
...               | yes p = yes (untype-Nf-injective p)
...               | no n  = no λ p → n (ap untype-Nf p)

isSetNf : {Γ : Con} {A : Ty} → isSet (Nf Γ A)
isSetNf = DiscreteisSet discreteNf


discreteNN : {Γ : Con} {A : Ty} → Discrete (NN Γ A)
discreteNN u v with discrete-untyped-NN (untype-NN u) (untype-NN v)
...               | yes p = yes (untype-NN-injective p)
...               | no n  = no λ p → n (ap untype-NN p)

isSetNN : {Γ : Con} {A : Ty} → isSet (NN Γ A)
isSetNN = DiscreteisSet discreteNN
