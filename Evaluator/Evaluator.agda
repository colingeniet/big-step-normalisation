{-# OPTIONS --safe --cubical #-}

module Evaluator.Evaluator where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Weakening.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm

{- It is by no mean clear that this evaluator terminates, hence it can not be
   defined as a regular function. Instead, it is defined as a relation.
   In
     eval u > envρ ⇒ valu
   u is a term, ρ is an environment, envρ the proof that ρ is an environment.
   valu is a proof that u is a value, but remember that terms are considered
   up to β conversion: the intuition is that valu is a proof that v is a value
   for some v equivalent to u. The predicate then claims that 'u evaluates to v
   in ρ'.
   evals is exactly similar for environments.
   $ applies a value to another, and returns a value, with the same relation 
   as above.

   Comments indicate how the more intuitive recursive function would be defined.
-}

-- eval : (u : Tm Δ A) (ρ : Env Γ Δ) → Val Γ A
data eval_>_⇒_ : {Γ Δ : Con} {A : Ty} → Tm Δ A → Env Γ Δ → Val Γ A → Set
-- eval : (σ : Tms Δ Θ) (ρ : Env Γ Δ) → Env Γ Θ
data evals_>_⇒_ : {Γ Δ Θ : Con} → Tms Δ Θ → Env Γ Δ → Env Γ Θ → Set
-- _$_ : (f : Val Γ (A ⟶ B)) (u : Val Γ A) → Val Γ B
data _$_⇒_ : {Γ : Con} {A B : Ty} → Val Γ (A ⟶ B) → Val Γ A → Val Γ B → Set

data eval_>_⇒_ where
  -- eval (u [ σ ]) ρ = eval u (evals σ ρ)
  eval[] : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
           {σρ : Env Γ Θ} {uσρ : Val Γ A} →
           evals σ > ρ ⇒ σρ → eval u > σρ ⇒ uσρ →
           eval (u [ σ ]) > ρ ⇒ uσρ
  -- eval (π₂ σ) ρ = π₂ (evals σ ρ)
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ}
           {σρ : Env Γ (Θ , A)} → evals σ > ρ ⇒ σρ →
           eval (π₂ σ) > ρ ⇒ π₂E σρ
  -- eval (lam u) ρ = (lam u) [ ρ ]
  evallam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) →
            eval (lam u) > ρ ⇒ lam u ρ
  -- eval (app f) (σ , u) = (eval f σ) $ u
  evalapp : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {ρ : Env Γ (Δ , A)} →
            {fρ : Val Γ (A ⟶ B)} {appfρ : Val Γ B} →
            eval f > π₁E ρ ⇒ fρ → fρ $ π₂E ρ ⇒ appfρ →
            eval (app f) > ρ ⇒ appfρ
  isPropeval : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} {v : Val Γ A} →
               isProp (eval u > ρ ⇒ v)
data evals_>_⇒_ where
  -- evals id ρ = ρ
  evalsid : {Γ Δ : Con} {ρ : Env Γ Δ} → evals id > ρ ⇒ ρ
  -- evals (σ ∘ ν) ρ = evals σ (evals ν ρ)
  evals∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {ρ : Env Γ Δ}
           {νρ : Env Γ Θ} {σνρ : Env Γ Ψ} →
           evals ν > ρ ⇒ νρ → evals σ > νρ ⇒ σνρ →
           evals (σ ∘ ν) > ρ ⇒ σνρ
  -- evals ε ρ = ε
  evalsε : {Γ Δ : Con} {ρ : Env Γ Δ} → evals ε > ρ ⇒ ε
  -- evals (σ , u) ρ = (evals σ ρ) , (eval u ρ)
  evals, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {u : Tm Δ A} {ρ : Env Γ Δ}
           {σρ : Env Γ Θ} {uρ : Val Γ A} →
           evals σ > ρ ⇒ σρ → eval u > ρ ⇒ uρ →
           evals (σ , u) > ρ ⇒ (σρ , uρ)
  -- evals (π₁ σ) ρ = π₁ (evals σ ρ)
  evalsπ₁ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ}
            {σρ : Env Γ (Θ , A)} → evals σ > ρ ⇒ σρ →
            evals (π₁ σ) > ρ ⇒ π₁E σρ
  isPropevals : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν : Env Γ Θ} →
                isProp (evals σ > ρ ⇒ ν)
data _$_⇒_ where
  -- (lam u) [ ρ ] $ v = eval u (ρ , v)
  $lam : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} {v : Val Γ A}
         {uρv : Val Γ B} →  eval u > (ρ , v) ⇒ uρv →
         (lam u ρ) $ v ⇒ uρv
  -- n $ v = n v
  $app : {Γ : Con} {A B : Ty} (n : NV Γ (A ⟶ B)) (v : Val Γ A) →
         (neu n) $ v ⇒ neu (app n v)
  isProp$ : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} {u : Val Γ A} {v : Val Γ B} →
            isProp (f $ u ⇒ v)


-- q : Val Γ A → Nf Γ A
data q_⇒_ : {Γ : Con} {A : Ty} → Val Γ A → Nf Γ A → Set
-- qs : NV Γ Δ → NN Γ Δ
data qs_⇒_ : {Γ : Con} {A : Ty} → NV Γ A → NN Γ A → Set

data q_⇒_ where
  -- q (n : o) = qs n
  -- A value of type o must be neutral !
  qo : {Γ : Con} {n : NV Γ o} {nf : NN Γ o} →
       qs n ⇒ nf → q (neu n) ⇒ (neu nf)
  -- q (f : A ⟶ B) = lam (q (f $ vz))
  q⟶ : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)}
       {fz : Val (Γ , A) B} {nffvz : Nf (Γ , A) B} →
       (f +V (wkwk A idw)) $ (neu (var z)) ⇒ fz → q fz ⇒ nffvz →
       q f ⇒ lam nffvz
  isPropq : {Γ : Con} {A : Ty} {v : Val Γ A} {n : Nf Γ A} →
            isProp (q v ⇒ n)
data qs_⇒_ where
  -- qs x ⇒ x
  qsvar : {Γ : Con} {A : Ty} {x : Var Γ A} → qs (var x) ⇒ (var x)
  -- qs (n $ v) ⇒ (qs n) $ (q v)
  qsapp : {Γ : Con} {A B : Ty} {f : NV Γ (A ⟶ B)} {u : Val Γ A}
          {neff : NN Γ (A ⟶ B)} {nfu : Nf Γ A} →
          qs f ⇒ neff → q u ⇒ nfu →
          qs (app f u) ⇒ (app neff nfu)
  isPropqs : {Γ : Con} {A : Ty} {v : NV Γ A} {n : NN Γ A} →
             isProp (qs v ⇒ n)


-- norm : Tm Γ A → Nf Γ A
data norm_⇒_ : {Γ : Con} {A : Ty} → Tm Γ A → Nf Γ A → Set where
  qeval : {Γ : Con} {A : Ty} {u : Tm Γ A} {v : Val Γ A} {n : Nf Γ A} →
          eval u > idenv ⇒ v → q v ⇒ n → norm u ⇒ n
