{-# OPTIONS --cubical #-}

module Evaluator.Evaluator where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable
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
data eval_>_⇒_ : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (ρ : Env Γ Δ) → Val Γ (A [ ⌜ ρ ⌝E ]T) → Set
-- eval : (σ : Tms Δ Θ) (ρ : Env Γ Δ) → Env Γ Θ
data evals_>_⇒_ : {Γ Δ Θ : Con} → Tms Δ Θ → Env Γ Δ → Env Γ Θ → Set
-- _$_ : (f : Val Γ (A ⟶ B)) (u : Val Γ A) → Val Γ B
data _$_⇒_ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Val Γ (Π A B) →
             (v : Val Γ A) → Val Γ (B [ < ⌜ v ⌝V > ]T) → Set

eval≡ : {Γ Δ : Con} {A : Ty Δ} {u : Tm Δ A} {ρ : Env Γ Δ}
        {uρ : Val Γ (A [ ⌜ ρ ⌝E ]T)} → eval u > ρ ⇒ uρ →
        u [ ⌜ ρ ⌝E ] ≡ ⌜ uρ ⌝V
evals≡ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
         {σρ : Env Γ Θ} → evals σ > ρ ⇒ σρ →
         σ ∘ ⌜ ρ ⌝E ≡ ⌜ σρ ⌝E
eval$≡ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Val Γ (Π A B)}
         {v : Val Γ A} {uv : Val Γ (B [ < ⌜ v ⌝V > ]T)} → u $ v ⇒ uv →
         ⌜ u ⌝V $ ⌜ v ⌝V ≡ ⌜ uv ⌝V

private
  [evals≡] : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
             {σρ : Env Γ Θ} → evals σ > ρ ⇒ σρ →
             A [ ⌜ σρ ⌝E ]T ≡ A [ σ ]T [ ⌜ ρ ⌝E ]T
  [evals≡] {A = A} {σ} {ρ} {σρ} evalsσ =
    A [ ⌜ σρ ⌝E ]T       ≡⟨ ap (A [_]T) (evals≡ evalsσ) ⁻¹ ⟩
    A [ σ ∘ ⌜ ρ ⌝E ]T    ≡⟨ [][]T ⟩
    A [ σ ]T [ ⌜ ρ ⌝E ]T ∎

  [↑∘<>] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {ρ : Tms Γ Δ}
           {v : Tm Γ (A [ ρ ]T)} → B [ ρ , v ]T ≡ B [ ρ ↑ A ]T [ < v > ]T
  [↑∘<>] {A = A} {B} {ρ} {v} =
    B [ ρ , v ]T            ≡⟨ ap (B [_]T) ↑∘<> ⁻¹ ⟩
    B [ (ρ ↑ A) ∘ < v > ]T  ≡⟨ [][]T ⟩
    B [ ρ ↑ A ]T [ < v > ]T ∎

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
  -- evals (π₁ σ) ρ = π₁ (evals σ ρ)
  evalsπ₁ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ}
            {σρ : Env Γ (Θ , A)} → evals σ > ρ ⇒ σρ →
            evals (π₁ σ) > ρ ⇒ π₁E σρ
  -- evals (σ , u) ρ = (evals σ ρ) , (eval u ρ)
  evals, : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {u : Tm Δ (A [ σ ]T)} {ρ : Env Γ Δ}
           {σρ : Env Γ Θ} {uρ : Val Γ (A [ σ ]T [ ⌜ ρ ⌝E ]T)} →
           (evalsσ : evals σ > ρ ⇒ σρ) → eval u > ρ ⇒ uρ →
           evals (σ , u) > ρ ⇒ (σρ , tr (Val Γ) ([evals≡] evalsσ ⁻¹) uρ)
  isPropevals : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν : Env Γ Θ} →
                isProp (evals σ > ρ ⇒ ν)

data eval_>_⇒_ where
  -- eval (u [ σ ]) ρ = eval u (evals σ ρ)
  eval[] : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
           {σρ : Env Γ Θ} {uσρ : Val Γ (A [ ⌜ σρ ⌝E ]T)} →
           (evalsσ : evals σ > ρ ⇒ σρ) → eval u > σρ ⇒ uσρ →
           eval (u [ σ ]) > ρ ⇒ tr (Val Γ) ([evals≡] evalsσ) uσρ
  -- eval (π₂ σ) ρ = π₂ (evals σ ρ)
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ}
           {σρ : Env Γ (Θ , A)} → (evalsσ : evals σ > ρ ⇒ σρ) →
           eval (π₂ σ) > ρ ⇒ tr (Val Γ) ([evals≡] (evalsπ₁ evalsσ)) (π₂E σρ)
  -- eval (lam u) ρ = (lam u) [ ρ ]
  evallam : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
            (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → eval (lam u) > ρ ⇒ lam u ρ
  -- eval (app f) (σ , u) = (eval f σ) $ u
  evalapp : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)}
            {ρ : Env Γ Δ} {v : Val Γ (A [ ⌜ ρ ⌝E ]T)} {fρ : Val Γ (Π A B [ ⌜ ρ ⌝E ]T)}
            {fρv : Val Γ (B [ ⌜ ρ ⌝E ↑ A ]T [ < ⌜ v ⌝V > ]T)} →
            eval f > ρ ⇒ fρ → (tr (Val Γ) Π[] fρ) $ v ⇒ fρv →
            eval (app f) > (ρ , v) ⇒ tr (Val Γ) ([↑∘<>] ⁻¹) fρv
  isPropeval : {Γ Δ : Con} {A : Ty Δ} {u : Tm Δ A} {ρ : Env Γ Δ} {v : Val Γ (A [ ⌜ ρ ⌝E ]T)} →
               isProp (eval u > ρ ⇒ v)
  
data _$_⇒_ where
  -- (lam u) [ ρ ] $ v = eval u (ρ , v)
  $lam : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {u : Tm (Δ , A) B} {ρ : Env Γ Δ}
         {v : Val Γ (A [ ⌜ ρ ⌝E ]T)} {uρv : Val Γ (B [ ⌜ ρ , v ⌝E ]T)} →
         eval u > (ρ , v) ⇒ uρv →
         tr (Val Γ) Π[] (lam u ρ) $ v ⇒ tr (Val Γ) [↑∘<>] uρv
  -- n $ v = n v
  $app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} (n : NV Γ (Π A B)) (v : Val Γ A) →
         (neu n) $ v ⇒ neu (app n v)
  isProp$ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Val Γ (Π A B)}
            {u : Val Γ A} {v : Val Γ (B [ < ⌜ u ⌝V > ]T)} →
            isProp (f $ u ⇒ v)


abstract
  evals≡ (evalsid {ρ = ρ}) =
    id ∘ ⌜ ρ ⌝E ≡⟨ id∘ ⟩
    ⌜ ρ ⌝E      ∎
  evals≡ (evals∘ {σ = σ} {ν} {ρ} {νρ} {σνρ} cν cσ) =
    (σ ∘ ν) ∘ ⌜ ρ ⌝E ≡⟨ ∘∘ ⟩
    σ ∘ (ν ∘ ⌜ ρ ⌝E) ≡⟨ ap (_∘_ _) (evals≡ cν) ⟩
    σ ∘ ⌜ νρ ⌝E      ≡⟨ evals≡ cσ ⟩
    ⌜ σνρ ⌝E         ∎
  evals≡ (evalsε {ρ = ρ}) =
    ε ∘ ⌜ ρ ⌝E ≡⟨ εη ⟩
    ε         ∎
  evals≡ (evals, {σ = σ} {u} {ρ} {σρ} {uρ} cσ cu) =
    let p : tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ])
            ≅[ Tm _ ] ⌜ tr (Val _) ([evals≡] cσ ⁻¹) uρ ⌝V
        p = tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ]) ≅⟨ trfill (Tm _) ([][]T ⁻¹) _ ⁻¹ ⟩
            u [ ⌜ ρ ⌝E ]                        ≅⟨ eval≡ cu ⟩
            ⌜ uρ ⌝V                             ≅⟨ apd ⌜_⌝V (trfill (Val _) ([evals≡] cσ ⁻¹) uρ) ⟩
            ⌜ tr (Val _) ([evals≡] cσ ⁻¹) uρ ⌝V ≅∎
    in (σ , u) ∘ ⌜ ρ ⌝E
         ≡⟨ ,∘ ⟩
       σ ∘ ⌜ ρ ⌝E , tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ])
         ≡⟨ (λ i → evals≡ cσ i , ≅-to-≡[] isSetTy p {P = ap (_ [_]T) (evals≡ cσ)} i) ⟩
       ⌜ σρ , tr (Val _) ([evals≡] cσ ⁻¹) uρ ⌝E ∎
  evals≡ (evalsπ₁ {σ = σ} {ρ} {σρ} cσ) =
    (π₁ σ) ∘ ⌜ ρ ⌝E ≡⟨ π₁∘ ⁻¹ ⟩
    π₁ (σ ∘ ⌜ ρ ⌝E) ≡⟨ ap π₁ (evals≡ cσ) ⟩
    π₁ ⌜ σρ ⌝E      ≡⟨ π₁E≡ ⁻¹ ⟩
    ⌜ π₁E σρ ⌝E     ∎
  evals≡ (isPropevals c c' i) =
    isSetTms (evals≡ c) (evals≡ c') i

  eval≡ (eval[] {u = u} {σ} {ρ} {σρ} {uσρ} cσ cu) = ≅-to-≡ {B = Tm _} isSetTy (
    u [ σ ] [ ⌜ ρ ⌝E ] ≅⟨ [][] ≅⁻¹ ⟩'
    u [ σ ∘ ⌜ ρ ⌝E ]   ≅⟨ apd (u [_]) (evals≡ cσ) ⟩
    u [ ⌜ σρ ⌝E ]      ≅⟨ eval≡ cu ⟩
    ⌜ uσρ ⌝V           ≅⟨ apd ⌜_⌝V (trfill (Val _) ([evals≡] cσ) uσρ) ⟩
    ⌜ tr (Val _) ([evals≡] cσ) uσρ ⌝V ≅∎)
  eval≡ (evalπ₂ {σ = σ} {ρ} {σρ} cσ) = ≅-to-≡ {B = Tm _} isSetTy (
    (π₂ σ) [ ⌜ ρ ⌝E ] ≅⟨ π₂∘ ≅⁻¹ ⟩'
    π₂ (σ ∘ ⌜ ρ ⌝E)   ≅⟨ apd π₂ (evals≡ cσ) ⟩
    π₂ ⌜ σρ ⌝E        ≅⟨ π₂E≡ ≅⁻¹ ⟩'
    ⌜ π₂E σρ ⌝V       ≅⟨ apd ⌜_⌝V (trfill (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ)) ⟩
    ⌜ tr (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ) ⌝V ≅∎)
  eval≡ (evallam u ρ) =
    (lam u) [ ⌜ ρ ⌝E ] ∎
  eval≡ (evalapp {Γ} {Δ} {A} {B} {f} {ρ} {v} {fρ} {fρv} cf $fρ) =
    let p : tr (Tm Γ) Π[] ⌜ fρ ⌝V ≅[ Tm Γ ] ⌜ tr (Val Γ) Π[] fρ ⌝V
        p = tr (Tm Γ) Π[] ⌜ fρ ⌝V  ≅⟨ trfill (Tm Γ) Π[] ⌜ fρ ⌝V ⁻¹ ⟩
            ⌜ fρ ⌝V                ≅⟨ apd ⌜_⌝V (trfill (Val Γ) Π[] fρ) ⟩
            ⌜ tr (Val Γ) Π[] fρ ⌝V ≅∎
    in ≅-to-≡ {B = Tm _} isSetTy (
    (app f) [ ⌜ ρ , v ⌝E ]
      ≅⟨ app[] ⟩'
    tr (Tm Γ) Π[] (f [ π₁ ⌜ ρ , v ⌝E ]) $ π₂ ⌜ ρ , v ⌝E
      ≅⟨ (λ i → tr (Tm Γ) Π[] (f [ π₁β {σ = ⌜ ρ ⌝E} {⌜ v ⌝V} i ])
                $ ≅-to-≡[] isSetTy π₂β {P = ap (A [_]T) π₁β} i) ⟩
    tr (Tm Γ) Π[] (f [ ⌜ ρ ⌝E ]) $ ⌜ v ⌝V
      ≅⟨ ap (λ x → tr (Tm Γ) Π[] x $ ⌜ v ⌝V) (eval≡ cf) ⟩
    tr (Tm Γ) Π[] ⌜ fρ ⌝V $ ⌜ v ⌝V
      ≅⟨ ap (_$ ⌜ v ⌝V) (≅-to-≡ isSetTy p) ⟩
    ⌜ tr (Val Γ) Π[] fρ ⌝V $ ⌜ v ⌝V
      ≅⟨ eval$≡ $fρ ⟩
    ⌜ fρv ⌝V
      ≅⟨ apd ⌜_⌝V (trfill (Val Γ) ([↑∘<>] ⁻¹) fρv) ⟩
    ⌜ tr (Val Γ) ([↑∘<>] ⁻¹) fρv ⌝V ≅∎)
  eval≡ (isPropeval c c' i) =
    isSetTm (eval≡ c) (eval≡ c') i

  eval$≡ ($lam {u = u} {ρ} {v} {uv} cu) =
    let p : ⌜ tr (Val _) Π[] (lam u ρ) ⌝V ≅[ Tm _ ] tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ])
        p = ⌜ tr (Val _) Π[] (lam u ρ) ⌝V ≅⟨ apd ⌜_⌝V (trfill (Val _) Π[] (lam u ρ) ⁻¹) ⟩
            ⌜ lam u ρ ⌝V                  ≅⟨ trfill (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) ⟩
            tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) ≅∎
    in ≅-to-≡ {B = Tm _} isSetTy (
    ⌜ tr (Val _) Π[] (lam u ρ) ⌝V $ ⌜ v ⌝V
      ≅⟨ ap (_$ ⌜ v ⌝V) (≅-to-≡ isSetTy p) ⟩
    tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) $ ⌜ v ⌝V
      ≅⟨ clos[] ⟩'
    u [ ⌜ ρ , v ⌝E ]
      ≅⟨ eval≡ cu ⟩
    ⌜ uv ⌝V
      ≅⟨ apd ⌜_⌝V (trfill (Val _) [↑∘<>] uv) ⟩
    ⌜ tr (Val _) [↑∘<>] uv ⌝V ≅∎)
  eval$≡ ($app n v) =
    ⌜ n ⌝NV $ ⌜ v ⌝V ∎
  eval$≡ (isProp$ c c' i) =
    isSetTm (eval$≡ c) (eval$≡ c') i

{-
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
-}
