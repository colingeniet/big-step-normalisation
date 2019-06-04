{-# OPTIONS --safe --cubical #-}

module Evaluator.Evaluator where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Maybe
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Domain
open import Variable.Variable
open import Variable.Lemmas
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
   They are overly simplyfied, and types are incorrect (would be correct for the
   simply typed lambda-calculus).
-}

-- eval : (u : Tm Δ A) (ρ : Env Γ Δ) → Val Γ A
-- It would be tempting to instead define this as
--   Tm Δ A → (ρ : Env Γ Δ) → Val Γ (A [ ⌜ ρ ⌝E ]T)
-- However, I found easier to make the relation more heterogeneous in some sense.
-- Note that  B ≡ A [ ⌜ ρ ⌝E ]T  follows from the  eval≡  lemma (it is the underlying path).
data eval_>_⇒_ : {Γ Δ : Con} {A : Ty Δ} {B : Ty Γ} →
                 Tm Δ A → Env Γ Δ → Val Γ B → Set
-- eval : (σ : Tms Δ Θ) (ρ : Env Γ Δ) → Env Γ Θ
data evals_>_⇒_ : {Γ Δ Θ : Con} → Tms Δ Θ → Env Γ Δ → Env Γ Θ → Set
-- _$_ : (f : Val Γ (A ⟶ B)) (u : Val Γ A) → Val Γ B
-- Same remark regarding the result type.
data _$_⇒_ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C : Ty Γ} →
             Val Γ (Π A B) → Val Γ A → Val Γ C → Set

-- Evaluation is the same as applying a substitution, up to all the appropriate embeddings.
eval≡ : {Γ Δ : Con} {A : Ty Δ} {B : Ty Γ} {u : Tm Δ A} {ρ : Env Γ Δ}
        {uρ : Val Γ B} → eval u > ρ ⇒ uρ → u [ ⌜ ρ ⌝E ] ≅[ Tm Γ ] ⌜ uρ ⌝V
evals≡ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ}
         {σρ : Env Γ Θ} → evals σ > ρ ⇒ σρ →
         σ ∘ ⌜ ρ ⌝E ≡ ⌜ σρ ⌝E
eval$≡ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C : Ty Γ}
         {u : Val Γ (Π A B)} {v : Val Γ A} {uv : Val Γ C} →
         u $ v ⇒ uv → ⌜ u ⌝V $ ⌜ v ⌝V ≅[ Tm Γ ] ⌜ uv ⌝V

abstract
  -- This lemma is required for a transport in the  evals,  constructor.
  evals,-aux : {Γ Δ Θ : Con} {A : Ty Θ} {B : Ty Γ} {σ : Tms Δ Θ} {u : Tm Δ (A [ σ ]T)}
               {ρ : Env Γ Δ} {σρ : Env Γ Θ} {uρ : Val Γ B} →
               evals σ > ρ ⇒ σρ → eval u > ρ ⇒ uρ → B ≡ A [ ⌜ σρ ⌝E ]T
  evals,-aux {A = A} {B} {σ} {u} {ρ} {σρ} evalsσ evalu =
    B                   ≡⟨ fst (eval≡ evalu) ⁻¹ ⟩
    A [ σ ]T [ ⌜ ρ ⌝E ]T ≡⟨ [][]T ⁻¹ ⟩
    A [ σ ∘ ⌜ ρ ⌝E ]T    ≡⟨ ap (A [_]T) (evals≡ evalsσ) ⟩
    A [ ⌜ σρ ⌝E ]T       ∎


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
  evals, : {Γ Δ Θ : Con} {A : Ty Θ} {B : Ty Γ} {σ : Tms Δ Θ} {u : Tm Δ (A [ σ ]T)}
           {ρ : Env Γ Δ} {σρ : Env Γ Θ} {uρ : Val Γ B} →
           (evalsσ : evals σ > ρ ⇒ σρ) → (evalu : eval u > ρ ⇒ uρ) →
           evals (σ , u) > ρ ⇒ (σρ , tr (Val Γ) (evals,-aux evalsσ evalu) uρ)
  isPropevals : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν : Env Γ Θ} →
                isProp (evals σ > ρ ⇒ ν)

data eval_>_⇒_ where
  -- eval (u [ σ ]) ρ = eval u (evals σ ρ)
  eval[] : {Γ Δ Θ : Con} {A : Ty Θ} {B : Ty Γ} {u : Tm Θ A} {σ : Tms Δ Θ}
           {ρ : Env Γ Δ} {σρ : Env Γ Θ} {uσρ : Val Γ B} →
           evals σ > ρ ⇒ σρ → eval u > σρ ⇒ uσρ →
           eval (u [ σ ]) > ρ ⇒ uσρ
  -- eval (π₂ σ) ρ = π₂ (evals σ ρ)
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ}
           {σρ : Env Γ (Θ , A)} → evals σ > ρ ⇒ σρ →
           eval (π₂ σ) > ρ ⇒ π₂E σρ
  -- eval (lam u) ρ = (lam u) [ ρ ]
  evallam : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
            (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → eval (lam u) > ρ ⇒ lam u ρ
  -- eval (app f) (σ , u) = (eval f σ) $ u
  evalapp : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
            {f : Tm Δ (Π A B)} {ρ : Env Γ Δ} {v : Val Γ (A [ ⌜ ρ ⌝E ]T)}
            {C : Ty (Γ , A [ ⌜ ρ ⌝E ]T)} {D : Ty Γ}
            {fρ : Val Γ (Π (A [ ⌜ ρ ⌝E ]T) C)} {fρv : Val Γ D} →
            eval f > ρ ⇒ fρ → fρ $ v ⇒ fρv → eval (app f) > (ρ , v) ⇒ fρv
  isPropeval : {Γ Δ : Con} {A : Ty Δ} {B : Ty Γ} {u : Tm Δ A} {ρ : Env Γ Δ} {v : Val Γ B} →
               isProp (eval u > ρ ⇒ v)

data _$_⇒_ where
  -- (lam u) [ ρ ] $ v = eval u (ρ , v)
  $lam : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {C : Ty Γ}
         {u : Tm (Δ , A) B} {ρ : Env Γ Δ} {v : Val Γ (A [ ⌜ ρ ⌝E ]T)} {uρv : Val Γ C} →
         eval u > (ρ , v) ⇒ uρv → tr (Val Γ) Π[] (lam u ρ) $ v ⇒ uρv
  -- n $ v = n v
  $app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} (n : NV Γ (Π A B)) (v : Val Γ A) →
         (neu n) $ v ⇒ neu (app n v)
  isProp$ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C : Ty Γ}
            {f : Val Γ (Π A B)} {u : Val Γ A} {v : Val Γ C} →
            isProp (f $ u ⇒ v)


abstract
  evals≡ (evalsid {ρ = ρ}) =
    id ∘ ⌜ ρ ⌝E ≡⟨ id∘ ⟩
    ⌜ ρ ⌝E      ∎
  evals≡ (evals∘ {σ = σ} {ν} {ρ} {νρ} {σνρ} evalsν evalsσ) =
    (σ ∘ ν) ∘ ⌜ ρ ⌝E ≡⟨ ∘∘ ⟩
    σ ∘ (ν ∘ ⌜ ρ ⌝E) ≡⟨ ap (_∘_ _) (evals≡ evalsν) ⟩
    σ ∘ ⌜ νρ ⌝E      ≡⟨ evals≡ evalsσ ⟩
    ⌜ σνρ ⌝E         ∎
  evals≡ (evalsε {ρ = ρ}) =
    ε ∘ ⌜ ρ ⌝E ≡⟨ εη ⟩
    ε         ∎
  evals≡ (evals, {A = A} {B} {σ} {u} {ρ} {σρ} {uρ} evalsσ evalu) =
    let p : B ≡ A [ ⌜ σρ ⌝E ]T
        p = evals,-aux evalsσ evalu
        q : tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ]) ≅[ Tm _ ] ⌜ tr (Val _) p uρ ⌝V
        q = tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ])
              ≅⟨ trfill (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ]) ⁻¹ ⟩
            u [ ⌜ ρ ⌝E ] ≅⟨ eval≡ evalu ⟩'
            ⌜ uρ ⌝V      ≅⟨ apd ⌜_⌝V (trfill (Val _) p uρ) ⟩
            ⌜ tr (Val _) p uρ ⌝V ≅∎
    in (σ , u) ∘ ⌜ ρ ⌝E ≡⟨ ,∘ ⟩
       σ ∘ ⌜ ρ ⌝E , tr (Tm _) ([][]T ⁻¹) (u [ ⌜ ρ ⌝E ])
         ≡⟨ (λ i → evals≡ evalsσ i , ≅-to-≡[] isSetTy q {P = ap (A [_]T) (evals≡ evalsσ)} i) ⟩
       ⌜ σρ ⌝E , ⌜ tr (Val _) p uρ ⌝V ∎
  evals≡ (evalsπ₁ {σ = σ} {ρ} {σρ} cσ) =
    (π₁ σ) ∘ ⌜ ρ ⌝E ≡⟨ π₁∘ ⁻¹ ⟩
    π₁ (σ ∘ ⌜ ρ ⌝E) ≡⟨ ap π₁ (evals≡ cσ) ⟩
    π₁ ⌜ σρ ⌝E      ≡⟨ π₁E≡ ⁻¹ ⟩
    ⌜ π₁E σρ ⌝E     ∎
  evals≡ (isPropevals c c' i) =
    isSetTms (evals≡ c) (evals≡ c') i

  eval≡ (eval[] {u = u} {σ} {ρ} {σρ} {uσρ} evalsσ evalu) =
    u [ σ ] [ ⌜ ρ ⌝E ] ≅⟨ [][] ≅⁻¹ ⟩'
    u [ σ ∘ ⌜ ρ ⌝E ]   ≅⟨ apd (u [_]) (evals≡ evalsσ) ⟩
    u [ ⌜ σρ ⌝E ]      ≅⟨ eval≡ evalu ⟩'
    ⌜ uσρ ⌝V           ≅∎
  eval≡ (evalπ₂ {σ = σ} {ρ} {σρ} cσ) =
    (π₂ σ) [ ⌜ ρ ⌝E ] ≅⟨ π₂∘ ≅⁻¹ ⟩'
    π₂ (σ ∘ ⌜ ρ ⌝E)   ≅⟨ apd π₂ (evals≡ cσ) ⟩
    π₂ ⌜ σρ ⌝E        ≅⟨ π₂E≡ ≅⁻¹ ⟩'
    ⌜ π₂E σρ ⌝V       ≅∎
  eval≡ (evallam u ρ) =
    (lam u) [ ⌜ ρ ⌝E ] ≅∎
  eval≡ (evalapp {A = A} {B} {f} {ρ} {v} {C} {D} {fρ} {fvρ} evalf $fρ) =
    let p : tr (Tm _) Π[] (f [ ⌜ ρ ⌝E ]) ≅[ Tm _ ] ⌜ fρ ⌝V
        p = tr (Tm _) Π[] (f [ ⌜ ρ ⌝E ]) ≅⟨ trfill (Tm _) Π[] (f [ ⌜ ρ ⌝E ]) ⁻¹ ⟩
            f [ ⌜ ρ ⌝E ]                 ≅⟨ eval≡ evalf ⟩'
            ⌜ fρ ⌝V                      ≅∎
        q : B [ ⌜ ρ ⌝E ↑ A ]T ≡ C
        q = make-non-dependent {B = λ A → Ty (_ , A)} isSetTy
                               (apd snd (yes-injective (ap domains (fst p))))
    in (app f) [ ⌜ ρ , v ⌝E ]
         ≅⟨ app[] ⟩'
       tr (Tm _) Π[] (f [ π₁ ⌜ ρ , v ⌝E ]) $ π₂ ⌜ ρ , v ⌝E
         ≅⟨ (λ i → tr (Tm _) Π[] (f [ π₁β {σ = ⌜ ρ ⌝E} {⌜ v ⌝V} i ])
                   $ ≅-to-≡[] isSetTy π₂β {P = ap (A [_]T) π₁β} i) ⟩
       tr (Tm _) Π[] (f [ ⌜ ρ ⌝E ]) $ ⌜ v ⌝V
         ≅⟨ apd (_$ ⌜ v ⌝V) (≅-to-≡[] isSetTy p {P = ap (Π (A [ ⌜ ρ ⌝E ]T)) q}) ⟩
       ⌜ fρ ⌝V $ ⌜ v ⌝V
         ≅⟨ eval$≡ $fρ ⟩'
       ⌜ fvρ ⌝V ≅∎
  eval≡ (isPropeval c c' i) =
    isSet≅ isSetTy isSetTm (eval≡ c) (eval≡ c') i

  eval$≡ ($lam {u = u} {ρ} {v} {uv} evalu) =
    let p : ⌜ tr (Val _) Π[] (lam u ρ) ⌝V ≅[ Tm _ ] tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ])
        p = ⌜ tr (Val _) Π[] (lam u ρ) ⌝V ≅⟨ apd ⌜_⌝V (trfill (Val _) Π[] (lam u ρ) ⁻¹) ⟩
            ⌜ lam u ρ ⌝V                  ≅⟨ trfill (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) ⟩
            tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) ≅∎
    in ⌜ tr (Val _) Π[] (lam u ρ) ⌝V $ ⌜ v ⌝V    ≅⟨ ap (_$ ⌜ v ⌝V) (≅-to-≡ isSetTy p) ⟩
       tr (Tm _) Π[] (lam u [ ⌜ ρ ⌝E ]) $ ⌜ v ⌝V ≅⟨ clos[] ⟩'
       u [ ⌜ ρ , v ⌝E ]                         ≅⟨ eval≡ evalu ⟩'
       ⌜ uv ⌝V                                  ≅∎
  eval$≡ ($app n v) =
    ⌜ n ⌝NV $ ⌜ v ⌝V ≅∎
  eval$≡ (isProp$ c c' i) =
    isSet≅ isSetTy isSetTm (eval$≡ c) (eval$≡ c') i



-- q : Val Γ A → Nf Γ A
data q_⇒_ : {Γ : Con} {A : Ty Γ} → Val Γ A → Nf Γ A → Set
-- qs : NV Γ Δ → NN Γ Δ
data qs_⇒_ : {Γ : Con} {A : Ty Γ} → NV Γ A → NN Γ A → Set

q≡ : {Γ : Con} {A : Ty Γ} {u : Val Γ A} {n : Nf Γ A} →
     q u ⇒ n → ⌜ u ⌝V ≡ ⌜ n ⌝N
qs≡ : {Γ : Con} {A : Ty Γ} {u : NV Γ A} {n : NN Γ A} →
      qs u ⇒ n → ⌜ u ⌝NV ≡ ⌜ n ⌝NN

data q_⇒_ where
  -- q (n : U / El x) = qs n
  -- A value of base type must be neutral !
  qU : {Γ : Con} {n : NV Γ U} {nf : NN Γ U} →
       qs n ⇒ nf → q (neu n) ⇒ neuU nf
  qEl : {Γ : Con} {u : Tm Γ U} {n : NV Γ (El u)} {nf : NN Γ (El u)} →
        qs n ⇒ nf → q (neu n) ⇒ neuEl nf
  -- q (f : A ⟶ B) = lam (q (f $ vz))
  qΠ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Val Γ (Π A B)}
       {fz : Val (Γ , A) B} {nfz : Nf (Γ , A) B} →
       tr (Val _) Π[] (f +V (wkw idw))
         $ tr (Val _) [⌜wkid⌝] (neu (var z))
         ⇒ fz →
       q fz ⇒ nfz → q f ⇒ lam nfz
  isPropq : {Γ : Con} {A : Ty Γ} {v : Val Γ A} {n : Nf Γ A} →
            isProp (q v ⇒ n)

data qs_⇒_ where
  -- qs x ⇒ x
  qsvar : {Γ : Con} {A : Ty Γ} {x : Var Γ A} → qs (var x) ⇒ (var x)
  -- qs (n $ v) ⇒ (qs n) $ (q v)
  qsapp : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : NV Γ (Π A B)} {u : Val Γ A}
          {neff : NN Γ (Π A B)} {nfu : Nf Γ A} →
          qs f ⇒ neff → (qu : q u ⇒ nfu) →
          qs (app f u) ⇒ tr (NN Γ) (ap (λ x → B [ < x > ]T) (q≡ qu) ⁻¹) (app neff nfu)
  isPropqs : {Γ : Con} {A : Ty Γ} {v : NV Γ A} {n : NN Γ A} →
             isProp (qs v ⇒ n)

abstract
  q≡ (qU {n = v} {n} qn) =
    ⌜ v ⌝NV ≡⟨ qs≡ qn ⟩
    ⌜ n ⌝NN ∎
  q≡ (qEl {n = v} {n} qn) =
    ⌜ v ⌝NV ≡⟨ qs≡ qn ⟩
    ⌜ n ⌝NN ∎
  q≡ (qΠ {Γ} {A} {B} {f} {fz} {nfz} $f qf) =
    let p : tr (Tm _) Π[] (⌜ f ⌝V [ wk ]) ≅[ Tm _ ] ⌜ tr (Val _) Π[] (f +V wkw idw) ⌝V
        p = tr (Tm _) Π[] (⌜ f ⌝V [ wk ]) ≅⟨ trfill (Tm _) Π[] (⌜ f ⌝V [ wk ]) ⁻¹ ⟩
            ⌜ f ⌝V [ wk ]                 ≅⟨ apd (⌜ f ⌝V [_]) ⌜wkid⌝ ⁻¹ ⟩
            ⌜ f ⌝V [ ⌜ wkw idw ⌝w ]       ≅⟨ ⌜⌝+V {v = f} ⁻¹ ⟩
            ⌜ f +V wkw idw ⌝V             ≅⟨ apd ⌜_⌝V (trfill (Val _) Π[] (f +V wkw idw)) ⟩
            ⌜ tr (Val _) Π[] (f +V wkw idw) ⌝V ≅∎
        q : vz {A = A} ≅[ Tm _ ] ⌜ tr (Val _) [⌜wkid⌝] (neu (var z)) ⌝V
        q = ⌜ neu (var z) ⌝V
              ≅⟨ apd ⌜_⌝V (trfill (Val _) [⌜wkid⌝] (neu (var z))) ⟩
            ⌜ tr (Val _) [⌜wkid⌝] (neu (var z)) ⌝V ≅∎
    in ≅-to-≡ {B = Tm _} isSetTy (
    ⌜ f ⌝V
      ≅⟨ classicη ≅⁻¹ ⟩'
    lam (tr (Tm _) Π[] (⌜ f ⌝V [ wk ]) $ vz)
      ≅⟨ (λ i → lam (≅-to-≡[] isSetTy p {P = ap (λ x → Π (A [ x ]T) (B [ x ↑ A ]T)) ⌜wkid⌝ ⁻¹} i
                     $ ≅-to-≡[] isSetTy q {P = ap (A [_]T) ⌜wkid⌝ ⁻¹} i)) ⟩
    lam (⌜ tr (Val _) Π[] (f +V wkw idw) ⌝V
         $ ⌜ tr (Val _) [⌜wkid⌝] (neu (var z)) ⌝V)
      ≅⟨ ap≅ lam (eval$≡ $f) ⟩'
    lam ⌜ fz ⌝V
      -- Agda has some unsolved metas if this is replaced with (ap lam (q≡ qf)).
      -- Don't ask me why
      ≅⟨ (λ i → lam (q≡ qf i)) ⟩
    lam ⌜ nfz ⌝N ≅∎)

  q≡ (isPropq c c' i) =
    isSetTm (q≡ c) (q≡ c') i  

  qs≡ (qsvar {x = x}) =
    ⌜ x ⌝v ∎
  qs≡ (qsapp {f = f} {v} {n} {m} qf qv) = ≅-to-≡ {B = Tm _} isSetTy (
    ⌜ f ⌝NV $ ⌜ v ⌝V
      ≅⟨ (λ i → qs≡ qf i $ q≡ qv i) ⟩
    ⌜ n ⌝NN $ ⌜ m ⌝N
      ≅⟨ apd ⌜_⌝NN (trfill (NN _) (ap (λ x → _ [ < x > ]T) (q≡ qv) ⁻¹) (app n m)) ⟩
    ⌜ tr (NN _) (ap (λ x → _ [ < x > ]T) (q≡ qv) ⁻¹) (app n m) ⌝NN ≅∎)
  qs≡ (isPropqs c c' i) =
    isSetTm (qs≡ c) (qs≡ c') i

