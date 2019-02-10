{-# OPTIONS --cubical #-}

open import equality
open import types
open import terms
open import normal-forms

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
data eval_>_⇒_ : {Γ Δ : Con} {A : Ty} {ρ : Tms Γ Δ} (u : Tm Δ A) → Env ρ → Val (u [ ρ ]) → Set
-- eval : (σ : Tms Δ Θ) (ρ : Env Γ Δ) → Env Γ Θ
data evals_>_⇒_ : {Γ Δ Θ : Con} {ρ : Tms Γ Δ} (σ : Tms Δ Θ) → Env ρ → Env (σ ∘ ρ) → Set
-- _$_ : (f : Val Γ (A ⟶ B)) (u : Val Γ A) → Val Γ B
data _$_⇒_ : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} {u : Tm Γ A} →
             Val f → Val u → Val (f $ u) → Set

data eval_>_⇒_ where
  -- eval (u [ σ ]) ρ = eval u (evals σ ρ)
  eval[] : {Γ Δ Θ : Con} {A : Ty} {u : Tm Θ A} {σ : Tms Δ Θ} {ρ : Tms Γ Δ} {envρ : Env ρ}
           {envσρ : Env (σ ∘ ρ)} {valu : Val (u [ σ ∘ ρ ])} →
           evals σ > envρ ⇒ envσρ → eval u > envσρ ⇒ valu →
           eval (u [ σ ]) > envρ ⇒ tr (λ t → Val t) [][] valu
  -- eval (π₂ σ) ρ = π₂ (evals σ ρ)
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Tms Γ Δ} {envρ : Env ρ}
           {envσρ : Env (σ ∘ ρ)} → evals σ > envρ ⇒ envσρ →
           eval (π₂ σ) > envρ ⇒ tr Val π₂∘ (π₂list envσρ)
  -- eval (lam u) ρ = lam (u [ ρ ↑ A ])
  evallam : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {envρ : Env ρ} →
            eval (lam u) > envρ ⇒ tr Val (lam[] ⁻¹) (vlam (u [ ρ ↑ A ]))
  -- eval (app f) (σ , u) = (eval f σ) $ u
  evalapp : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {ρ : Tms Γ (Δ , A)} {envρ : Env ρ} →
            {valf : Val (f [ π₁ ρ ])} {valfu : Val (f [ π₁ ρ ] $ π₂ ρ)} →
            eval f > π₁list envρ ⇒ valf → valf $ π₂list envρ ⇒ valfu →
            eval (app f) > envρ ⇒ tr Val (app[] ⁻¹) valfu
data evals_>_⇒_ where
  -- evals id ρ = ρ
  evalsid : {Γ Δ : Con} {ρ : Tms Γ Δ} {envρ : Env ρ} →
            evals id > envρ ⇒ tr Env (id∘ ⁻¹) envρ
  -- evals (σ ∘ ν) ρ = evals σ (evals ν ρ)
  evals∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {ρ : Tms Γ Δ} {envρ : Env ρ}
           {envνρ : Env (ν ∘ ρ)} {envσνρ : Env (σ ∘ (ν ∘ ρ))} →
           evals ν > envρ ⇒ envνρ → evals σ > envνρ ⇒ envσνρ →
           evals (σ ∘ ν) > envρ ⇒ tr Env (∘∘ ⁻¹) envσνρ
  -- evals ε ρ = ε
  evalsε : {Γ Δ : Con} {ρ : Tms Γ Δ} {envρ : Env ρ} →
           evals ε > envρ ⇒ tr Env (εη ⁻¹) ε
  -- evals (σ , u) ρ = (evals σ ρ) , (eval u ρ)
  evals, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {u : Tm Δ A} {ρ : Tms Γ Δ} {envρ : Env ρ}
           {envσρ : Env (σ ∘ ρ)} {valuρ : Val (u [ ρ ])} →
           evals σ > envρ ⇒ envσρ → eval u > envρ ⇒ valuρ →
           evals (σ , u) > envρ ⇒ tr Env (,∘ ⁻¹) (envσρ , valuρ)
  -- evals (π₁ σ) ρ = π₁ (evals σ ρ)
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Tms Γ Δ} {envρ : Env ρ}
           {envσρ : Env (σ ∘ ρ)} → evals σ > envρ ⇒ envσρ →
           evals (π₁ σ) > envρ ⇒ tr Env π₁∘ (π₁list envσρ)
data _$_⇒_ where
  -- (lam u) $ v = eval u (< v >)
  $lam : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} {v : Tm Γ A} {valv : Val v} {valuv : Val (u [ < v > ])} →
         eval u > (idenv , valv) ⇒ valuv →
         (vlam u) $ valv ⇒ tr (λ x → Val (x [ < v > ])) (β ⁻¹) valuv
  -- n $ v = n v
  $app : {Γ : Con} {A B : Ty} {n : Tm Γ (A ⟶ B)} {v : Tm Γ A} (neun : Ne Val n) (valv : Val v) →
         (vneu neun) $ valv ⇒ vneu (app neun valv)


-- q : Val Γ A → Nf Γ A
data q_⇒_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Val u → Nf u → Set
-- qs : Ne Val Γ Δ → Ne Nf Γ Δ
data qs_⇒_ : {Γ : Con} {A : Ty} {u : Tm Γ A} → Ne Val u → Ne Nf u → Set

data q_⇒_ where
  -- q (n : o) = qs n
  -- A value of type o must be neutral !
  qso : {Γ : Con} {u : Tm Γ o} {neuu : Ne Val u} {nefu : Ne Nf u} →
        qs neuu ⇒ nefu → q (vneu neuu) ⇒ (nneu nefu)
  -- q (f : A ⟶ B) = lam (q (f $ vz))
  qs⟶ : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} {valf : Val f}
        {valfvz : Val (f + A $ vz)} {nffvz : Nf (f + A $ vz)} →
        (valf +V A) $ (vneu (var z)) ⇒ valfvz → q valfvz ⇒ nffvz →
        q valf ⇒ tr Nf classicη (nlam nffvz)
data qs_⇒_ where
  -- qs x ⇒ x
  qsvar : {Γ : Con} {A : Ty} {x : Tm Γ A} {varx : Var x} →
          qs (var varx) ⇒ (var varx)
  -- qs (n $ v) ⇒ (qs n) $ (q v)
  qsapp : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} {u : Tm Γ A} {neuf : Ne Val f} {valu : Val u}
          {neff : Ne Nf f} {nfu : Nf u} →
          qs neuf ⇒ neff → q valu ⇒ nfu →
          qs (app neuf valu) ⇒ (app neff nfu)


-- norm : Tm Γ A → Nf Γ A
data norm_⇒_ : {Γ : Con} {A : Ty} (u : Tm Γ A) → Nf u → Set where
  -- norm u = quote (eval u id)
  eval-quote : {Γ : Con} {A : Ty} {u : Tm Γ A} {valu : Val u} {nfu : Nf u} →
               eval u > idenv ⇒ (tr Val ([id] ⁻¹) valu) → q valu ⇒ nfu →
               norm u ⇒ nfu



-- In the big annoying technical lemmas serie: all computation can be weakened below a context.
postulate
  evalwk : {Γ Δ : Con} {A : Ty} {ρ : Tms Γ Δ} {u : Tm Δ A} {envρ : Env ρ}
           {valu : Val (u [ ρ ])} →
           eval u > envρ ⇒ valu → (B : Ty) →
           eval u > (envρ +E B) ⇒ tr Val ([][] ⁻¹) (valu +V B)
  evalswk : {Γ Δ Θ : Con} {ρ : Tms Γ Δ} {σ : Tms Δ Θ} {envρ : Env ρ}
            {envσρ : Env (σ ∘ ρ)} →
            evals σ > envρ ⇒ envσρ → (B : Ty) →
            evals σ > (envρ +E B) ⇒ tr Env ∘∘ (envσρ +E B)
  $wk : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} {u : Tm Γ A}
        {valf : Val f} {valu : Val u} {valfu : Val (f $ u)} →
        valf $ valu ⇒ valfu → (B : Ty) →
        (valf +V B) $ (valu +V B) ⇒ tr Val $[] (valfu +V B)
  qwk : {Γ : Con} {A : Ty} {u : Tm Γ A} {valu : Val u} {nfu : Nf u} →
        q valu ⇒ nfu → (B : Ty) →
        q (valu +V B) ⇒ (nfu +N B)
  qswk : {Γ : Con} {A : Ty} {u : Tm Γ A} {nevu : Ne Val u} {nefu : Ne Nf u} →
         qs nevu ⇒ nefu → (B : Ty) →
         qs (nevu +NV B) ⇒ (nefu +NN B)
  normwk : {Γ : Con} {A : Ty} {u : Tm Γ A} {nfu : Nf u} →
           norm u ⇒ nfu → (B : Ty) →
           norm (u + B) ⇒ (nfu +N B)
