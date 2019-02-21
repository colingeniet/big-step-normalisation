{-# OPTIONS --safe --without-K #-}

module Normalisation.Evaluator where

open import Equality
open import Syntax.Terms
open import Normalisation.NormalForms

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
  evalπ₂ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ} {σρ : Env Γ (Θ , A)} →
           evals σ > ρ ⇒ σρ → eval (π₂ σ) > ρ ⇒ π₂list σρ
  -- eval (lam u) ρ = (lam u) [ ρ ]
  evallam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) →
            eval (lam u) > ρ ⇒ vlam u ρ
  -- eval (app f) (σ , u) = (eval f σ) $ u
  evalapp : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {ρ : Env Γ (Δ , A)} →
            {fρ : Val Γ (A ⟶ B)} {appfρ : Val Γ B} →
            eval f > π₁list ρ ⇒ fρ → fρ $ π₂list ρ ⇒ appfρ →
            eval (app f) > ρ ⇒ appfρ
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
  evalsπ₁ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ρ : Env Γ Δ} {σρ : Env Γ (Θ , A)} →
            evals σ > ρ ⇒ σρ → evals (π₁ σ) > ρ ⇒ π₁list σρ
data _$_⇒_ where
  -- (lam u) [ ρ ] $ v = eval u (ρ , v)
  $lam : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} {v : Val Γ A}
         {uρv : Val Γ B} →  eval u > (ρ , v) ⇒ uρv →
         (vlam u ρ) $ v ⇒ uρv
  -- n $ v = n v
  $app : {Γ : Con} {A B : Ty} (n : Ne Val Γ (A ⟶ B)) (v : Val Γ A) →
         (vneu n) $ v ⇒ vneu (app n v)


-- q : Val Γ A → Nf Γ A
data q_⇒_ : {Γ : Con} {A : Ty} → Val Γ A → Nf Γ A → Set
-- qs : Ne Val Γ Δ → Ne Nf Γ Δ
data qs_⇒_ : {Γ : Con} {A : Ty} → Ne Val Γ A → Ne Nf Γ A → Set

data q_⇒_ where
  -- q (n : o) = qs n
  -- A value of type o must be neutral !
  qo : {Γ : Con} {n : Ne Val Γ o} {nf : Ne Nf Γ o} →
        qs n ⇒ nf → q (vneu n) ⇒ (nneu nf)
  -- q (f : A ⟶ B) = lam (q (f $ vz))
  q⟶ : {Γ : Con} {A B : Ty} {f : Val Γ (A ⟶ B)} {fz : Val (Γ , A) B} {nffvz : Nf (Γ , A) B} →
        (f +V A) $ (vneu (var z)) ⇒ fz → q fz ⇒ nffvz →
        q f ⇒ nlam nffvz
data qs_⇒_ where
  -- qs x ⇒ x
  qsvar : {Γ : Con} {A : Ty} {x : Var Γ A} → qs (var x) ⇒ (var x)
  -- qs (n $ v) ⇒ (qs n) $ (q v)
  qsapp : {Γ : Con} {A B : Ty} {f : Ne Val Γ (A ⟶ B)} {u : Val Γ A}
          {neff : Ne Nf Γ (A ⟶ B)} {nfu : Nf Γ A} →
          qs f ⇒ neff → q u ⇒ nfu →
          qs (app f u) ⇒ (app neff nfu)


-- norm : Tm Γ A → Nf Γ A
data norm_⇒_ : {Γ : Con} {A : Ty} → Tm Γ A → Nf Γ A → Set where
  qeval : {Γ : Con} {A : Ty} {u : Tm Γ A} {v : Val Γ A} {n : Nf Γ A} →
          eval u > idenv ⇒ v → q v ⇒ n → norm u ⇒ n



-- All computations can be weakened.
-- Most general version, for the induction.

evalgenwk : {Γ Δ : Con} {B : Ty} (Ψ : Con) {u : Tm Δ B} {ρ : Env (Γ ++ Ψ) Δ}
            {uρ : Val (Γ ++ Ψ) B} → eval u > ρ ⇒ uρ → (A : Ty) →
            eval u > (envgenwk Ψ ρ A) ⇒ (valgenwk Ψ uρ A)
evalsgenwk : {Γ Δ Θ : Con} (Ψ : Con) {σ : Tms Δ Θ} {ρ : Env (Γ ++ Ψ) Δ}
             {σρ : Env (Γ ++ Ψ) Θ} → evals σ > ρ ⇒ σρ → (A : Ty) →
             evals σ > (envgenwk Ψ ρ A) ⇒ (envgenwk Ψ σρ A)
$genwk : {Γ : Con} {A B : Ty} (Δ : Con) {f : Val (Γ ++ Δ) (A ⟶ B)} {u : Val (Γ ++ Δ) A}
         {fu : Val (Γ ++ Δ) B} → f $ u ⇒ fu → (C : Ty) →
         (valgenwk Δ f C) $ (valgenwk Δ u C) ⇒ (valgenwk Δ fu C)

evalgenwk Δ (eval[] cσ cu) A =
  eval[] (evalsgenwk Δ cσ A) (evalgenwk Δ cu A)
evalgenwk Δ (evalπ₂ {σρ = σρ} cσ) A =
  tr (λ u → eval _ > _ ⇒ u) (π₂+ {σ = σρ}) (evalπ₂ (evalsgenwk Δ cσ A))
evalgenwk Δ (evallam u ρ) A = evallam u (envgenwk Δ ρ A)
evalgenwk Δ (evalapp {ρ = ρ} cf $fρ) A =
  evalapp
  (tr (λ ρ → eval _ > ρ ⇒ _) (π₁+ {σ = ρ} ⁻¹) (evalgenwk Δ cf A))
  (tr (λ v → _ $ v ⇒ _) (π₂+ {σ = ρ} ⁻¹) ($genwk Δ $fρ A))

evalsgenwk Δ evalsid A = evalsid
evalsgenwk Δ (evals∘ cν cσ) A = evals∘ (evalsgenwk Δ cν A) (evalsgenwk Δ cσ A)
evalsgenwk Δ evalsε A = evalsε
evalsgenwk Δ (evals, cσ cu) A = evals, (evalsgenwk Δ cσ A) (evalgenwk Δ cu A)
evalsgenwk Δ (evalsπ₁ {σρ = σρ} cσ) A =
  tr (λ u → evals _ > _ ⇒ u) (π₁+ {σ = σρ}) (evalsπ₁ (evalsgenwk Δ cσ A))

$genwk Δ ($lam cu) A = $lam (evalgenwk Δ cu A)
$genwk Δ ($app n v) A = $app (nvgenwk Δ n A) (valgenwk Δ v A)


qgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Val (Γ ++ Δ) B} {n : Nf (Γ ++ Δ) B} →
         q u ⇒ n → (A : Ty) → q (valgenwk Δ u A) ⇒ (nfgenwk Δ n A)
qsgenwk : {Γ : Con} {B : Ty} (Δ : Con) {u : Ne Val (Γ ++ Δ) B} {n : Ne Nf (Γ ++ Δ) B} →
          qs u ⇒ n → (A : Ty) → qs (nvgenwk Δ u A) ⇒ (nefgenwk Δ n A)

qgenwk Δ (qo qn) A = qo (qsgenwk Δ qn A)
qgenwk Δ (q⟶ {A = A} $f qf) C =
  q⟶ (tr (λ x → x $ _ ⇒ _) (++-+V ⁻¹) ($genwk (Δ , A) $f C))
     (qgenwk (Δ , A) qf C)
  where ++-+V : {Γ Δ : Con} {A B C : Ty} {u : Val (Γ ++ Δ) A} →
                (valgenwk Δ u C) +V B ≡ valgenwk (Δ , B) (u +V B) C
        ++-+NV : {Γ Δ : Con} {A B C : Ty} {u : Ne Val (Γ ++ Δ) A} →
                 (nvgenwk Δ u C) +NV B ≡ nvgenwk (Δ , B) (u +NV B) C
        ++-+E : {Γ Δ Θ : Con} {B C : Ty} {σ : Env (Γ ++ Δ) Θ} →
                (envgenwk Δ σ C) +E B ≡ envgenwk (Δ , B) (σ +E B) C
        ++-+V {u = vlam u ρ} = ap (vlam u) ++-+E
        ++-+V {u = vneu u} = ap vneu ++-+NV
        ++-+NV {u = var x} = refl
        ++-+NV {u = app f u} = ap (λ x → app x _) ++-+NV ∙ ap (λ x → app _ x) ++-+V
        ++-+E {σ = ε} = refl
        ++-+E {σ = σ , u} = ap (λ x → x , _) ++-+E ∙ ap (λ x → _ , x) ++-+V
qsgenwk Δ qsvar A = qsvar
qsgenwk Δ (qsapp qf qu) A = qsapp (qsgenwk Δ qf A) (qgenwk Δ qu A)



-- Those are the lemmas which are actually used later on.
qwk : {Γ : Con} {B : Ty} {u : Val Γ B} {n : Nf Γ B} →
      q u ⇒ n → (A : Ty) → q (u +V A) ⇒ (n +N A)
qwk = qgenwk ●

evalwks : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {ρ : Env Γ Δ} {v : Val Γ A} →
          eval u > ρ ⇒ v → (Θ : Con) → eval u > (ρ ++E Θ) ⇒ (v ++V Θ)
evalwks c ● = c
evalwks c (Θ , A) = evalgenwk ● (evalwks c Θ) A

evalswks : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ρ : Env Γ Δ} {ν : Env Γ Θ} →
          evals σ > ρ ⇒ ν → (Θ : Con) → evals σ > (ρ ++E Θ) ⇒ (ν ++E Θ)
evalswks c ● = c
evalswks c (Θ , A) = evalsgenwk ● (evalswks c Θ) A

qswks : {Γ : Con} {A : Ty} {u : Ne Val Γ A} {n : Ne Nf Γ A} →
        qs u ⇒ n → (Δ : Con) → qs (u ++NV Δ) ⇒ (n ++NN Δ)
qswks qu ● = qu
qswks qu (Δ , A) = qsgenwk ● (qswks qu Δ) A
