{-# OPTIONS --safe --without-K #-}

{-
  Definitions of variables, values, environments and normal forms,
  with associated constructions and basic lemmas.

  Each definition comes with the definition of the embedding into terms,
  and the definition(s) of weakening(s).
-}

module Normalisation.NormalForms where

open import Syntax.Terms
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Equality


-- Variables, values, normal forms, ... all have this type.
Tm-like : Set₁
Tm-like = (Γ : Con) (A : Ty) → Set
Tms-like : Set₁
Tms-like = (Γ Δ : Con) → Set

-- Lifting from Tm-like to Tms-like (it's just a list).
infix 60 list
infixr 10 _,_
data list (X : Tm-like) : Tms-like where
  ε : {Γ : Con} → list X Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → list X Γ Δ → X Γ A → list X Γ (Δ , A)

-- Associated projections.
π₁list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → list X Γ Δ
π₁list (σ , _) = σ
π₂list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → X Γ A
π₂list (_ , u) = u

πηlist : {X : Tm-like} {Γ Δ : Con} {A : Ty} {ρ : list X Γ (Δ , A)} →
         (π₁list ρ , π₂list ρ) ≡ ρ
πηlist {ρ = ρ , u} = refl


-- Variables.
data Var : Tm-like where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

-- Embedding.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

-- 's' is already the weakening of variables by a type.
-- Weakening by a context.
_++v_ : {Γ : Con} {A : Ty} → Var Γ A → (Δ : Con) → Var (Γ ++ Δ) A
x ++v ● = x
x ++v (Δ , B) = s (x ++v Δ)

-- Weakening below a context.
varwk : {Γ : Con} (Δ : Con) {B : Ty} → Var (Γ ++ Δ) B → (A : Ty) →
          Var ((Γ , A) ++ Δ) B
varwk ● x A = s x
varwk (Δ , C) z A = z
varwk (Δ , C) (s x) A = s (varwk Δ x A)



-- Neutral forms : a variable applied to terms satisfying P.
-- This is used both for values and normal forms, hence the general definition.
data Ne (X : Tm-like) : Tm-like where
  var : {Γ : Con} {A : Ty} → Var Γ A → Ne X Γ A
  app : {Γ : Con} {A B : Ty} → Ne X Γ (A ⟶ B) → X Γ A → Ne X Γ B



-- Values and environments (list of values) are mutually defined.
data Val : Tm-like

Env : Tms-like
Env = list Val

-- A value is a λ-closure or a neutral value.
data Val where
  vlam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ (A ⟶ B)
  vneu : {Γ : Con} {A : Ty} → Ne Val Γ A → Val Γ A

-- Embeddings.
⌜_⌝V : {Γ : Con} {A : Ty} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty} → Ne Val Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ
⌜ vlam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ vneu n ⌝V = ⌜ n ⌝NV
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V

-- Weakenings:
-- - below a context.
valgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Val (Γ ++ Δ) B →
           (A : Ty) → Val ((Γ , A) ++ Δ) B
nvgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Val (Γ ++ Δ) B →
          (A : Ty) → Ne Val ((Γ , A) ++ Δ) B
envgenwk : {Γ Θ : Con} (Δ : Con) → Env (Γ ++ Δ) Θ →
           (A : Ty) → Env ((Γ , A) ++ Δ) Θ
valgenwk Δ (vlam u ρ) A = vlam u (envgenwk Δ ρ A)
valgenwk Δ (vneu u) A   = vneu (nvgenwk Δ u A)
nvgenwk Δ (var x) A   = var (varwk Δ x A)
nvgenwk Δ (app f u) A = app (nvgenwk Δ f A) (valgenwk Δ u A)
envgenwk Δ ε A       = ε
envgenwk Δ (σ , u) A = envgenwk Δ σ A , valgenwk Δ u A

-- - simple.
_+V_ : {Γ : Con} {B : Ty} → Val Γ B → (A : Ty) → Val (Γ , A) B
u +V A = valgenwk ● u A
_+NV_ : {Γ : Con} {B : Ty} → Ne Val Γ B → (A : Ty) → Ne Val (Γ , A) B
u +NV A = nvgenwk ● u A
_+E_ : {Γ Δ : Con} → Env Γ Δ → (A : Ty) → Env (Γ , A) Δ
σ +E A = envgenwk ● σ A

-- - by a context
_++V_ : {Γ : Con} {A : Ty} → Val Γ A → (Δ : Con) → Val (Γ ++ Δ) A
u ++V ● = u
u ++V (Δ , A) = (u ++V Δ) +V A
_++E_ : {Γ Δ : Con} → Env Γ Δ → (Θ : Con) → Env (Γ ++ Θ) Δ
σ ++E ● = σ
σ ++E (Δ , A) = (σ ++E Δ) +E A
_++NV_ : {Γ : Con} {A : Ty} → Ne Val Γ A → (Δ : Con) → Ne Val (Γ ++ Δ) A
u ++NV ● = u
u ++NV (Δ , A) = (u ++NV Δ) +NV A

-- Weakening and embedding commute (up to equivalence, of course).
+V≈ : {Γ : Con} {A B : Ty} {u : Val Γ B} → ⌜ u +V A ⌝V ≈ ⌜ u ⌝V + A
+NV≈ : {Γ : Con} {A B : Ty} {u : Ne Val Γ B} → ⌜ u +NV A ⌝NV ≈ ⌜ u ⌝NV + A
+E≋ : {Γ Δ : Con} {A : Ty} {σ : Env Γ Δ} → ⌜ σ +E A ⌝E ≋ ⌜ σ ⌝E +s A

+V≈ {u = vlam u ρ} = refl≈ [ +E≋ ]≈ ∙≈ [][]
+V≈ {u = vneu n} = +NV≈ {u = n}
+NV≈ {A = A} {u = var x} = refl≈
+NV≈ {u = app n u} = +NV≈ {u = n} $≈ +V≈ {u = u}
                   ∙≈ $[] ≈⁻¹
+E≋ {σ = ε} = εη ≋⁻¹
+E≋ {σ = σ , u} = +E≋ {σ = σ} ,≋ +V≈ {u = u}
                ∙≋ ,∘ ≋⁻¹

-- Weakening can be pushed inside a λ-closure.
[]++V : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} →
        vlam u (ρ ++E Θ) ≡ (vlam u ρ) ++V Θ
[]++V {Θ = ●} = refl
[]++V {Θ = Θ , C} {u = u} {ρ = ρ} =
  ap (λ u → u +V C) ([]++V {Θ = Θ} {u = u} {ρ = ρ})

-- Embedding and projections commute.
π₁E≋ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₁list σ ⌝E ≋ π₁ ⌜ σ ⌝E
π₁E≋ {σ = _ , _} = π₁β ≋⁻¹
π₂E≈ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₂list σ ⌝V ≈ π₂ ⌜ σ ⌝E
π₂E≈ {σ = _ , _} = π₂β ≈⁻¹

-- Weakening and projections commute.
π₁+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₁list (envgenwk Δ σ A) ≡ envgenwk Δ (π₁list σ) A
π₁+ {σ = _ , _} = refl
π₂+ : {Γ Δ Θ : Con} {A B : Ty} {σ : Env (Γ ++ Δ) (Θ , B)} →
      π₂list (envgenwk Δ σ A) ≡ valgenwk Δ (π₂list σ) A
π₂+ {σ = _ , _} = refl

-- Weakening and environment extension commute.
,++E : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Γ Δ} {v : Val Γ A} →
       (ρ , v) ++E Θ ≡ (ρ ++E Θ , v ++V Θ)
,++E {Θ = ●} = refl
,++E {Θ = Θ , B} {ρ = ρ} {v = v} = ap (λ u → u +E B) (,++E {Θ = Θ} {ρ = ρ} {v = v})

-- Weakening and constructors commute.
++var : {Γ Δ : Con} {A : Ty} {x : Var Γ A} → (var x) ++NV Δ ≡ var (x ++v Δ)
++var {Δ = ●} = refl
++var {Δ = Δ , B} {x = x} = ap (λ u → u +NV B) (++var {Δ = Δ} {x = x})

++VNV : {Γ Δ : Con} {A : Ty} {v : Ne Val Γ A} → (vneu v) ++V Δ ≡ vneu (v ++NV Δ)
++VNV {Δ = ●} = refl
++VNV {Δ = Δ , B} {v = v} = ap (λ u → u +V B) (++VNV {Δ = Δ} {v = v})


-- The identity environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E A , vneu (var z)

idenv≋ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≋ id
idenv≋ {●} = εη ≋⁻¹
idenv≋ {Γ , A} = (+E≋ ∙≋ (idenv≋ ∘≋ refl≋)) ,≋ refl≈
               ∙≋ ↑id



-- β-normal η-long forms.
-- Note that a neutral normal form is a normal form only if it is of the base
-- type. This forces to η-expand terms 'as much as possible' while keeping a
-- β-normal form.
data Nf : Tm-like where
  nlam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  nneu : {Γ : Con} → Ne Nf Γ o → Nf Γ o

-- Embeddings.
⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty} → Ne Nf Γ A → Tm Γ A
⌜ nlam u ⌝N = lam ⌜ u ⌝N
⌜ nneu n ⌝N = ⌜ n ⌝NN(idenv≋ ∘≋ refl≋)) ,≋ refl≈
               ∙≋ ↑id
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N

-- Weakenings:
-- - below a context.
nfgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Nf (Γ ++ Δ) B → (A : Ty) →
          Nf ((Γ , A) ++ Δ) B
nefgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Nf (Γ ++ Δ) B → (A : Ty) →
           Ne Nf ((Γ , A) ++ Δ) B
nfgenwk {B = B ⟶ C} Δ (nlam u) A = nlam (nfgenwk (Δ , B) u A)
nfgenwk Δ (nneu u) A = nneu (nefgenwk Δ u A)
nefgenwk Δ (var x) A = var (varwk Δ x A)
nefgenwk Δ (app f u) A = app (nefgenwk Δ f A) (nfgenwk Δ u A)

-- - simple.
_+N_ : {Γ : Con} {B : Ty} → Nf Γ B → (A : Ty) → Nf (Γ , A) B
_+NN_ : {Γ : Con} {B : Ty} → Ne Nf Γ B → (A : Ty) → Ne Nf (Γ , A) B
u +N A = nfgenwk ● u A
u +NN A = nefgenwk ● u A

-- - by a context.
_++N_ : {Γ : Con} {A : Ty} → Nf Γ A → (Δ : Con) → Nf (Γ ++ Δ) A
u ++N ● = u
u ++N (Δ , A) = (u ++N Δ) +N A
_++NN_ : {Γ : Con} {A : Ty} → Ne Nf Γ A → (Δ : Con) → Ne Nf (Γ ++ Δ) A
u ++NN ● = u
u ++NN (Δ , A) = (u ++NN Δ) +NN A
