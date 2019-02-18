module Normalisation.NormalForms where

open import Syntax
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Equality


-- Variables, values, normal forms, ... all have this type.
Tm-like : Set₁
Tm-like = (Γ : Con) (A : Ty) → Set
Tms-like : Set₁
Tms-like = (Γ Δ : Con) → Set

infix 60 list
infixr 10 _,_
data list (X : Tm-like) : Tms-like where
  ε : {Γ : Con} → list X Γ ●
  _,_ : {Γ Δ : Con} {A : Ty} → list X Γ Δ → X Γ A → list X Γ (Δ , A)

π₁list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → list X Γ Δ
π₁list (σ , _) = σ
π₂list : {X : Tm-like} {Γ Δ : Con} {A : Ty} → list X Γ (Δ , A) → X Γ A
π₂list (_ , u) = u

-- Variables.
data Var : Tm-like where
  z : {Γ : Con} {A : Ty} → Var (Γ , A) A
  s : {Γ : Con} {A B : Ty} → Var Γ A → Var (Γ , B) A

_++v_ : {Γ : Con} {A : Ty} → Var Γ A → (Δ : Con) → Var (Γ ++ Δ) A
x ++v ● = x
x ++v (Δ , B) = s (x ++v Δ)

-- Neutral forms : a variable applied to terms satisfying P.
-- This is used both for values and normal forms, so here is a generic definition.
data Ne (X : Tm-like) : Tm-like where
  var : {Γ : Con} {A : Ty} → Var Γ A → Ne X Γ A
  app : {Γ : Con} {A B : Ty} → Ne X Γ (A ⟶ B) → X Γ A → Ne X Γ B


data Val : Tm-like

Env : Tms-like
Env = list Val

data Val where
  vlam : {Γ Δ : Con} {A B : Ty} (u : Tm (Δ , A) B) (ρ : Env Γ Δ) → Val Γ (A ⟶ B)
  vneu : {Γ : Con} {A : Ty} → Ne Val Γ A → Val Γ A

data Nf : Tm-like where
  nlam : {Γ : Con} {A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⟶ B)
  nneu : {Γ : Con} → Ne Nf Γ o → Nf Γ o


-- Embeddings.
⌜_⌝v : {Γ : Con} {A : Ty} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

⌜_⌝V : {Γ : Con} {A : Ty} → Val Γ A → Tm Γ A
⌜_⌝NV : {Γ : Con} {A : Ty} → Ne Val Γ A → Tm Γ A
⌜_⌝E : {Γ Δ : Con} → Env Γ Δ → Tms Γ Δ
⌜ vlam u ρ ⌝V = (lam u) [ ⌜ ρ ⌝E ]
⌜ vneu n ⌝V = ⌜ n ⌝NV
⌜ var x ⌝NV = ⌜ x ⌝v
⌜ app n v ⌝NV = ⌜ n ⌝NV $ ⌜ v ⌝V
⌜ ε ⌝E = ε
⌜ ρ , v ⌝E = ⌜ ρ ⌝E , ⌜ v ⌝V

⌜_⌝N : {Γ : Con} {A : Ty} → Nf Γ A → Tm Γ A
⌜_⌝NN : {Γ : Con} {A : Ty} → Ne Nf Γ A → Tm Γ A
⌜ nlam u ⌝N = lam ⌜ u ⌝N
⌜ nneu n ⌝N = ⌜ n ⌝NN
⌜ var x ⌝NN = ⌜ x ⌝v
⌜ app n u ⌝NN = ⌜ n ⌝NN $ ⌜ u ⌝N


-- Weakening for values / environments.
_+V_ : {Γ : Con} {B : Ty} → Val Γ B → (A : Ty) → Val (Γ , A) B
_+NV_ : {Γ : Con} {B : Ty} → Ne Val Γ B → (A : Ty) → Ne Val (Γ , A) B
_+E_ : {Γ Δ : Con} → Env Γ Δ → (A : Ty) → Env (Γ , A) Δ
(vlam u ρ) +V A = vlam u (ρ +E A)
(vneu u) +V A = vneu (u +NV A)
(var x) +NV A   = var (s x)
(app f u) +NV A = app (f +NV A) (u +V A)
ε +E A       = ε
(σ , u) +E A = σ +E A , u +V A


-- Weakening of variables below a context.
varwk : {Γ : Con} (Δ : Con) {B : Ty} → Var (Γ ++ Δ) B → (A : Ty) →
          Var ((Γ , A) ++ Δ) B
varwk ● x A = s x
varwk (Δ , C) z A = z
varwk (Δ , C) (s x) A = s (varwk Δ x A)

-- Weakening for normal forms must be done at an arbitrary position in the context
-- for the induction.
nfgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Nf (Γ ++ Δ) B → (A : Ty) → Nf ((Γ , A) ++ Δ) B
nefgenwk : {Γ : Con} {B : Ty} (Δ : Con) → Ne Nf (Γ ++ Δ) B → (A : Ty) → Ne Nf ((Γ , A) ++ Δ) B
nfgenwk {B = B ⟶ C} Δ (nlam u) A = nlam (nfgenwk (Δ , B) u A)
nfgenwk Δ (nneu u) A = nneu (nefgenwk Δ u A)
nefgenwk Δ (var x) A = var (varwk Δ x A)
nefgenwk Δ (app f u) A = app (nefgenwk Δ f A) (nfgenwk Δ u A)

_+N_ : {Γ : Con} {B : Ty} → Nf Γ B → (A : Ty) → Nf (Γ , A) B
_+NN_ : {Γ : Con} {B : Ty} → Ne Nf Γ B → (A : Ty) → Ne Nf (Γ , A) B
u +N A = nfgenwk ● u A
u +NN A = nefgenwk ● u A

-- Weakening by a context.
_++V_ : {Γ : Con} {A : Ty} → Val Γ A → (Δ : Con) → Val (Γ ++ Δ) A
u ++V ● = u
u ++V (Δ , A) = (u ++V Δ) +V A
_++E_ : {Γ Δ : Con} → Env Γ Δ → (Θ : Con) → Env (Γ ++ Θ) Δ
σ ++E ● = σ
σ ++E (Δ , A) = (σ ++E Δ) +E A
_++NV_ : {Γ : Con} {A : Ty} → Ne Val Γ A → (Δ : Con) → Ne Val (Γ ++ Δ) A
u ++NV ● = u
u ++NV (Δ , A) = (u ++NV Δ) +NV A
_++N_ : {Γ : Con} {A : Ty} → Nf Γ A → (Δ : Con) → Nf (Γ ++ Δ) A
u ++N ● = u
u ++N (Δ , A) = (u ++N Δ) +N A
_++NN_ : {Γ : Con} {A : Ty} → Ne Nf Γ A → (Δ : Con) → Ne Nf (Γ ++ Δ) A
u ++NN ● = u
u ++NN (Δ , A) = (u ++NN Δ) +NN A


-- Embedding commutes with everything as expected.
var≡ : {Γ : Con} {A B : Ty} {x : Var Γ A} → ⌜ s {B = B} x ⌝v ≡ vs ⌜ x ⌝v
var≡ = refl

+V≈ : {Γ : Con} {A B : Ty} {u : Val Γ B} → ⌜ u +V A ⌝V ≈ ⌜ u ⌝V + A
+NV≈ : {Γ : Con} {A B : Ty} {u : Ne Val Γ B} → ⌜ u +NV A ⌝NV ≈ ⌜ u ⌝NV + A
+E≋ : {Γ Δ : Con} {A : Ty} {σ : Env Γ Δ} → ⌜ σ +E A ⌝E ≋ ⌜ σ ⌝E +s A

+V≈ {u = vlam u ρ} = refl≈ [ +E≋ ]≈ ∙≈ [][]
+V≈ {u = vneu n} = +NV≈ {u = n}
+NV≈ {A = A} {u = var x} rewrite var≡ {B = A} {x = x} = refl≈
+NV≈ {u = app n u} = +NV≈ {u = n} $≈ +V≈ {u = u}
                   ∙≈ $[] ≈⁻¹
+E≋ {σ = ε} = εη ≋⁻¹
+E≋ {σ = σ , u} = +E≋ {σ = σ} ,≋ +V≈ {u = u}
                ∙≋ ,∘ ≋⁻¹

π₁E≋ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₁list σ ⌝E ≋ π₁ ⌜ σ ⌝E
π₁E≋ {σ = _ , _} = π₁β ≋⁻¹
π₂E≈ : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} → ⌜ π₂list σ ⌝V ≈ π₂ ⌜ σ ⌝E
π₂E≈ {σ = _ , _} = π₂β ≈⁻¹

π₁+ : {Γ Δ : Con} {A B : Ty} {σ : Env Γ (Δ , A)} → π₁list (σ +E B) ≡ (π₁list σ) +E B
π₁+ {σ = _ , _} = refl
π₂+ : {Γ Δ : Con} {A B : Ty} {σ : Env Γ (Δ , A)} → π₂list (σ +E B) ≡ (π₂list σ) +V B
π₂+ {σ = _ , _} = refl

[]++V : {Γ Δ Θ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Env Γ Δ} →
        vlam u (ρ ++E Θ) ≡ (vlam u ρ) ++V Θ
[]++V {Θ = ●} = refl
[]++V {Θ = Θ , C} {u = u} {ρ = ρ} =
  ap (λ u → u +V C) ([]++V {Θ = Θ} {u = u} {ρ = ρ})

,++E : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Γ Δ} {v : Val Γ A} →
       (ρ , v) ++E Θ ≡ (ρ ++E Θ , v ++V Θ)
,++E {Θ = ●} = refl
,++E {Θ = Θ , B} {ρ = ρ} {v = v} = ap (λ u → u +E B) (,++E {Θ = Θ} {ρ = ρ} {v = v})

++var : {Γ Δ : Con} {A : Ty} {x : Var Γ A} → (var x) ++NV Δ ≡ var (x ++v Δ)
++var {Δ = ●} = refl
++var {Δ = Δ , B} {x = x} = ap (λ u → u +NV B) (++var {Δ = Δ} {x = x})

++VNV : {Γ Δ : Con} {A : Ty} {v : Ne Val Γ A} → (vneu v) ++V Δ ≡ vneu (v ++NV Δ)
++VNV {Δ = ●} = refl
++VNV {Δ = Δ , B} {v = v} = ap (λ u → u +V B) (++VNV {Δ = Δ} {v = v})

-- The identity is an environment.
idenv : {Γ : Con} → Env Γ Γ
idenv {●} = ε
idenv {Γ , A} = idenv +E A , vneu (var z)

idenv≋ : {Γ : Con} → ⌜ idenv {Γ} ⌝E ≋ id
idenv≋ {●} = εη ≋⁻¹
idenv≋ {Γ , A} = (+E≋ ∙≋ (idenv≋ ∘≋ refl≋)) ,≋ refl≈
               ∙≋ ↑id
