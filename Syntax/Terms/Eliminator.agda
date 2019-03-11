{-# OPTIONS --cubical --safe #-}

module Syntax.Terms.Eliminator where

open import Library.Equality
open import Library.Sets
open import Syntax.Types
open import Syntax.Terms
open import Agda.Primitive


record Motives {l} : Set (lsuc l) where
  field
    Tmᴹ : {Γ : Con} {A : Ty} → Tm Γ A → Set l
    Tmsᴹ : {Γ Δ : Con} → Tms Γ Δ → Set l

  term-motive : {i : term-index} (u : term i) → Set l
  term-motive {i = Tm-i Γ A} u = Tmᴹ u
  term-motive {i = Tms-i Γ Δ} σ = Tmsᴹ σ



record Methods {l} (M : Motives {l}) : Set (lsuc l) where
  open Motives M
  infixr 10 _,ᴹ_
  infixr 20 _∘ᴹ_
  infixl 30 _[_]ᴹ
  field
    _[_]ᴹ : {Γ Δ : Con} {A : Ty} {u : Tm Δ A} {σ : Tms Γ Δ} →
            Tmᴹ u → Tmsᴹ σ → Tmᴹ (u [ σ ])
    π₂ᴹ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} →
          Tmsᴹ σ → Tmᴹ (π₂ σ)
    lamᴹ : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} →
           Tmᴹ u → Tmᴹ (lam u)
    appᴹ : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
           Tmᴹ f → Tmᴹ (app f)
    idᴹ : {Γ : Con} → Tmsᴹ (id {Γ})
    _∘ᴹ_ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
           Tmsᴹ σ → Tmsᴹ ν → Tmsᴹ (σ ∘ ν)
    εᴹ : {Γ : Con} → Tmsᴹ (ε {Γ})
    _,ᴹ_ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
           Tmsᴹ σ → Tmᴹ u → Tmsᴹ (σ , u)
    π₁ᴹ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} →
          Tmsᴹ σ → Tmsᴹ (π₁ σ)
    id∘ᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} (σᴹ : Tmsᴹ σ) →
           idᴹ ∘ᴹ σᴹ ≡[ ap Tmsᴹ id∘ ]≡ σᴹ
    ∘idᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} (σᴹ : Tmsᴹ σ) →
           σᴹ ∘ᴹ idᴹ ≡[ ap Tmsᴹ ∘id ]≡ σᴹ
    ∘∘ᴹ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {δ : Tms Γ Δ}
          (σᴹ : Tmsᴹ σ) (νᴹ : Tmsᴹ ν) (δᴹ : Tmsᴹ δ) →
          (σᴹ ∘ᴹ νᴹ) ∘ᴹ δᴹ ≡[ ap Tmsᴹ ∘∘ ]≡ σᴹ ∘ᴹ (νᴹ ∘ᴹ δᴹ)
    εηᴹ : {Γ : Con} {σ : Tms Γ ●} (σᴹ : Tmsᴹ σ) → σᴹ ≡[ ap Tmsᴹ εη ]≡ εᴹ
    π₁βᴹ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A}
           (σᴹ : Tmsᴹ σ) (uᴹ : Tmᴹ u) → π₁ᴹ (σᴹ ,ᴹ uᴹ) ≡[ ap Tmsᴹ π₁β ]≡ σᴹ
    π₂βᴹ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A}
           (σᴹ : Tmsᴹ σ) (uᴹ : Tmᴹ u) → π₂ᴹ (σᴹ ,ᴹ uᴹ) ≡[ ap Tmᴹ π₂β ]≡ uᴹ
    πηᴹ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ , A)} (σᴹ : Tmsᴹ σ) →
          (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ) ≡[ ap Tmsᴹ πη ]≡ σᴹ
    βᴹ : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} (uᴹ : Tmᴹ u) →
         appᴹ (lamᴹ uᴹ) ≡[ ap Tmᴹ β ]≡ uᴹ
    ηᴹ : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} (fᴹ : Tmᴹ f) →
         lamᴹ (appᴹ fᴹ) ≡[ ap Tmᴹ η ]≡ fᴹ
    lam[]ᴹ : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {σ : Tms Γ Δ}
             (uᴹ : Tmᴹ u) (σᴹ : Tmsᴹ σ) →
             (lamᴹ uᴹ) [ σᴹ ]ᴹ ≡[ ap Tmᴹ lam[] ]≡ lamᴹ (uᴹ [ σᴹ ∘ᴹ (π₁ᴹ idᴹ) ,ᴹ π₂ᴹ idᴹ ]ᴹ)
    ,∘ᴹ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Δ A}
          (σᴹ : Tmsᴹ σ) (νᴹ : Tmsᴹ ν) (uᴹ : Tmᴹ u) →
          (σᴹ ,ᴹ uᴹ) ∘ᴹ νᴹ ≡[ ap Tmsᴹ ,∘ ]≡ σᴹ ∘ᴹ νᴹ ,ᴹ uᴹ [ νᴹ ]ᴹ

    isSetTmᴹ : {Γ : Con} {A : Ty} {u : Tm Γ A} → isSet (Tmᴹ u)
    isSetTmsᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} → isSet (Tmsᴹ σ)



  {- Just like the definition of terms, the eliminator function is made 
     non mutually inductive to avoid some mutual dependency problems.
  -}
  termᴹ : {i : term-index} (u : term i) → term-motive u

  termᴹ (u [ σ ]) = (termᴹ u) [ termᴹ σ ]ᴹ
  termᴹ (π₂ σ) = π₂ᴹ (termᴹ σ)
  termᴹ (lam u) = lamᴹ (termᴹ u)
  termᴹ (app f) = appᴹ (termᴹ f)

  termᴹ id = idᴹ
  termᴹ (σ ∘ ν) = (termᴹ σ) ∘ᴹ (termᴹ ν)
  termᴹ ε = εᴹ
  termᴹ (σ , u) = (termᴹ σ) ,ᴹ (termᴹ u)
  termᴹ (π₁ σ) = π₁ᴹ (termᴹ σ)

  termᴹ (id∘ {σ = σ} i) = id∘ᴹ (termᴹ σ) i
  termᴹ (∘id {σ = σ} i) = ∘idᴹ (termᴹ σ) i
  termᴹ (∘∘ {σ = σ} {ν = ν} {δ = δ} i) =
    ∘∘ᴹ (termᴹ σ) (termᴹ ν) (termᴹ δ) i
  termᴹ (εη {σ = σ} i) = εηᴹ (termᴹ σ) i
  termᴹ (π₁β {σ = σ} {u = u} i) = π₁βᴹ (termᴹ σ) (termᴹ u) i
  termᴹ (π₂β {σ = σ} {u = u} i) = π₂βᴹ (termᴹ σ) (termᴹ u) i
  termᴹ (πη {σ = σ} i) = πηᴹ (termᴹ σ) i
  termᴹ (β {u = u} i) = βᴹ (termᴹ u) i
  termᴹ (η {f = f} i) = ηᴹ (termᴹ f) i
  termᴹ (lam[] {u = u} {σ = σ} i) = lam[]ᴹ (termᴹ u) (termᴹ σ) i
  termᴹ (,∘ {σ = σ} {ν = ν} {u = u} i) =
    ,∘ᴹ (termᴹ σ) (termᴹ ν) (termᴹ u) i

  termᴹ (isSetTm p q i j) =
    isSetDependent2 {B = Tmᴹ} isSetTm isSetTmᴹ
                     (λ k → termᴹ (p k)) (λ k → termᴹ (q k)) i j
  termᴹ (isSetTms p q i j) =
    isSetDependent2 {B = Tmsᴹ} isSetTms isSetTmsᴹ
                     (λ k → termᴹ (p k)) (λ k → termᴹ (q k)) i j


  -- And the nicer looking version of the previous function.
  elimTm : {Γ : Con} {A : Ty} (u : Tm Γ A) → Tmᴹ u
  elimTm u = termᴹ u

  elimTms : {Γ Δ : Con} (σ : Tms Γ Δ) → Tmsᴹ σ
  elimTms σ = termᴹ σ
