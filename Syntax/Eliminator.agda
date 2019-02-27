{-# OPTIONS --cubical --safe #-}

module Syntax.Eliminator where

open import Library.Equality
open import Library.Sets
open import Syntax.Types
open import Syntax.Terms
open import Agda.Primitive


record Motives {l} : Set (lsuc l) where
  field
    Tmᴹ : {Γ : Con} {A : Ty} → Tm Γ A → Set l
    Tmsᴹ : {Γ Δ : Con} → Tms Γ Δ → Set l


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

    isSetTmᴹ : {Γ : Con} {A : Ty} {u v : Tm Γ A} {p : u ≡ v}
               {x : Tmᴹ u} {y : Tmᴹ v} (q r : x ≡[ ap Tmᴹ p ]≡ y) → q ≡ r
    isSetTmsᴹ : {Γ Δ : Con} {σ ν : Tms Γ Δ} {p : σ ≡ ν}
                {x : Tmsᴹ σ} {y : Tmsᴹ ν} (q r : x ≡[ ap Tmsᴹ p ]≡ y) → q ≡ r

  -- The set hypotheses can be generalized to the case where the two
  -- dependent paths lie other two equal paths.
  genisSetTmᴹ : {Γ : Con} {A : Ty} {u v : Tm Γ A} {p q : u ≡ v} (α : p ≡ q)
                {x : Tmᴹ u} {y : Tmᴹ v} (r : x ≡[ ap Tmᴹ p ]≡ y)
                (s : x ≡[ ap Tmᴹ q ]≡ y) →
                r ≡[ ap (λ p → x ≡[ ap Tmᴹ p ]≡ y) α ]≡ s
  genisSetTmᴹ α {x} {y} r s = trfill (λ p → x ≡[ ap Tmᴹ p ]≡ y) α r
                              d∙ isSetTmᴹ _ s

  genisSetTmsᴹ : {Γ Δ : Con} {σ ν : Tms Γ Δ} {p q : σ ≡ ν} (α : p ≡ q)
                 {x : Tmsᴹ σ} {y : Tmsᴹ ν} (r : x ≡[ ap Tmsᴹ p ]≡ y)
                (s : x ≡[ ap Tmsᴹ q ]≡ y) →
                r ≡[ ap (λ p → x ≡[ ap Tmsᴹ p ]≡ y) α ]≡ s
  genisSetTmsᴹ α {x} {y} r s = trfill (λ p → x ≡[ ap Tmsᴹ p ]≡ y) α r
                               d∙ isSetTmsᴹ _ s




{- Just like the definition of terms, the eliminator function is made 
   non mutually inductive to avoid some mutual dependency problems.
-}
termMotives : ∀ {l} (Mo : Motives {l}) {i : term-index} (u : term i) → Set l
termMotives Mo {i = Tm-i Γ A} u = Tmᴹ u
  where open Motives Mo
termMotives Mo {i = Tms-i Γ Δ} σ = Tmsᴹ σ
  where open Motives Mo


elimterm : ∀ {l} {Mo : Motives {l}} (M : Methods Mo) {i : term-index}
             (u : term i) → termMotives Mo u

elimterm M (u [ σ ]) = (elimterm M u) [ elimterm M σ ]ᴹ
  where open Methods M
elimterm M (π₂ σ) = π₂ᴹ (elimterm M σ)
  where open Methods M
elimterm M (lam u) = lamᴹ (elimterm M u)
  where open Methods M
elimterm M (app f) = appᴹ (elimterm M f)
  where open Methods M

elimterm M id = idᴹ
  where open Methods M
elimterm M (σ ∘ ν) = (elimterm M σ) ∘ᴹ (elimterm M ν)
  where open Methods M
elimterm M ε = εᴹ
  where open Methods M
elimterm M (σ , u) = (elimterm M σ) ,ᴹ (elimterm M u)
  where open Methods M
elimterm M (π₁ σ) = π₁ᴹ (elimterm M σ)
  where open Methods M

elimterm {Mo = Mo} M (id∘ {σ = σ} i) = id∘ᴹ (elimterm M σ) i
  where open Methods M
elimterm M (∘id {σ = σ} i) = ∘idᴹ (elimterm M σ) i
  where open Methods M
elimterm M (∘∘ {σ = σ} {ν = ν} {δ = δ} i) =
  ∘∘ᴹ (elimterm M σ) (elimterm M ν) (elimterm M δ) i
  where open Methods M
elimterm M (εη {σ = σ} i) = εηᴹ (elimterm M σ) i
  where open Methods M
elimterm M (π₁β {σ = σ} {u = u} i) = π₁βᴹ (elimterm M σ) (elimterm M u) i
  where open Methods M
elimterm M (π₂β {σ = σ} {u = u} i) = π₂βᴹ (elimterm M σ) (elimterm M u) i
  where open Methods M
elimterm M (πη {σ = σ} i) = πηᴹ (elimterm M σ) i
  where open Methods M
elimterm M (β {u = u} i) = βᴹ (elimterm M u) i
  where open Methods M
elimterm M (η {f = f} i) = ηᴹ (elimterm M f) i
  where open Methods M
elimterm M (lam[] {u = u} {σ = σ} i) = lam[]ᴹ (elimterm M u) (elimterm M σ) i
  where open Methods M
elimterm M (,∘ {σ = σ} {ν = ν} {u = u} i) =
  ,∘ᴹ (elimterm M σ) (elimterm M ν) (elimterm M u) i
  where open Methods M

elimterm {Mo = Mo} M (isSetTm p q i j) =
  genisSetTmᴹ (isSetTm p q)
              (λ k → elimterm M (p k))
              (λ k → elimterm M (q k))
              i j
  where open Methods M
elimterm {Mo = Mo} M (isSetTms p q i j) =
  genisSetTmsᴹ (isSetTms p q)
               (λ k → elimterm M (p k))
               (λ k → elimterm M (q k)) i j
  where open Methods M


-- And the nicer looking version of the previous function.
elimTm : ∀ {l} {Mo : Motives {l}} (M : Methods Mo) {Γ : Con} {A : Ty}
           (u : Tm Γ A) → Motives.Tmᴹ Mo u
elimTm M u = elimterm M u

elimTms : ∀ {l} {Mo : Motives {l}} (M : Methods Mo) {Γ Δ : Con}
            (σ : Tms Γ Δ) → Motives.Tmsᴹ Mo σ
elimTms M σ = elimterm M σ
