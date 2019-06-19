{-# OPTIONS --cubical --allow-unsolved-meta #-}

module Syntax.Eliminator where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Syntax.Terms
open import Agda.Primitive

{-
-- Type elimination
module Type where
  record Motives {l} : Set (lsuc l) where
    field
      Tyᴹ : (Γ : Con) → Ty Γ → Set l

  record Methods {l} (M : Motives {l}) : Set (lsuc l) where
    open Motives M
    infixl 30 _[_]Tᴹ
    field
      Uᴹ : {Γ : Con} → Tyᴹ Γ U
      Elᴹ : {Γ : Con} (u : Tm Γ U) → Tyᴹ Γ (El u)
      Πᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
           Tyᴹ Γ A → Tyᴹ (Γ , A) B → Tyᴹ Γ (Π A B)
      _[_]Tᴹ : {Γ Δ : Con} {A : Ty Δ} → Tyᴹ Δ A → (σ : Tms Γ Δ) → Tyᴹ Γ (A [ σ ]T)
      [id]Tᴹ : {Γ : Con} {A : Ty Γ} {Aᴹ : Tyᴹ Γ A} → Aᴹ [ id ]Tᴹ ≡[ ap (Tyᴹ Γ) [id]T ]≡ Aᴹ
      [][]Tᴹ : {Γ Δ Θ : Con} {A : Ty Θ} {Aᴹ : Tyᴹ Θ A} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
               Aᴹ [ σ ∘ ν ]Tᴹ ≡[ ap (Tyᴹ Γ) [][]T ]≡ Aᴹ [ σ ]Tᴹ [ ν ]Tᴹ
      U[]ᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} → (Uᴹ {Δ}) [ σ ]Tᴹ ≡[ ap (Tyᴹ Γ) U[] ]≡ Uᴹ {Γ}
      El[]ᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} {u : Tm Δ U} →
              (Elᴹ u) [ σ ]Tᴹ ≡[ ap (Tyᴹ Γ) El[] ]≡ Elᴹ (tr (Tm Γ) U[] (u [ σ ]))
      Π[]ᴹ : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Tms Γ Δ} {Aᴹ : Tyᴹ Δ A} {Bᴹ : Tyᴹ (Δ , A) B} →
             (Πᴹ Aᴹ Bᴹ) [ σ ]Tᴹ ≡[ ap (Tyᴹ Γ) Π[] ]≡ Πᴹ (Aᴹ [ σ ]Tᴹ) (Bᴹ [ σ ↑ A ]Tᴹ)
      isSetTyᴹ : {Γ : Con} {A : Ty Γ} → isSet (Tyᴹ Γ A)

    ⟦_⟧T : {Γ : Con} → (A : Ty Γ) → Tyᴹ Γ A
    ⟦ U ⟧T = Uᴹ
    ⟦ El u ⟧T = Elᴹ u
    ⟦ Π A B ⟧T = Πᴹ ⟦ A ⟧T ⟦ B ⟧T
    ⟦ A [ σ ]T ⟧T = ⟦ A ⟧T [ σ ]Tᴹ
    ⟦ [id]T {A = A} i ⟧T = [id]Tᴹ {Aᴹ = ⟦ A ⟧T} i
    ⟦ [][]T {A = A} {σ} {ν} i ⟧T = [][]Tᴹ {Aᴹ = ⟦ A ⟧T} {σ} {ν} i
    ⟦ U[] i ⟧T = U[]ᴹ i
    ⟦ El[] i ⟧T = El[]ᴹ i
    ⟦ Π[] {A = A} {B} {σ} i ⟧T = Π[]ᴹ {Aᴹ = ⟦ A ⟧T} {Bᴹ = ⟦ B ⟧T} i
    ⟦ isSetTy p q i j ⟧T = isSetDependent2 {B = Tyᴹ _} isSetTy isSetTyᴹ
                                           (λ k → ⟦ p k ⟧T) (λ k → ⟦ q k ⟧T) i j
-}
{-
module Full where
  record Motives {l} : Set (lsuc l) where
    field
      Conᴹ : Con → Set l
      Tyᴹ : {Γ : Con} → Conᴹ Γ → Ty Γ → Set l
      Tmsᴹ : {Γ Δ : Con} → Conᴹ Γ → Conᴹ Δ → Tms Γ Δ → Set l
      Tmᴹ : {Γ : Con} {A : Ty Γ} (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ A → Tm Γ A → Set l

  record Methods {l} (M : Motives {l}) : Set (lsuc l) where
    open Motives M
    infixr 10 _,Cᴹ_ _,ᴹ_
    infixr 20 _∘ᴹ_
    infixl 30 _[_]Tᴹ _[_]ᴹ
    field
      ●ᴹ : Conᴹ ●
      _,Cᴹ_ : {Γ : Con} {A : Ty Γ} → (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ A → Conᴹ (Γ , A)

      Uᴹ : {Γ : Con} → (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ U
      Elᴹ : {Γ : Con} {Γᴹ : Conᴹ Γ} → (u : Tm Γ U)  → Tyᴹ Γᴹ (El u)
      Πᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {Γᴹ : Conᴹ Γ} →
           (Aᴹ : Tyᴹ Γᴹ A) → Tyᴹ (Γᴹ ,Cᴹ Aᴹ) B → Tyᴹ Γᴹ (Π A B)
      _[_]Tᴹ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} →
               Tyᴹ Δᴹ A → Tmsᴹ Γᴹ Δᴹ σ → Tyᴹ Γᴹ (A [ σ ]T)

      idᴹ : {Γ : Con} → (Γᴹ : Conᴹ Γ) → Tmsᴹ Γᴹ Γᴹ id
      _∘ᴹ_ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ν : Tms Γ Δ}
             {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Θᴹ : Conᴹ Θ} →
             Tmsᴹ Δᴹ Θᴹ σ → Tmsᴹ Γᴹ Δᴹ ν → Tmsᴹ Γᴹ Θᴹ (σ ∘ ν)
      εᴹ : {Γ : Con} → (Γᴹ : Conᴹ Γ) → Tmsᴹ Γᴹ ●ᴹ ε
      _,ᴹ_ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)}
             {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Δᴹ A} →
             (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) → Tmᴹ Γᴹ (Aᴹ [ σᴹ ]Tᴹ) u → Tmsᴹ Γᴹ (Δᴹ ,Cᴹ Aᴹ) (σ , u)
      π₁ᴹ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)}
            {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Δᴹ A} →
            Tmsᴹ Γᴹ (Δᴹ ,Cᴹ Aᴹ) σ → Tmsᴹ Γᴹ Δᴹ (π₁ σ)

      _[_]ᴹ : {Γ Δ : Con} {A : Ty Δ} {u : Tm Δ A} {σ : Tms Γ Δ}
              {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Δᴹ A} →
              Tmᴹ Δᴹ Aᴹ u → (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) → Tmᴹ Γᴹ (Aᴹ [ σᴹ ]Tᴹ) (u [ σ ])
      π₂ᴹ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)}
            {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Aᴹ : Tyᴹ Δᴹ A} →
            (σᴹ : Tmsᴹ Γᴹ (Δᴹ ,Cᴹ Aᴹ) σ) → Tmᴹ Γᴹ (Aᴹ [ π₁ᴹ σᴹ ]Tᴹ) (π₂ σ)
      lamᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Tm (Γ , A) B}
             {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ A} {Bᴹ : Tyᴹ (Γᴹ ,Cᴹ Aᴹ) B} →
             Tmᴹ (Γᴹ ,Cᴹ Aᴹ) Bᴹ u → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam u)
      appᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)}
             {Γᴹ : Conᴹ Γ} {Aᴹ : Tyᴹ Γᴹ A} {Bᴹ : Tyᴹ (Γᴹ ,Cᴹ Aᴹ) B} →
             Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) f → Tmᴹ (Γᴹ ,Cᴹ Aᴹ) Bᴹ (app f)

      [id]Tᴹ : {Γ : Con} {A : Ty Γ} {Γᴹ : Conᴹ Γ} (Aᴹ : Tyᴹ Γᴹ A) →
               Aᴹ [ idᴹ Γᴹ ]Tᴹ ≡[ ap (Tyᴹ Γᴹ) [id]T ]≡ Aᴹ
      [][]Tᴹ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ}
               {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} {Θᴹ : Conᴹ Θ}
               (Aᴹ : Tyᴹ Θᴹ A) (σᴹ : Tmsᴹ Δᴹ Θᴹ σ) (νᴹ : Tmsᴹ Γᴹ Δᴹ ν) →
               Aᴹ [ σᴹ ∘ᴹ νᴹ ]Tᴹ ≡[ ap (Tyᴹ Γᴹ) [][]T ]≡ Aᴹ [ σᴹ ]Tᴹ [ νᴹ ]Tᴹ
      U[]ᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) →
             Uᴹ Δᴹ [ σᴹ ]Tᴹ ≡[ ap (Tyᴹ Γᴹ) U[] ]≡ Uᴹ Γᴹ
      El[]ᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} {u : Tm Δ U}
              {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ} (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) →
              (Elᴹ u) [ σᴹ ]Tᴹ ≡[ ap (Tyᴹ Γᴹ) El[] ]≡ Elᴹ (tr (Tm _) U[] (u [ σ ]))
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
-}

module Proposition where
  -- If the codomain of the function (the motives) is a mere proposition,
  -- the eliminator becomes simpler as one needs not to provide any path constructor.
  record Motives {l} : Set (lsuc l) where
    field
      Tmsᴹ : {Γ Δ : Con} → Tms Γ Δ → Set l
      Tmᴹ : {Γ : Con} {A : Ty Γ} → Tm Γ A → Set l

    term-motive : {i : term-index} (u : term i) → Set l
    term-motive {Ty-i Γ} _ = ⊤l
    term-motive {Tms-i Γ Δ} = Tmsᴹ
    term-motive {Tm-i Γ A} = Tmᴹ

  record Methods {l} (M : Motives {l}) : Set (lsuc l) where
    open Motives M
    infixr 10 _,ᴹ_
    infixr 20 _∘ᴹ_
    infixl 30 _[_]ᴹ
    field
      idᴹ : {Γ : Con} → Tmsᴹ (id {Γ})
      _∘ᴹ_ : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
             Tmsᴹ σ → Tmsᴹ ν → Tmsᴹ (σ ∘ ν)
      εᴹ : {Γ : Con} → Tmsᴹ (ε {Γ})
      _,ᴹ_ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
             Tmsᴹ σ → Tmᴹ u → Tmsᴹ (σ , u)
      π₁ᴹ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)} →
            Tmsᴹ σ → Tmsᴹ (π₁ σ)
      _[_]ᴹ : {Γ Δ : Con} {A : Ty Δ} {u : Tm Δ A} {σ : Tms Γ Δ} →
              Tmᴹ u → Tmsᴹ σ → Tmᴹ (u [ σ ])
      π₂ᴹ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)} →
            Tmsᴹ σ → Tmᴹ (π₂ σ)
      lamᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Tm (Γ , A) B} →
             Tmᴹ u → Tmᴹ (lam u)
      appᴹ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)} →
             Tmᴹ f → Tmᴹ (app f)

      isPropTmsᴹ : {Γ Δ : Con} {σ : Tms Γ Δ} → isProp (Tmsᴹ σ)
      isPropTmᴹ : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → isProp (Tmᴹ u)


    {- Just like the definition of terms, the eliminator function is made 
       non mutually inductive to avoid some mutual dependency problems.
    -}
    termᴹ : {i : term-index} (u : term i) → term-motive u

    termᴹ {i = Ty-i _} _ = tt

    termᴹ (u [ σ ]) = (termᴹ u) [ termᴹ σ ]ᴹ
    termᴹ (π₂ σ) = π₂ᴹ (termᴹ σ)
    termᴹ (lam u) = lamᴹ (termᴹ u)
    termᴹ (app f) = appᴹ (termᴹ f)

    termᴹ id = idᴹ
    termᴹ (σ ∘ ν) = (termᴹ σ) ∘ᴹ (termᴹ ν)
    termᴹ ε = εᴹ
    termᴹ (σ , u) = (termᴹ σ) ,ᴹ (termᴹ u)
    termᴹ (π₁ σ) = π₁ᴹ (termᴹ σ)

    termᴹ (id∘ {σ = σ} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (id∘ {σ = σ}) (idᴹ ∘ᴹ termᴹ σ) (termᴹ σ) i
    termᴹ (∘id {σ = σ} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (∘id {σ = σ}) (termᴹ σ ∘ᴹ idᴹ) (termᴹ σ) i
    termᴹ (∘∘ {σ = σ} {ν = ν} {δ = δ} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (∘∘ {σ = σ} {ν = ν} {δ = δ})
                      ((termᴹ σ ∘ᴹ termᴹ ν) ∘ᴹ termᴹ δ)
                      (termᴹ σ ∘ᴹ (termᴹ ν ∘ᴹ termᴹ δ)) i
    termᴹ (εη {σ = σ} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (εη {σ = σ}) (termᴹ σ) εᴹ i
    termᴹ (π₁β {σ = σ} {u = u} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (π₁β {σ = σ} {u = u})
                      (π₁ᴹ (termᴹ σ ,ᴹ termᴹ u))
                      (termᴹ σ) i
    termᴹ (π₂β' {A = A} {σ = σ} {u = u} i) =
      let p : π₂ (σ , u) ≡[ ap (λ x → Tm _ (A [ x ]T)) π₁β ]≡ u
          p = ≅-to-≡[] isSetTy π₂β
          q : π₂ᴹ (termᴹ σ ,ᴹ termᴹ u) ≡[ apd Tmᴹ p ]≡ termᴹ u
          q = isPropPath {B = λ i → Tmᴹ (p i)} isPropTmᴹ
                         (π₂ᴹ (termᴹ σ ,ᴹ termᴹ u)) (termᴹ u)
          r : π₂ᴹ (termᴹ σ ,ᴹ termᴹ u) ≅[ Tmᴹ ] termᴹ (tr (λ x → Tm _ (A [ x ]T)) (π₁β ⁻¹) u)
          r = {!!}
          s : termᴹ (π₂ (σ , u)) ≡[ ap Tmᴹ π₂β' ]≡ termᴹ (tr (λ x → Tm _ (A [ x ]T)) (π₁β ⁻¹) u)
          s = ≅-to-≡[] {B = Tmᴹ} isSetTm r {P = π₂β'}
      in {!s i!}
    termᴹ (πη {σ = σ} i) =
      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (πη {σ = σ}) (π₁ᴹ (termᴹ σ) ,ᴹ π₂ᴹ (termᴹ σ)) (termᴹ σ) i
    termᴹ (,∘ {σ = σ} {ν = ν} {u = u} i) = {!!}
{-      isPropDependent {B = Tmsᴹ} isPropTmsᴹ
                      (,∘ {σ = σ} {ν = ν} {u = u})
                      ((termᴹ σ ,ᴹ termᴹ u) ∘ᴹ termᴹ ν)
                      ((termᴹ σ ∘ᴹ termᴹ ν) ,ᴹ (termᴹ u [ termᴹ ν ]ᴹ)) i-}
    termᴹ (β {u = u} i) =
      isPropDependent {B = Tmᴹ} isPropTmᴹ
                      (β {u = u}) (appᴹ (lamᴹ (termᴹ u))) (termᴹ u) i
    termᴹ (η {f = f} i) =
      isPropDependent {B = Tmᴹ} isPropTmᴹ
                      (η {f = f}) (lamᴹ (appᴹ (termᴹ f))) (termᴹ f) i
    termᴹ (lam[]' {u = u} {σ = σ} i) = {!!}
{-      isPropDependent {B = Tmᴹ} isPropTmᴹ
                      (lam[] {u = u} {σ = σ})
                      ((lamᴹ (termᴹ u)) [ termᴹ σ ]ᴹ)
                      (lamᴹ ((termᴹ u) [ termᴹ σ ∘ᴹ π₁ᴹ idᴹ ,ᴹ π₂ᴹ idᴹ ]ᴹ)) i-}

    termᴹ (isSetTm p q i j) =
      isSetDependent2 {B = Tmᴹ} isSetTm (PropisSet isPropTmᴹ)
                       (λ k → termᴹ (p k)) (λ k → termᴹ (q k)) i j
    termᴹ (isSetTms p q i j) =
      isSetDependent2 {B = Tmsᴹ} isSetTms (PropisSet isPropTmsᴹ)
                       (λ k → termᴹ (p k)) (λ k → termᴹ (q k)) i j


    -- And the nicer looking version of the previous function.
    elimTm : {Γ : Con} {A : Ty Γ} (u : Tm Γ A) → Tmᴹ u
    elimTm u = termᴹ u

    elimTms : {Γ Δ : Con} (σ : Tms Γ Δ) → Tmsᴹ σ
    elimTms σ = termᴹ σ
