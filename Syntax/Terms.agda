{-# OPTIONS --safe --cubical #-}

{-
  Term and substitution definitions for the simply typed λ-calculus with
  explicit substitutions.
-}

module Syntax.Terms where

open import Library.Equality
open import Library.Sets
open import Library.Maybe
open import Library.Negation
open import Library.NotEqual

---- Terms Definition.
{-
  The definition of terms and substitution can not be made with mutually
  inductive types because of constructor dependencies (path constructors
  need to have all regular constructor in scope, which just does not work)
  Making it a simple inductive type with complex indexing solves the problem,
  and with appropriate definitions, it is no harder to use.
-}

data term-index : Set
data Con : Set
data term : term-index → Set

data term-index where
  Ty-i : Con → term-index
  Tm-i : (Γ : Con) → term (Ty-i Γ) → term-index
  Tms-i : Con → Con → term-index

Ty : Con → Set
Ty Γ = term (Ty-i Γ)
Tm : (Γ : Con) → Ty Γ → Set
Tm Γ A = term (Tm-i Γ A)
Tms : Con → Con → Set
Tms Γ Δ = term (Tms-i Γ Δ)


infixl 10 _,_
infixr 20 _∘_
infixl 30 _[_]T _[_]

data Con where
  ● : Con
  _,_ : (Γ : Con) → Ty Γ → Con

data term where
  -- Types.
  U : {Γ : Con} → Ty Γ
  El : {Γ : Con} → Tm Γ U → Ty Γ
  Π : {Γ : Con} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
  _[_]T : {Γ Δ : Con} → Ty Δ → Tms Γ Δ → Ty Γ
  -- Substitutions.
  id : {Γ : Con} → Tms Γ Γ
  _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  ε : {Γ : Con} → Tms Γ ●
  _,_ : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T) → Tms Γ (Δ , A)
  π₁ : {Γ Δ : Con} {A : Ty Δ} → Tms Γ (Δ , A) → Tms Γ Δ
  -- Terms.
  _[_] : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)
  π₂ : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁ σ ]T)
  lam : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Tm Γ (Π A B) → Tm (Γ , A) B
  -- Type laws.
  [id]T : {Γ : Con} {A : Ty Γ} → A [ id ]T ≡ A
  [][]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
          A [ σ ∘ ν ]T ≡ A [ σ ]T [ ν ]T
  U[] : {Γ Δ : Con} {σ : Tms Γ Δ} → U [ σ ]T ≡ U
  El[] : {Γ Δ : Con} {u : Tm Δ U} {σ : Tms Γ Δ} →
         (El u) [ σ ]T ≡ El (tr (Tm Γ) U[] (u [ σ ]))
  Π[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Tms Γ Δ} →
        (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ∘ π₁ id , tr (Tm _) ([][]T ⁻¹) (π₂ id) ]T)
  -- Substitutions laws.
  id∘ : {Γ Δ : Con} {σ : Tms Γ Δ} → id ∘ σ ≡ σ
  ∘id : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ∘ id ≡ σ
  ∘∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {δ : Tms Γ Δ} →
       (σ ∘ ν) ∘ δ ≡ σ ∘ (ν ∘ δ)
  εη : {Γ : Con} {σ : Tms Γ ●} → σ ≡ ε
  π₁β : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
        π₁ (σ , u) ≡ σ
  π₂β' : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
         π₂ (σ , u) ≡ tr (λ x → Tm Γ (A [ x ]T)) (π₁β ⁻¹) u
  πη : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)} → (π₁ σ , π₂ σ) ≡ σ
  ,∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Δ (A [ σ ]T)} →
       (σ , u) ∘ ν ≡ σ ∘ ν , (tr (Tm Γ) ([][]T ⁻¹) (u [ ν ]))
  β : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Tm (Γ , A) B} → app (lam u) ≡ u
  η : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)} → lam (app f) ≡ f
  lam[]' : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {u : Tm (Δ , A) B} {σ : Tms Γ Δ} →
           (lam u) [ σ ]
           ≡ tr (Tm Γ) (Π[] ⁻¹) (lam (u [ σ ∘ (π₁ id) , tr (Tm _) ([][]T ⁻¹) (π₂ id) ]))
  isSetTy : {Γ : Con} → isSet (Ty Γ)
  isSetTm : {Γ : Con} {A : Ty Γ} → isSet (Tm Γ A)
  isSetTms : {Γ Δ : Con} → isSet (Tms Γ Δ)


-- Additional Constructions.
-- Weakening substitution.
wk : {Γ : Con} {A : Ty Γ} → Tms (Γ , A) Γ
wk = π₁ id

-- Variables (De Brujin indices).
vz : {Γ : Con} {A : Ty Γ} → Tm (Γ , A) (A [ wk ]T)
vz = π₂ id
vs : {Γ : Con} {A B : Ty Γ} → Tm Γ A → Tm (Γ , B) (A [ wk ]T)
vs u = u [ wk ]

-- Lifting of substitutions.
_↑_ : {Γ Δ : Con} (σ : Tms Γ Δ) (A : Ty Δ) → Tms (Γ , (A [ σ ]T)) (Δ , A)
σ ↑ A = σ ∘ wk , tr (Tm _) ([][]T ⁻¹) vz

-- Classical application.
<_> : {Γ : Con} {A : Ty Γ} → Tm Γ A → Tms Γ (Γ , A)
< u > = id , tr (Tm _) ([id]T ⁻¹) u

infixl 10 _$_
_$_ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
      Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ < u > ]T)
f $ u = (app f) [ < u > ]


-- Heterogeneous version of dependent path constructors.
π₂β : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
      π₂ (σ , u) ≅[ Tm Γ ] u
π₂β {Γ} {A = A} {σ = σ} {u} =
  π₂ (σ , u)
    ≅⟨ π₂β' ⟩
  tr (λ x → Tm Γ (A [ x ]T)) (π₁β ⁻¹) u
    ≅⟨ trfill (λ x → Tm Γ (A [ x ]T)) (π₁β ⁻¹) u ⁻¹ ⟩
  u ≅∎

lam[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {u : Tm (Δ , A) B} {σ : Tms Γ Δ} →
        (lam u) [ σ ] ≅[ Tm Γ ] lam (u [ σ ↑ A ])
lam[] {Γ} {Δ} {A} {B} {u} {σ} =
  (lam u) [ σ ]
    ≅⟨ lam[]' ⟩
  tr (Tm Γ) (Π[] ⁻¹) (lam (u [ σ ↑ A ]))
    ≅⟨ trfill (Tm Γ) (Π[] ⁻¹) _ ⁻¹ ⟩
  lam (u [ σ ↑ A ]) ≅∎

-- alternative version of lam[]'', which is usefull in a few places
lam[]'' : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {u : Tm (Δ , A) B} {σ : Tms Γ Δ} →
          tr (Tm Γ) Π[] ((lam u) [ σ ]) ≡ lam (u [ σ ↑ A ])
lam[]'' {Γ} {Δ} {A} {B} {u} {σ} = ≅-to-≡ isSetTy
  (tr (Tm Γ) Π[] ((lam u) [ σ ]) ≅⟨ trfill (Tm Γ) Π[] _ ⁻¹ ⟩
   (lam u) [ σ ]                 ≅⟨ lam[] ⟩'
   lam (u [ σ ↑ A ])             ≅∎)


abstract
  isSetCon : isSet Con
  isSetCon {●} {●} p q =
    let p≡refl : p ≡ refl
        p≡refl i j = ●η (p j) (λ k → p (j ∧ (1- k))) i
        q≡refl : q ≡ refl
        q≡refl i j = ●η (q j) (λ k → q (j ∧ (1- k))) i
    in p≡refl ∙ q≡refl ⁻¹
    -- The point of this function is that ●η ● p is refl no matter p.
    -- This is similar to the proof of Hedberg theorem.
    where ●η : (Θ : Con) (p : Θ ≡ ●) → Θ ≡ ●
          ●η ● _ = refl
          ●η (_ , _) p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p))
  isSetCon {●} {_ , _} p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
  isSetCon {_ , _} {●} p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊥; (_ , _) → ⊤}) p))
  isSetCon {Γ , A} {Δ , B} p q =
    let p1 : Γ ≡ Δ
        p1 i = π₁C (p i) (λ j → p (i ∧ (1- j)))
        p2 : A ≡[ ap Ty p1 ]≡ B
        p2 i = π₂C (p i) (λ j → p (i ∧ (1- j)))
        q1 : Γ ≡ Δ
        q1 i = π₁C (q i) (λ j → q (i ∧ (1- j)))
        q2 : A ≡[ ap Ty q1 ]≡ B
        q2 i = π₂C (q i) (λ j → q (i ∧ (1- j)))
        p≡p1p2 : p ≡ (λ i → (p1 i) , (p2 i))
        p≡p1p2 i j = πηC (p j) (λ k → p (j ∧ (1- k))) (1- i)
        q≡q1q2 : q ≡ (λ i → (q1 i) , (q2 i))
        q≡q1q2 i j = πηC (q j) (λ k → q (j ∧ (1- k))) (1- i)
        p1≡q1 : p1 ≡ q1
        p1≡q1 = isSetCon {Γ} {Δ} p1 q1
        p2≡q2 : p2 ≡[ ap (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 ]≡ q2
        p2≡q2 = trfill (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 p2
                d∙ isSetDependent {B = Ty} isSetTy (tr (λ p → A ≡[ ap Ty p ]≡ B) p1≡q1 p2) q2
    in p≡p1p2 ∙ (λ i j → p1≡q1 i j , p2≡q2 i j) ∙ q≡q1q2 ⁻¹
    -- Same remark as for the case of ●.
    where π₁C : (Θ : Con) → Θ ≡ Γ , A → Con
          π₁C ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          π₁C (Θ , _) _ = Θ
          π₂C : (Θ : Con) (p : Θ ≡ Γ , A) → Ty (π₁C Θ p)
          π₂C ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          π₂C (_ , C) _ = C
          πηC : (Θ : Con) (p : Θ ≡ Γ , A) → (π₁C Θ p) , (π₂C Θ p) ≡ Θ
          πηC ● p = ⊥-elim (⊤≢⊥ (ap (λ {● → ⊤; (_ , _) → ⊥}) p))
          πηC (Θ , C) _ = refl
