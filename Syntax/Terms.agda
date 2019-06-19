{-# OPTIONS --cubical #-}

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
infixr 0 _≈⟨_⟩_ _≋⟨_⟩_ _≈⟨_⟩'_ _≋⟨_⟩'_
infix 1 _≈∎ _≋∎
infix 4 _≈_ _≋_
infixr 6 _∙≈_ _∙≋_
infix 8 _≈⁻¹ _≋⁻¹
infixl 10 _,_ _,≋_
infixr 20 _∘_ _∘≋_
infixl 30 _[_] _[_]' _[_]≈


{-# NO_POSITIVITY_CHECK #-}
data Con : Set
data Ty : Con → Set
data Tms : Con → Con → Set
data Tm : (Γ : Con) → Ty Γ → Set
data _≋_ : {Γ Δ Θ Ψ : Con} → Tms Γ Θ → Tms Δ Ψ → Set
data _≈_ : {Γ Δ : Con} {A : Ty Γ} {B : Ty Δ} → Tm Γ A → Tm Δ B → Set

data Con where
  ● : Con
  _,_ : (Γ : Con) → Ty Γ → Con

Π' : {Γ : Con} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
_[_]' : {Γ Δ : Con} → Ty Δ → Tms Γ Δ → Ty Γ
_↑_ : {Γ Δ : Con} (σ : Tms Γ Δ) (A : Ty Δ) → Tms (Γ , A [ σ ]') (Δ , A)

data Tms where
  id : {Γ : Con} → Tms Γ Γ
  _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  ε : {Γ : Con} → Tms Γ ●
  _,_ : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]') → Tms Γ (Δ , A)
  π₁ : {Γ Δ : Con} {A : Ty Δ} → Tms Γ (Δ , A) → Tms Γ Δ

data Tm where
  _[_] : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]')
  π₂ : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁ σ ]')
  lam : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Tm (Γ , A) B → Tm Γ (Π' A B)
  app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} → Tm Γ (Π' A B) → Tm (Γ , A) B

data Ty where
  U : {Γ : Con} → Ty Γ
  El : {Γ : Con} → Tm Γ U → Ty Γ
  Π : {Γ : Con} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
  _[_] : {Γ Δ : Con} → Ty Δ → Tms Γ Δ → Ty Γ
  [id]T : {Γ : Con} {A : Ty Γ} → A [ id ] ≡ A
  [][]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
          A [ σ ∘ ν ] ≡ A [ σ ] [ ν ]
  U[] : {Γ Δ : Con} {σ : Tms Γ Δ} → U [ σ ]' ≡ U
  El[] : {Γ Δ : Con} {u : Tm Δ U} {σ : Tms Γ Δ} →
         (El u) [ σ ] ≡ El (tr (Tm Γ) U[] (u [ σ ]))
  Π[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Tms Γ Δ} →
        (Π A B) [ σ ] ≡ Π (A [ σ ]') (B [ σ ↑ A ])
  El≈ : {Γ : Con} {u v : Tm Γ U} → u ≈ v → El u ≡ El v
  _[_]≈ : {Γ Δ : Con} {A : Ty Δ} {σ ν : Tms Γ Δ} → σ ≋ ν → A [ σ ] ≡ A [ ν ]
  isSetTy : {Γ : Con} → isSet (Ty Γ)

_[_]' = Ty._[_]
Π' = Π

-- Additional Constructions.
-- Weakening substitution.
wk : {Γ : Con} {A : Ty Γ} → Tms (Γ , A) Γ
wk = π₁ id

-- Variables (De Brujin indices).
vz : {Γ : Con} {A : Ty Γ} → Tm (Γ , A) (A [ wk ])
vz = π₂ id
vs : {Γ : Con} {A B : Ty Γ} → Tm Γ A → Tm (Γ , B) (A [ wk ])
vs u = u [ wk ]

-- Lifting of substitutions.
σ ↑ A = σ ∘ wk , tr (Tm _) ([][]T ⁻¹) vz

data _≋_ where
  refl≋ : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ≋ σ
  _≋⁻¹ : {Γ Δ Θ Ψ : Con} {σ : Tms Γ Δ} {ν : Tms Θ Ψ} → σ ≋ ν → ν ≋ σ
  _∙≋_ : {Γ Δ Θ Ψ Φ Ω : Con} {σ : Tms Γ Δ} {ν : Tms Θ Ψ} {δ : Tms Φ Ω} →
         σ ≋ ν → ν ≋ δ → σ ≋ δ
  _∘≋_ : {Γ Δ Θ Ψ Φ Ω : Con} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {δ : Tms Φ Ω} {ρ : Tms Ψ Φ} →
         σ ≋ δ → ν ≋ ρ → σ ∘ ν ≋ δ ∘ ρ
  _,≋_ : {Γ Δ Θ Ψ : Con} {A : Ty Δ} {B : Ty Ψ} {σ : Tms Γ Δ} {ν : Tms Θ Ψ}
         {u : Tm Γ (A [ σ ])} {v : Tm Θ (B [ ν ])} → σ ≋ ν → u ≈ v → σ , u ≋ ν , v
  π₁≋ : {Γ Δ Θ Ψ : Con} {A : Ty Δ} {B : Ty Ψ} {σ : Tms Γ (Δ , A)} {ν : Tms Θ (Ψ , B)} →
        σ ≋ ν → π₁ σ ≋ π₁ ν
  id∘ : {Γ Δ : Con} {σ : Tms Γ Δ} → id ∘ σ ≋ σ
  ∘id : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ∘ id ≋ σ
  ∘∘ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ν : Tms Δ Θ} {δ : Tms Γ Δ} →
       (σ ∘ ν) ∘ δ ≋ σ ∘ (ν ∘ δ)
  εη : {Γ : Con} {σ : Tms Γ ●} → σ ≋ ε {Γ}
  π₁β : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ])} →
        π₁ (σ , u) ≋ σ
  πη : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ , A)} → (π₁ σ , π₂ σ) ≋ σ
  ,∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Δ (A [ σ ])} →
       (σ , u) ∘ ν ≋ σ ∘ ν , (tr (Tm Γ) ([][]T ⁻¹) (u [ ν ]))

data _≈_ where
  refl≈ : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → u ≈ u
  _≈⁻¹ : {Γ Δ : Con} {A : Ty Γ} {B : Ty Δ} {u : Tm Γ A} {v : Tm Δ B} → u ≈ v → v ≈ u
  _∙≈_ : {Γ Δ Θ : Con} {A : Ty Γ} {B : Ty Δ} {C : Ty Θ} {u : Tm Γ A} {v : Tm Δ B} {w : Tm Θ C} →
         u ≈ v → v ≈ w → u ≈ w
  _[_]≈ : {Γ Δ Θ Ψ : Con} {A : Ty Δ} {B : Ty Ψ} {u : Tm Δ A} {v : Tm Ψ B} {σ : Tms Γ Δ} {ν : Tms Θ Ψ} →
          u ≈ v → σ ≋ ν → u [ σ ] ≈ v [ ν ]
  π₂≈ : {Γ Δ Θ Ψ : Con} {A : Ty Δ} {B : Ty Ψ} {σ : Tms Γ (Δ , A)} {ν : Tms Θ (Ψ , B)} →
        σ ≋ ν → π₂ σ ≈ π₂ ν
  lam≈ : {Γ Δ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C : Ty Δ} {D : Ty (Δ , C)} →
         {u : Tm (Γ , A) B} {v : Tm (Δ , C) D} → u ≈ v → lam u ≈ lam v
  app≈ : {Γ Δ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {C : Ty Δ} {D : Ty (Δ , C)} →
         {u : Tm Γ (Π A B)} {v : Tm Δ (Π C D)} → u ≈ v → app u ≈ app v
  π₂β : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ])} →
        π₂ (σ , u) ≈ u
  β : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Tm (Γ , A) B} → app (lam u) ≈ u
  η : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)} → lam (app f) ≈ f
  lam[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {u : Tm (Δ , A) B} {σ : Tms Γ Δ} →
          (lam u) [ σ ] ≈ lam (u [ σ ↑ A ])
  

-- Equivalence proofs syntax
_≋∎ : {Γ Δ : Con} (σ : Tms Γ Δ) → σ ≋ σ
σ ≋∎ = refl≋ {σ = σ}
_≋⟨_⟩_ : {Γ Δ Θ Ψ Φ Ω : Con} (σ : Tms Γ Δ) {ν : Tms Θ Ψ} {δ : Tms Φ Ω} →
         σ ≋ ν → ν ≋ δ → σ ≋ δ
σ ≋⟨ p ⟩ q = _∙≋_ {σ = σ} p q

_≈∎ : {Γ : Con} {A : Ty Γ} (u : Tm Γ A) → u ≈ u
u ≈∎ = refl≈ {u = u}
_≈⟨_⟩_ : {Γ Δ Θ : Con} {A : Ty Γ} {B : Ty Δ} {C : Ty Θ} (u : Tm Γ A) {v : Tm Δ B} {w : Tm Θ C} →
         u ≈ v → v ≈ w → u ≈ w
u ≈⟨ p ⟩ q = _∙≈_ {u = u} p q

_≋⟨_⟩'_ : {Γ Δ Θ Ψ Φ Ω : Con} (σ : Tms Γ Δ) {ν : Tms Θ Ψ} {δ : Tms Φ Ω} →
          {P : Γ ≡ Θ} {Q : Δ ≡ Ψ} → σ ≡[ ap2 Tms P Q ]≡ ν → ν ≋ δ → σ ≋ δ
σ ≋⟨ p ⟩' q = σ ≋⟨ trd (σ ≋_) p (refl≋ {σ = σ}) ⟩ q

_≈⟨_⟩'_ : {Γ Δ Θ : Con} {A : Ty Γ} {B : Ty Δ} {C : Ty Θ} (u : Tm Γ A) {v : Tm Δ B} {w : Tm Θ C} →
          {P : Γ ≡ Δ} {Q : A ≡[ ap Ty P ]≡ B} → u ≡[ (λ i → Tm (P i) (Q i)) ]≡ v → v ≈ w → u ≈ w
u ≈⟨ p ⟩' q = u ≈⟨ trd (u ≈_) p (refl≈ {u = u}) ⟩ q


-- Classical application.
<_> : {Γ : Con} {A : Ty Γ} → Tm Γ A → Tms Γ (Γ , A)
< u > = id , tr (Tm _) ([id]T ⁻¹) u

infixl 10 _$_
_$_ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
      Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ < u > ])
f $ u = (app f) [ < u > ]


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

