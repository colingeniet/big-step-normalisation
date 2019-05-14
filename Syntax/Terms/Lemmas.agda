{-# OPTIONS --safe --cubical #-}

module Syntax.Terms.Lemmas where

open import Library.Equality
open import Syntax.Terms

-- Interaction between projections and composition.
π₁∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₁ (σ ∘ ν) ≡ (π₁ σ) ∘ ν
π₁∘ {σ = σ} {ν} =
  π₁ (σ ∘ ν)                    ≡⟨ ap (λ σ → π₁ (σ ∘ ν)) πη ⁻¹ ⟩
  π₁ ((π₁ σ , π₂ σ) ∘ ν)         ≡⟨ ap π₁ ,∘ ⟩
  π₁ ((π₁ σ) ∘ ν , (π₂ σ) [ ν ]) ≡⟨ π₁β ⟩
  (π₁ σ) ∘ ν                    ∎

π₂∘ : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₂ (σ ∘ ν) ≡ (π₂ σ) [ ν ]
π₂∘ {σ = σ} {ν} =
  π₂ (σ ∘ ν)                    ≡⟨ ap (λ σ → π₂ (σ ∘ ν)) πη ⁻¹ ⟩
  π₂ ((π₁ σ , π₂ σ) ∘ ν)         ≡⟨ ap π₂ ,∘ ⟩
  π₂ ((π₁ σ) ∘ ν , (π₂ σ) [ ν ]) ≡⟨ π₂β ⟩
  (π₂ σ) [ ν ]                  ∎


-- Applying id or ∘ to a term behaves as expected.
[id] : {Γ : Con} {A : Ty} {u : Tm Γ A} → u [ id ] ≡ u
[id] {u = u} =
  u [ id ]                ≡⟨ π₂β {σ = id} ⁻¹ ⟩
  π₂ (id , u [ id ])      ≡⟨ ap (λ ν → π₂ (ν , u [ id ])) id∘ ⁻¹ ⟩
  π₂ (id ∘ id , u [ id ]) ≡⟨ ap π₂ ,∘ ⁻¹ ⟩
  π₂ ((id , u) ∘ id)      ≡⟨ ap π₂ ∘id ⟩
  π₂ (id , u)             ≡⟨ π₂β ⟩
  u                      ∎

[][] : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Θ A} →
       u [ σ ∘ ν ] ≡ u [ σ ] [ ν ]
[][] {σ = σ} {ν} {u} =
  u [ σ ∘ ν ]                     ≡⟨ π₂β {σ = σ ∘ ν} ⁻¹ ⟩
  π₂ (σ ∘ ν , u [ σ ∘ ν ])        ≡⟨ ap (λ ρ → π₂ (ρ , u [ σ ∘ ν ])) id∘ ⁻¹ ⟩
  π₂ (id ∘ (σ ∘ ν) , u [ σ ∘ ν ]) ≡⟨ ap π₂ ,∘ ⁻¹ ⟩
  π₂ ((id , u) ∘ (σ ∘ ν))         ≡⟨ ap π₂ ∘∘ ⁻¹ ⟩
  π₂ (((id , u) ∘ σ) ∘ ν)         ≡⟨ π₂∘ ⟩
  (π₂ ((id , u) ∘ σ)) [ ν ]       ≡⟨ ap (λ x → x [ ν ]) π₂∘ ⟩
  (π₂ (id , u)) [ σ ] [ ν ]       ≡⟨ ap (λ u → u [ σ ] [ ν ]) π₂β ⟩
  u [ σ ] [ ν ]                  ∎

-- Lifting the identity yields the identity.
↑id : {Γ : Con} {A : Ty} → _↑_ {Γ = Γ} id A ≡ id
↑id =
  id ∘ wk , vz ≡⟨ ap (λ σ → σ , vz) id∘ ⟩
  wk , vz      ≡⟨ πη ⟩
  id           ∎

-- Applying a substitution to the variable 0 gives the last element of thereof.
vz[,] : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → vz [ σ , u ] ≡ u
vz[,] {σ = σ} {u} =
  (π₂ id) [ σ , u ] ≡⟨ π₂∘ ⁻¹ ⟩
  π₂ (id ∘ (σ , u)) ≡⟨ ap π₂ id∘ ⟩
  π₂ (σ , u)        ≡⟨ π₂β ⟩
  u                ∎

-- Particular case.
vz[<>] : {Γ : Con} {A : Ty} {u : Tm Γ A} → vz [ < u > ] ≡ u
vz[<>] = vz[,]

-- Postcomposing with a weakening simply forgets the last element.
wk, : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} → wk ∘ (σ , u) ≡ σ
wk, {σ = σ} {u} =
  (π₁ id) ∘ (σ , u) ≡⟨ π₁∘ ⁻¹ ⟩
  π₁ (id ∘ (σ , u)) ≡⟨ ap π₁ id∘ ⟩
  π₁ (σ , u)        ≡⟨ π₁β ⟩
  σ                ∎

-- Composition followed by extension is the same as extension followed
-- by composition up to a lifting.
↑∘, : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ (ν , u) ≡ (σ ∘ ν) , u
↑∘, {σ = σ} {ν} {u} =
  (σ ∘ wk , vz) ∘ (ν , u)           ≡⟨ ,∘ ⟩
  (σ ∘ wk) ∘ (ν , u) , vz [ ν , u ] ≡⟨ ap (λ x → (σ ∘ wk) ∘ (ν , u) , x) vz[,] ⟩
  (σ ∘ wk) ∘ (ν , u) , u            ≡⟨ ap (λ ρ → ρ , u) ∘∘ ⟩
  σ ∘ (wk ∘ (ν , u)) , u            ≡⟨ ap (λ ρ → σ ∘ ρ , u) wk, ⟩
  σ ∘ ν , u                         ∎


-- This version of the previous lemma proves to be particularly usefull.
↑∘<> : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {u : Tm Γ A} →
      (σ ↑ A) ∘ < u > ≡ σ , u
↑∘<> {A = A} {σ} {u} =
  (σ ↑ A) ∘ (id , u) ≡⟨ ↑∘, ⟩
  (σ ∘ id) , u       ≡⟨ ap (λ σ → σ , u) ∘id ⟩
  σ , u              ∎


-- Interaction between application and substitution.
[]app : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ Δ} →
        app (f [ σ ]) ≡ (app f) [ σ ↑ A ]
[]app {A = A} {f = f} {σ} =
  app (f [ σ ])                 ≡⟨ ap (λ x → app (x [ σ ])) η ⁻¹ ⟩
  app ((lam (app f)) [ σ ])     ≡⟨ ap app lam[] ⟩
  app (lam ((app f) [ σ ↑ A ])) ≡⟨ β ⟩
  (app f) [ σ ↑ A ]             ∎

app[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {σ : Tms Γ (Δ , A)} →
        (app f) [ σ ] ≡ f [ π₁ σ ] $ π₂ σ
app[] {A = A} {f = f} {σ} =
  app f [ σ ]                      ≡⟨ ap (λ σ → (app f) [ σ ]) πη ⁻¹ ⟩
  app f [ π₁ σ , π₂ σ ]             ≡⟨ ap (λ σ → (app f) [ σ ]) ↑∘<> ⁻¹ ⟩
  app f [ ((π₁ σ) ↑ A) ∘ < π₂ σ > ] ≡⟨ [][] ⟩
  app f [ (π₁ σ) ↑ A ] [ < π₂ σ > ] ≡⟨ ap (λ u → u [ < π₂ σ > ]) []app ⁻¹ ⟩
  app (f [ π₁ σ ]) [ < π₂ σ > ]     ∎

-- Behaviour of classical application through substitution.
$[] : {Γ Δ : Con} {A B : Ty} {f : Tm Δ (A ⟶ B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
      (f $ u) [ σ ] ≡ (f [ σ ]) $ (u [ σ ])
$[] {f = f} {u} {σ} =
  app f [ id , u ] [ σ ]                   ≡⟨ [][] ⁻¹ ⟩
  app f [ (id , u) ∘ σ ]                   ≡⟨ ap (λ σ → app f [ σ ]) ,∘ ⟩
  app f [ id ∘ σ , u [ σ ] ]               ≡⟨ ap (λ ν → app f [ ν , u [ σ ] ]) id∘ ⟩
  app f [ σ , u [ σ ] ]                    ≡⟨ app[] ⟩
  f [ π₁ (σ , u [ σ ]) ] $ π₂ (σ , u [ σ ]) ≡⟨ ap2 (λ ν v → f [ ν ] $ v) π₁β π₂β ⟩
  f [ σ ] $ u [ σ ]                        ∎

-- Applying a λ-closure (i.e. a term of the form (λ u)[ρ]) to something
-- is the same as evaluating the body of the closure in the extended
-- environment.
clos[] : {Γ Δ : Con} {A B : Ty} {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ A} →
         (lam u) [ ρ ] $ v ≡ u [ ρ , v ]
clos[] {A = A} {u = u} {ρ} {v} =
  lam u [ ρ ] $ v       ≡⟨ ap (λ x → x $ v) lam[]  ⟩
  lam (u [ ρ ↑ A ]) $ v ≡⟨ ap (λ x → x [ < v > ]) β ⟩
  u [ ρ ↑ A ] [ < v > ] ≡⟨ [][] ⁻¹ ⟩
  u [ (ρ ↑ A) ∘ < v > ] ≡⟨ ap (λ σ → u [ σ ]) ↑∘<> ⟩
  u [ ρ , v ]           ∎
 
-- Classical β and η conversion rules.
classicβ : {Γ : Con} {A B : Ty} {u : Tm (Γ , A) B} {v : Tm Γ A} →
           lam u $ v ≡ u [ < v > ]
classicβ {u = u} {v} =
  lam u $ v          ≡⟨ ap (λ x → x $ v) [id] ⁻¹ ⟩
  (lam u) [ id ] $ v ≡⟨ clos[] ⟩
  u [ < v > ]        ∎

classicη : {Γ : Con} {A B : Ty} {f : Tm Γ (A ⟶ B)} →
           lam (f [ wk ] $ vz) ≡ f
classicη {A = A} {f = f} =
  lam (f [ wk ] $ vz)  ≡⟨ ap lam app[] ⁻¹ ⟩
  lam ((app f) [ id ]) ≡⟨ ap lam [id] ⟩
  lam (app f)          ≡⟨ η ⟩
  f                    ∎
