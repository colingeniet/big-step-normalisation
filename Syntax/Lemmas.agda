{-# OPTIONS --safe --cubical #-}

module Syntax.Lemmas where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms


-- Interaction between projections and composition.
π₁∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₁ (σ ∘ ν) ≡ (π₁ σ) ∘ ν
π₁∘ {σ = σ} {ν} =
  π₁ (σ ∘ ν)            ≡⟨ ap (λ σ → π₁ (σ ∘ ν)) πη ⁻¹ ⟩
  π₁ ((π₁ σ , π₂ σ) ∘ ν) ≡⟨ ap π₁ ,∘ ⟩
  π₁ ((π₁ σ) ∘ ν , _)    ≡⟨ π₁β ⟩
  (π₁ σ) ∘ ν            ∎

π₂∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
      π₂ (σ ∘ ν) ≅[ Tm Γ ] (π₂ σ) [ ν ]
π₂∘ {Γ} {A = A} {σ = σ} {ν} =
  π₂ (σ ∘ ν)
    ≅⟨ apd (λ σ → π₂ (σ ∘ ν)) πη ⁻¹ ⟩
  π₂ ((π₁ σ , π₂ σ) ∘ ν)
    ≅⟨ apd π₂ ,∘ ⟩
  π₂ ((π₁ σ) ∘ ν , tr (Tm Γ) ([][]T ⁻¹) (π₂ σ [ ν ]))
    ≅⟨ π₂β ⟩'
  tr (Tm Γ) ([][]T ⁻¹) (π₂ σ [ ν ])
    ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩
  π₂ σ [ ν ] ≅∎

-- Applying id or ∘ to a term behaves as expected.
[id] : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → u [ id ] ≅[ Tm Γ ] u
[id] {Γ} {A} {u} =
  u [ id ]
    ≅⟨ apd (λ x → x [ id ]) (trfill (Tm Γ) ([id]T ⁻¹) u) ⟩
  tr (Tm Γ) ([id]T ⁻¹) u [ id ]
    ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩
  tr (Tm Γ) ([][]T ⁻¹)
     (tr (Tm Γ) ([id]T ⁻¹) u [ id ])
    ≅⟨ π₂β ≅⁻¹ ⟩'
  π₂ (id ∘ id ,
      tr (Tm Γ) ([][]T ⁻¹)
         (tr (Tm Γ) ([id]T ⁻¹) u [ id ]))
    ≅⟨ apd π₂ ,∘ ⁻¹ ⟩
  π₂ ((id , tr (Tm Γ) ([id]T ⁻¹) u) ∘ id)
    ≅⟨ apd π₂ ∘id ⟩
  π₂ (id , tr (Tm Γ) ([id]T ⁻¹) u)
    ≅⟨ π₂β ⟩'
  tr (Tm Γ) ([id]T ⁻¹) u
    ≅⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩
  u ≅∎


[][] : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Θ A} →
       u [ σ ∘ ν ] ≅[ Tm Γ ] u [ σ ] [ ν ]
[][] {Γ} {Δ} {Θ} {A} {σ = σ} {ν} {u} =
  u [ σ ∘ ν ]
    ≅⟨ apd (λ x → x [ σ ∘ ν ]) (trfill (Tm Θ) ([id]T ⁻¹) u) ⟩
  tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ]
    ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩
  tr (Tm Γ) ([][]T ⁻¹)
     (tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ])
    ≅⟨ π₂β {σ = id ∘ (σ ∘ ν)} ≅⁻¹ ⟩'
  π₂ (id ∘ σ ∘ ν ,
      tr (Tm Γ) ([][]T ⁻¹)
         (tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ]))
    ≅⟨ apd π₂ ,∘ ⁻¹ ⟩
  π₂ ((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ ∘ ν)
    ≅⟨ apd π₂ ∘∘ ⁻¹ ⟩
  π₂ (((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ) ∘ ν)
    ≅⟨ π₂∘ ⟩'
  π₂ ((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ) [ ν ]
    ≅⟨ ap≅ (λ x → x [ ν ]) π₂∘ ⟩'
  π₂ (id , tr (Tm Θ) ([id]T ⁻¹) u) [ σ ] [ ν ]
    ≅⟨ ap≅ (λ x → x [ σ ] [ ν ]) π₂β ⟩'
  tr (Tm Θ) ([id]T ⁻¹) u [ σ ] [ ν ]
    ≅⟨ apd (λ x → x [ σ ] [ ν ]) (trfill (Tm Θ) ([id]T ⁻¹) u) ⁻¹ ⟩
  u [ σ ] [ ν ] ≅∎

{-
-- Lifting the identity yields the identity.
↑id : {Γ : Con} {A : Ty Γ} → (id {Γ}) ↑ A ≡[ {!!} ]≡ id {Γ , A}
↑id =
  id ∘ wk , vz ≡⟨ ap (λ σ → σ , vz) id∘ ⟩
  wk , vz      ≡⟨ πη ⟩
  id           ∎
-}

-- Postcomposing with a weakening simply forgets the last element.
wk, : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
      wk ∘ (σ , u) ≡ σ
wk, {σ = σ} {u} =
  (π₁ id) ∘ (σ , u) ≡⟨ π₁∘ ⁻¹ ⟩
  π₁ (id ∘ (σ , u)) ≡⟨ ap π₁ id∘ ⟩
  π₁ (σ , u)        ≡⟨ π₁β ⟩
  σ                ∎

-- Applying a substitution to the variable 0 gives the last element of thereof.
vz[,] : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
        vz [ σ , u ] ≅[ Tm Γ ] u
vz[,] {Γ} {Δ} {A} {σ} {u} =
  (π₂ id) [ σ , u ] ≅⟨ π₂∘ ≅⁻¹ ⟩'
  π₂ (id ∘ (σ , u)) ≅⟨ apd π₂ id∘ ⟩
  π₂ (σ , u)        ≅⟨ π₂β ⟩'
  u                ≅∎

-- Particular case.
vz[<>] : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → vz [ < u > ] ≅[ Tm Γ ] u
vz[<>] {Γ} {A} {u} =
  vz [ id , tr (Tm Γ) ([id]T ⁻¹) u ] ≅⟨ vz[,] ⟩'
  tr (Tm Γ) ([id]T ⁻¹) u             ≅⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩
  u                                  ≅∎


-- Composition followed by extension is the same as extension followed
-- by composition up to a lifting.
↑∘, : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ (A [ σ ]T [ ν ]T)} →
      (σ ↑ A) ∘ (ν , u) ≡ (σ ∘ ν) , tr (Tm Γ) ([][]T ⁻¹) u
↑∘, {Γ} {Δ} {Θ} {A} {σ = σ} {ν} {u} =
  let p : (σ ∘ wk) ∘ (ν , u) ≡ σ ∘ ν
      p = (σ ∘ wk) ∘ (ν , u) ≡⟨ ∘∘ ⟩
          σ ∘ (wk ∘ (ν , u)) ≡⟨ ap (λ x → σ ∘ x) wk, ⟩
          σ ∘ ν              ∎
      q : (tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ] ≅[ Tm Γ ] u
      q = tr (Tm _) ([][]T ⁻¹) vz [ ν , u ]
            ≅⟨ apd (λ x → x [ ν , u ]) (trfill (Tm _) ([][]T ⁻¹) vz) ⁻¹ ⟩
          vz [ ν , u ] ≅⟨ vz[,] ⟩'
          u            ≅∎
      q' : tr (Tm Γ) ([][]T ⁻¹)
              ((tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ])
           ≅[ Tm Γ ]
           tr (Tm Γ) ([][]T ⁻¹) u
      q' = tr (Tm Γ) ([][]T ⁻¹)
              ((tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ])
             ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩
           (tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ]
             ≅⟨ q ⟩'
           u
             ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) u ⟩
           tr (Tm Γ) ([][]T ⁻¹) u ≅∎
  in
  (σ ↑ A) ∘ (ν , u)
    ≡⟨ ,∘ ⟩
  (σ ∘ wk) ∘ (ν , u) ,
   tr (Tm Γ) ([][]T ⁻¹)
      ((tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ])
    ≡⟨ (λ i → p i , (≅-to-≡[] isSetTy q' {P = λ i → A [ p i ]T} i)) ⟩
  (σ ∘ ν) , tr (Tm Γ) ([][]T ⁻¹) u ∎


-- This version of the previous lemma proves to be particularly usefull.
↑∘<> : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ]T)} →
      (σ ↑ A) ∘ < u > ≡ σ , u
↑∘<> {Γ} {A = A} {σ} {u} =
  let p : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u) ≅[ Tm Γ ] u
      p =
        tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u)
          ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩
        tr (Tm Γ) ([id]T ⁻¹) u
          ≅⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩
        u ≅∎
  in
  (σ ↑ A) ∘ (id , tr (Tm _) ([id]T ⁻¹) u)
    ≡⟨ ↑∘, ⟩
  (σ ∘ id) , (tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u))
    ≡⟨ (λ i → ∘id i ,
              ≅-to-≡[] isSetTy p {ap (λ x → A [ x ]T) ∘id} i) ⟩
  σ , u ∎


-- Interaction between application and substitution.
[]app : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {σ : Tms Γ Δ} →
        app (tr (Tm Γ) Π[] (f [ σ ])) ≅[ Tm (Γ , A [ σ ]T) ] (app f) [ σ ↑ A ]
[]app {Γ} {Δ} {A} {B} {f} {σ} =
  app (tr (Tm Γ) Π[] (f [ σ ]))
    ≅⟨ ap (λ x → app (tr (Tm Γ) Π[] (x [ σ ]))) (η ⁻¹) ⟩
  app (tr (Tm Γ) Π[] ((lam (app f)) [ σ ]))
    ≅⟨ ap app lam[]'' ⟩
  app (lam ((app f) [ σ ↑ A ]))
    ≅⟨ β ⟩
  (app f) [ σ ↑ A ] ≅∎


app[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {σ : Tms Γ (Δ , A)} →
        (app f) [ σ ] ≅[ Tm Γ ] (tr (Tm Γ) Π[] (f [ π₁ σ ])) $ π₂ σ
app[] {Γ} {Δ} {A} {B} {f} {σ} =
  (app f) [ σ ]                      ≅⟨ apd (λ σ → (app f) [ σ ]) πη ⁻¹ ⟩
  (app f) [ π₁ σ , π₂ σ ]             ≅⟨ apd (λ σ → (app f) [ σ ]) ↑∘<> ⁻¹ ⟩
  (app f) [ (π₁ σ ↑ A) ∘ < π₂ σ > ]   ≅⟨ [][] ⟩'
  (app f) [ π₁ σ ↑ A ] [ < π₂ σ > ]   ≅⟨ ap≅ (λ u → u [ < π₂ σ > ]) []app ≅⁻¹ ⟩'
  (tr (Tm Γ) Π[] (f [ π₁ σ ])) $ π₂ σ ≅∎


-- Behaviour of classical application through substitution.
$[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
      (f $ u) [ σ ] ≅[ Tm Γ ] (tr (Tm Γ) Π[] (f [ σ ])) $ (u [ σ ])
$[] {Γ} {Δ} {A} {B} {f} {u} {σ} =
  let p : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ]) ≅[ Tm Γ ] u [ σ ]
      p = tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
            ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩
          tr (Tm Δ) ([id]T ⁻¹) u [ σ ]
            ≅⟨ apd (λ x → x [ σ ]) (trfill (Tm Δ) ([id]T ⁻¹) u ⁻¹) ⟩
          u [ σ ] ≅∎
  in
  (app f) [ id , tr (Tm Δ) ([id]T ⁻¹) u ] [ σ ]
    ≅⟨ [][] ≅⁻¹ ⟩'
  (app f) [ (id , tr (Tm Δ) ([id]T ⁻¹) u) ∘ σ ]
    ≅⟨ apd (λ x → (app f) [ x ]) ,∘ ⟩
  (app f) [ id ∘ σ , tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ]) ]
    ≅⟨ (λ i → (app f) [ id∘ i , ≅-to-≡[] isSetTy p {P = ap (λ x → A [ x ]T) id∘} i ]) ⟩
  (app f) [ σ , u [ σ ] ]
    ≅⟨ apd (λ σ → (app f) [ σ ]) ↑∘<> ⁻¹ ⟩
  (app f) [ (σ ↑ A) ∘ < u [ σ ] > ]
    ≅⟨ [][] ⟩'
  (app f) [ σ ↑ A ] [ < u [ σ ] > ]
    ≅⟨ ap≅ (λ x → x [ < u [ σ ] > ]) []app ≅⁻¹ ⟩'
  (tr (Tm Γ) Π[] (f [ σ ])) $ (u [ σ ]) ≅∎

-- Applying a λ-closure (i.e. a term of the form (λ u)[ρ]) to something
-- is the same as evaluating the body of the closure in the extended
-- environment.
clos[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
         {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ (A [ ρ ]T)} →
         (tr (Tm Γ) Π[] ((lam u) [ ρ ])) $ v ≅[ Tm Γ ] u [ ρ , v ]
clos[] {Γ} {Δ} {A} {B} {u} {ρ} {v} =
  (tr (Tm Γ) Π[] ((lam u) [ ρ ])) $ v
    ≅⟨ ap (λ x → x $ v) lam[]'' ⟩
  lam (u [ ρ ↑ A ]) $ v
    ≅⟨ ap (λ x → x [ < v > ]) β ⟩
  u [ ρ ↑ A ] [ < v > ]
    ≅⟨ [][] ≅⁻¹ ⟩'
  u [ (ρ ↑ A) ∘ < v > ]
    ≅⟨ apd (λ σ → u [ σ ]) ↑∘<> ⟩
  u [ ρ , v ] ≅∎


-- Classical β and η conversion rules.
{-
classicβ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {u : Tm (Γ , A) B} {v : Tm Γ A} →
           lam u $ v ≡ u [ < v > ]
classicβ {Γ} {A} {B} {u} {v} =
  let p : lam u ≅[ Tm Γ ] tr (Tm Γ) Π[] ((lam u) [ id ])
      p = lam u          ≅⟨ [id] ≅⁻¹ ⟩'
          (lam u) [ id ] ≅⟨ trfill (Tm Γ) Π[] _ ⟩
          tr (Tm Γ) Π[] (lam u [ id ]) ≅∎
  in ≅-to-≡ isSetTy (
  lam u $ v
    ≅⟨ (λ i → (≅-to-≡[] isSetTy p {P = {!!}} i) $ (trfill (Tm Γ) ([id]T ⁻¹) v i)) ⟩
  (tr (Tm Γ) Π[] ((lam u) [ id ])) $ (tr (Tm Γ) ([id]T ⁻¹) v)
    ≅⟨ clos[] ⟩'
  u [ < v > ] ≅∎)
-}

classicη : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)} →
           lam (tr (Tm _) Π[] (f [ wk ]) $ vz) ≅[ Tm Γ ] f
classicη {Γ} {A} {B} {f} =
  lam (tr (Tm _) Π[] (f [ wk ]) $ vz)
    ≅⟨ ap (λ x → lam (tr (Tm _) Π[] (x [ wk ]) $ vz)) η ⁻¹ ⟩
  lam (tr (Tm _) Π[] ((lam (app f)) [ wk ]) $ vz)
    ≅⟨ ap≅ lam clos[] ⟩'
  lam (app f [ wk , vz ])
    ≅⟨ apd (λ x → lam (app f [ x ])) πη ⟩
  lam (app f [ id ])
    ≅⟨ ap≅ lam [id] ⟩'
  lam (app f)
    ≅⟨ η ⟩
  f ≅∎
