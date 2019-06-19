{-# OPTIONS --cubical #-}

module Syntax.Lemmas where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms


abstract
  -- Interaction between projections and composition.
  π₁∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
        π₁ (σ ∘ ν) ≋ (π₁ σ) ∘ ν
  π₁∘ {σ = σ} {ν} =
    π₁ (σ ∘ ν)            ≋⟨ π₁≋ (πη ∘≋ refl≋) ≋⁻¹ ⟩
    π₁ ((π₁ σ , π₂ σ) ∘ ν) ≋⟨ π₁≋ ,∘ ⟩
    π₁ ((π₁ σ) ∘ ν , _)    ≋⟨ π₁β ⟩
    (π₁ σ) ∘ ν            ≋∎

  π₂∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ , A)} {ν : Tms Γ Δ} →
        π₂ (σ ∘ ν) ≈ (π₂ σ) [ ν ]
  π₂∘ {Γ} {A = A} {σ = σ} {ν} =
    π₂ (σ ∘ ν)            ≈⟨ π₂≈ (πη ∘≋ refl≋) ≈⁻¹ ⟩
    π₂ ((π₁ σ , π₂ σ) ∘ ν) ≈⟨ π₂≈ ,∘ ⟩
    π₂ ((π₁ σ) ∘ ν , tr (Tm Γ) ([][]T ⁻¹) (π₂ σ [ ν ]))
      ≈⟨ π₂β ⟩
    tr (Tm Γ) ([][]T ⁻¹) (π₂ σ [ ν ])
      ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) (π₂ σ [ ν ]) ⁻¹ ⟩'
    π₂ σ [ ν ] ≈∎

  -- Applying id or ∘ to a term behaves as expected.
  [id] : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → u [ id ] ≈ u
  [id] {Γ} {A} {u} =
    u [ id ]
      ≈⟨ (λ i → (trfill (Tm Γ) ([id]T ⁻¹) u i) [ id ]) ⟩'
    tr (Tm Γ) ([id]T ⁻¹) u [ id ]
      ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩'
    tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u [ id ])
      ≈⟨ π₂β ≈⁻¹ ⟩
    π₂ (id ∘ id , tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u [ id ]))
      ≈⟨ π₂≈ ,∘ ≈⁻¹ ⟩
    π₂ ((id , tr (Tm Γ) ([id]T ⁻¹) u) ∘ id)
      ≈⟨ π₂≈ ∘id ⟩
    π₂ (id , tr (Tm Γ) ([id]T ⁻¹) u)
      ≈⟨ π₂β ⟩
    tr (Tm Γ) ([id]T ⁻¹) u
      ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩'
    u ≈∎

  [][] : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Θ A} →
         u [ σ ∘ ν ] ≈ u [ σ ] [ ν ]
  [][] {Γ} {Δ} {Θ} {A} {σ = σ} {ν} {u} =
    u [ σ ∘ ν ]
      ≈⟨ (λ i → (trfill (Tm Θ) ([id]T ⁻¹) u i) [ σ ∘ ν ]) ⟩'
    tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ]
      ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩'
    tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ])
      ≈⟨ π₂β {σ = id ∘ (σ ∘ ν)} ≈⁻¹ ⟩
    π₂ (id ∘ σ ∘ ν , tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Θ) ([id]T ⁻¹) u [ σ ∘ ν ]))
      ≈⟨ π₂≈ ,∘ ≈⁻¹ ⟩
    π₂ ((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ ∘ ν)
      ≈⟨ π₂≈ ∘∘ ≈⁻¹ ⟩
    π₂ (((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ) ∘ ν)
      ≈⟨ π₂∘ ⟩
    π₂ ((id , tr (Tm Θ) ([id]T ⁻¹) u) ∘ σ) [ ν ]
      ≈⟨ π₂∘ [ refl≋ ]≈ ⟩
    π₂ (id , tr (Tm Θ) ([id]T ⁻¹) u) [ σ ] [ ν ]
      ≈⟨ π₂β [ refl≋ ]≈ [ refl≋ ]≈ ⟩
    tr (Tm Θ) ([id]T ⁻¹) u [ σ ] [ ν ]
      ≈⟨ (λ i → (trfill (Tm Θ) ([id]T ⁻¹) u (1- i)) [ σ ] [ ν ]) ⟩'
    u [ σ ] [ ν ] ≈∎


  <>∘ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Δ A} →
        < u > ∘ σ ≋ σ , u [ σ ]
  <>∘ {Γ} {Δ} {A} {σ} {u} =
    let p : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ]) ≈ u [ σ ]
        p = tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
              ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩'
            tr (Tm Δ) ([id]T ⁻¹) u [ σ ]
              ≈⟨ (λ i → (trfill (Tm Δ) ([id]T ⁻¹) u (1- i)) [ σ ]) ⟩'
            u [ σ ] ≈∎
    in < u > ∘ σ ≋⟨ ,∘ ⟩
       id ∘ σ , tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
         ≋⟨ id∘ ,≋ p ⟩
       σ , u [ σ ] ≋∎


  -- Lifting the identity yields the identity.
  ↑id : {Γ : Con} {A : Ty Γ} → id ↑ A ≋ id {Γ , A}
  ↑id {Γ} {A} =
    let p : id ∘ wk {A = A [ id ]} ≋ wk {A = A}
        p = id ∘ wk {A = A [ id ]} ≋⟨ id∘ ⟩
            wk {A = A [ id ]}      ≋⟨ (λ i → wk {A = [id]T {A = A} i}) ⟩'
            wk {A = A}             ≋∎
        q : tr (Tm _) ([][]T ⁻¹) (vz {A = A [ id ]}) ≈ vz {A = A}
        q = tr (Tm _) ([][]T ⁻¹) (vz {A = A [ id ]})
              ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⁻¹ ⟩'
            vz {A = A [ id ]} ≈⟨ (λ i → vz {A = [id]T {A = A} i}) ⟩'
            vz {A = A}        ≈∎
    in id ∘ wk {A = A [ id ]} , tr (Tm _) ([][]T ⁻¹) (vz {A = A [ id ]})
         ≋⟨ p ,≋ q ⟩
       wk {A = A} , vz {A = A} ≋⟨ πη ⟩
       id                      ≋∎

  -- Postcomposing with a weakening simply forgets the last element.
  wk, : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ])} →
        wk ∘ (σ , u) ≋ σ
  wk, {σ = σ} {u} =
    (π₁ id) ∘ (σ , u) ≋⟨ π₁∘ ≋⁻¹ ⟩
    π₁ (id ∘ (σ , u)) ≋⟨ π₁≋ id∘ ⟩
    π₁ (σ , u)        ≋⟨ π₁β ⟩
    σ                 ≋∎

  -- Applying a substitution to the variable 0 gives the last element thereof.
  vz[,] : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ])} →
          vz [ σ , u ] ≈ u
  vz[,] {Γ} {Δ} {A} {σ} {u} =
    (π₂ id) [ σ , u ] ≈⟨ π₂∘ ≈⁻¹ ⟩
    π₂ (id ∘ (σ , u)) ≈⟨ π₂≈ id∘ ⟩
    π₂ (σ , u)        ≈⟨ π₂β ⟩
    u                 ≈∎

  -- Particular case.
  vz[<>] : {Γ : Con} {A : Ty Γ} {u : Tm Γ A} → vz [ < u > ] ≈ u
  vz[<>] {Γ} {A} {u} =
    vz [ id , tr (Tm Γ) ([id]T ⁻¹) u ] ≈⟨ vz[,] ⟩
    tr (Tm Γ) ([id]T ⁻¹) u             ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩'
    u                                  ≈∎


  -- Composition followed by extension is the same as extension followed
  -- by composition up to a lifting.
  ↑∘, : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} {u : Tm Γ (A [ σ ] [ ν ])} →
        (σ ↑ A) ∘ (ν , u) ≋ (σ ∘ ν) , tr (Tm Γ) ([][]T ⁻¹) u
  ↑∘, {Γ} {Δ} {Θ} {A} {σ = σ} {ν} {u} =
    let p : (σ ∘ wk) ∘ (ν , u) ≋ σ ∘ ν
        p = (σ ∘ wk) ∘ (ν , u) ≋⟨ ∘∘ ⟩
            σ ∘ (wk ∘ (ν , u)) ≋⟨ refl≋ ∘≋ wk, ⟩
            σ ∘ ν              ≋∎
        q : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) vz [ ν , u ]) ≈ tr (Tm Γ) ([][]T ⁻¹) u
        q = tr (Tm Γ) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) vz [ ν , u ])
              ≈⟨ trfill (Tm _) ([][]T ⁻¹) _ ⁻¹ ⟩'
            tr (Tm _) ([][]T ⁻¹) vz [ ν , u ]
              ≈⟨ (λ i → trfill (Tm _) ([][]T ⁻¹) vz (1- i) [ ν , u ]) ⟩'
            vz [ ν , u ]           ≈⟨ vz[,] ⟩
            u                      ≈⟨ trfill (Tm _) ([][]T ⁻¹) u ⟩'
            tr (Tm Γ) ([][]T ⁻¹) u ≈∎
    in (σ ↑ A) ∘ (ν , u) ≋⟨ ,∘ ⟩
       (σ ∘ wk) ∘ (ν , u) , tr (Tm Γ) ([][]T ⁻¹) ((tr (Tm _) ([][]T ⁻¹) vz) [ ν , u ])
         ≋⟨ p ,≋ q ⟩
       (σ ∘ ν) , tr (Tm Γ) ([][]T ⁻¹) u ≋∎

  -- Some special cases of the previous lemma
  ↑∘<> : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (A [ σ ])} →
        (σ ↑ A) ∘ < u > ≋ σ , u
  ↑∘<> {Γ} {A = A} {σ} {u} =
    let p : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u) ≈ u
        p = tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u)
              ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩'
            tr (Tm Γ) ([id]T ⁻¹) u
              ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) u ⁻¹ ⟩'
            u ≈∎
    in (σ ↑ A) ∘ (id , tr (Tm _) ([id]T ⁻¹) u)
         ≋⟨ ↑∘, ⟩
       (σ ∘ id) , (tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Γ) ([id]T ⁻¹) u))
         ≋⟨ ∘id ,≋ p ⟩
       σ , u ≋∎

  ↑∘↑ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
        (σ ↑ A) ∘ (ν ↑ (A [ σ ])) ≋ (σ ∘ ν) ↑ A
  ↑∘↑ {Γ} {Δ} {Θ} {A} {σ} {ν} =
    let p : σ ∘ (ν ∘ wk {A = A [ σ ] [ ν ]}) ≋ (σ ∘ ν) ∘ wk {A = A [ σ ∘ ν ]}
        p = σ ∘ (ν ∘ wk {A = A [ σ ] [ ν ]}) ≋⟨ ∘∘ ≋⁻¹ ⟩
            (σ ∘ ν) ∘ wk {A = A [ σ ] [ ν ]}
              ≋⟨ (λ i → (σ ∘ ν) ∘ wk {A = [][]T {A = A} {σ} {ν} (1- i)}) ⟩'
            (σ ∘ ν) ∘ wk {A = A [ σ ∘ ν ]}   ≋∎
        q : tr (Tm _) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) (vz {A = A [ σ ] [ ν ]}))
            ≈ tr (Tm _) ([][]T ⁻¹) (vz {A = A [ σ ∘ ν ]})
        q = tr (Tm _) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) vz)
              ≈⟨ trfill (Tm _) ([][]T ⁻¹) _ ⁻¹ ⟩'
            tr (Tm _) ([][]T ⁻¹) vz
              ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⁻¹ ⟩'
            vz {A = A [ σ ] [ ν ]}
              ≈⟨ (λ i → vz {A = [][]T {A = A} {σ} {ν} (1- i)}) ⟩'
            vz {A = A [ σ ∘ ν ]}
              ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⟩'
            tr (Tm _) ([][]T ⁻¹) vz ≈∎
    in (σ ↑ A) ∘ (ν ↑ (A [ σ ])) ≋⟨ ↑∘, ⟩
       σ ∘ ν ∘ wk , tr (Tm _) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) vz)
         ≋⟨ p ,≋ q ⟩
       (σ ∘ ν) ∘ wk , tr (Tm _) ([][]T ⁻¹) vz ≋∎


  -- Interaction between application and substitution.
  []app : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {σ : Tms Γ Δ} →
          app (tr (Tm Γ) Π[] (f [ σ ])) ≈ (app f) [ σ ↑ A ]
  []app {Γ} {Δ} {A} {B} {f} {σ} =
    let p : tr (Tm Γ) Π[] (f [ σ ]) ≈ lam (app f [ σ ↑ A ])
        p = tr (Tm Γ) Π[] (f [ σ ]) ≈⟨ trfill (Tm Γ) Π[] (f [ σ ]) ⁻¹ ⟩'
            f [ σ ]                 ≈⟨ (η ≈⁻¹) [ refl≋ ]≈ ⟩
            lam (app f) [ σ ]       ≈⟨ lam[] ⟩
            lam (app f [ σ ↑ A ])   ≈∎
    in app (tr (Tm Γ) Π[] (f [ σ ])) ≈⟨ app≈ p ⟩
       app (lam ((app f) [ σ ↑ A ])) ≈⟨ β ⟩
       (app f) [ σ ↑ A ]             ≈∎

  app[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {σ : Tms Γ (Δ , A)} →
          (app f) [ σ ] ≈ (tr (Tm Γ) Π[] (f [ π₁ σ ])) $ π₂ σ
  app[] {Γ} {Δ} {A} {B} {f} {σ} =
    (app f) [ σ ]                      ≈⟨ refl≈ [ πη ≋⁻¹ ]≈ ⟩
    (app f) [ π₁ σ , π₂ σ ]             ≈⟨ refl≈ [ ↑∘<> ≋⁻¹ ]≈ ⟩
    (app f) [ (π₁ σ ↑ A) ∘ < π₂ σ > ]   ≈⟨ [][] ⟩
    (app f) [ π₁ σ ↑ A ] [ < π₂ σ > ]   ≈⟨ ([]app ≈⁻¹) [ refl≋ ]≈ ⟩
    (tr (Tm Γ) Π[] (f [ π₁ σ ])) $ π₂ σ ≈∎


  -- Behaviour of classical application through substitution.
  $[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Tm Δ (Π A B)} {u : Tm Δ A} {σ : Tms Γ Δ} →
        (f $ u) [ σ ] ≈ (tr (Tm Γ) Π[] (f [ σ ])) $ (u [ σ ])
  $[] {Γ} {Δ} {A} {B} {f} {u} {σ} =
    (app f) [ < u > ] [ σ ]               ≈⟨ [][] ≈⁻¹ ⟩
    (app f) [ < u > ∘ σ ]                 ≈⟨ refl≈ [ <>∘ ]≈ ⟩
    (app f) [ σ , u [ σ ] ]               ≈⟨ refl≈ [ ↑∘<> ≋⁻¹ ]≈ ⟩
    (app f) [ (σ ↑ A) ∘ < u [ σ ] > ]     ≈⟨ [][] ⟩
    (app f) [ σ ↑ A ] [ < u [ σ ] > ]     ≈⟨ ([]app ≈⁻¹) [ refl≋ ]≈ ⟩
    (tr (Tm Γ) Π[] (f [ σ ])) $ (u [ σ ]) ≈∎

  -- Applying a λ-closure (i.e. a term of the form (λ u)[ρ]) to something
  -- is the same as evaluating the body of the closure in the extended
  -- environment.
  clos[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)}
           {u : Tm (Δ , A) B} {ρ : Tms Γ Δ} {v : Tm Γ (A [ ρ ])} →
           (tr (Tm Γ) Π[] ((lam u) [ ρ ])) $ v ≈ u [ ρ , v ]
  clos[] {Γ} {Δ} {A} {B} {u} {ρ} {v} =
    let p : tr (Tm Γ) Π[] (lam u [ ρ ]) ≈ lam (u [ ρ ↑ A ])
        p = tr (Tm Γ) Π[] (lam u [ ρ ]) ≈⟨ trfill (Tm Γ) Π[] (lam u [ ρ ]) ⁻¹ ⟩'
            lam u [ ρ ]                 ≈⟨ lam[] ⟩
            lam (u [ ρ ↑ A ])           ≈∎
    in (tr (Tm Γ) Π[] ((lam u) [ ρ ])) $ v
         ≈⟨ (app≈ p) [ refl≋ ]≈ ⟩
       lam (u [ ρ ↑ A ]) $ v
         ≈⟨ β [ refl≋ ]≈ ⟩
       u [ ρ ↑ A ] [ < v > ]
         ≈⟨ [][] ≈⁻¹ ⟩
       u [ (ρ ↑ A) ∘ < v > ]
         ≈⟨ refl≈ [ ↑∘<> ]≈ ⟩
       u [ ρ , v ] ≈∎

{-
  -- Classical β and η conversion rules.
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
-}
