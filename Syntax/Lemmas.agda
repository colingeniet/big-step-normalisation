{-# OPTIONS --safe --cubical #-}

module Syntax.Lemmas where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms


abstract
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
      ≅⟨ apd (_[ id ]) (trfill (Tm Γ) ([id]T ⁻¹) u) ⟩
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
      ≅⟨ apd (_[ σ ∘ ν ]) (trfill (Tm Θ) ([id]T ⁻¹) u) ⟩
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
      ≅⟨ ap≅ (_[ ν ]) π₂∘ ⟩'
    π₂ (id , tr (Tm Θ) ([id]T ⁻¹) u) [ σ ] [ ν ]
      ≅⟨ ap≅ (λ x → x [ σ ] [ ν ]) π₂β ⟩'
    tr (Tm Θ) ([id]T ⁻¹) u [ σ ] [ ν ]
      ≅⟨ apd (λ x → x [ σ ] [ ν ]) (trfill (Tm Θ) ([id]T ⁻¹) u) ⁻¹ ⟩
    u [ σ ] [ ν ] ≅∎


  <>∘ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {u : Tm Δ A} →
        < u > ∘ σ ≡ σ , u [ σ ]
  <>∘ {Γ} {Δ} {A} {σ} {u} =
    let p : id ∘ σ ≡ σ
        p = id∘
        q : tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
            ≅[ Tm Γ ] u [ σ ]
        q = tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
              ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⁻¹ ⟩
            tr (Tm Δ) ([id]T ⁻¹) u [ σ ]
              ≅⟨ apd (_[ σ ]) (trfill (Tm Δ) ([id]T ⁻¹) u) ⁻¹ ⟩
            u [ σ ] ≅∎
    in
    < u > ∘ σ ≡⟨ ,∘ ⟩
    id ∘ σ , tr (Tm Γ) ([][]T ⁻¹) (tr (Tm Δ) ([id]T ⁻¹) u [ σ ])
      ≡⟨ (λ i → p i , ≅-to-≡[] isSetTy q {P = ap (A [_]T) p} i) ⟩
    σ , u [ σ ] ∎


  -- Lifting the identity yields the identity.
  ↑id : {Γ : Con} {A : Ty Γ} →
        id ↑ A
        ≅[ (λ Δ → Tms Δ (Γ , A)) ]
        id {Γ , A}
  ↑id {Γ} {A} =
    let P : Γ , A [ id ]T ≡ Γ , A
        P = ap (Γ ,_) [id]T
        Q : (Γ , A [ id ]T ,, A [ id ]T [ wk ]T) ≡ (Γ , A ,, A [ wk ]T)
        Q = apd {B = λ _ → Σ Con Ty} (λ x → Γ , x ,, x [ wk {A = x} ]T) [id]T
        p : id ∘ wk {A = A [ id ]T}
            ≅[ (λ Δ → Tms Δ Γ) ]
            wk {A = A}
        p = id ∘ wk {A = A [ id ]T} ≅⟨ id∘ ⟩
            wk {A = A [ id ]T}      ≅⟨ apd (λ x → wk {A = x}) [id]T ⟩
            wk {A = A} ≅∎
        q : tr (Tm _) ([][]T ⁻¹) (vz {A = A [ id ]T})
            ≅[ (λ (x : Σ Con Ty) → Tm (fst x) (snd x)) ]
            vz {A = A}
        q = tr (Tm _) ([][]T ⁻¹) (vz {A = A [ id ]T})
              ≅⟨ ap (_ ,,_) [][]T ∣ trfill (Tm _) ([][]T ⁻¹) vz ⁻¹ ⟩
            vz {A = A [ id ]T}
              ≅⟨ Q ∣ apd (λ x → vz {A = x}) ([id]T {A = A}) ⟩
            vz {A = A} ≅∎
        p' = ≅-to-≡[] isSetCon p {P = P}
        q' = ≅-to-≡[] (isSetΣ isSetCon isSetTy) q {P = λ i → P i ,, A [ p' i ]T}
    in (id ∘ wk) , tr (Tm _) ([][]T ⁻¹) vz
         ≅⟨ (λ i → p' i , q' i) ⟩
       wk , vz ≅⟨ πη ⟩
       id      ≅∎


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


  -- Some special cases of the previous lemma
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

  ↑∘↑ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
        (σ ↑ A) ∘ (ν ↑ (A [ σ ]T)) ≅[ (λ x → Tms x (Θ , A)) ] (σ ∘ ν) ↑ A
  ↑∘↑ {Γ} {Δ} {Θ} {A} {σ} {ν} =
    let P : A [ σ ]T [ ν ]T ≡ A [ σ ∘ ν ]T
        P = [][]T ⁻¹
        p : Γ Con., A [ σ ]T [ ν ]T ≡ Γ , A [ σ ∘ ν ]T
        p = ap (Γ ,_) P
        q : σ ∘ (ν ∘ (wk {A = A [ σ ]T [ ν ]T}))
            ≡[ ap (λ x → Tms x Θ) p ]≡
            (σ ∘ ν) ∘ (wk {A = A [ σ ∘ ν ]T})
        q = ≅-to-≡[] {B = λ x → Tms x Θ} isSetCon (
            σ ∘ (ν ∘ (wk {A = A [ σ ]T [ ν ]T}))
              ≅⟨ ∘∘ ⁻¹ ⟩
            (σ ∘ ν) ∘ (wk {A = A [ σ ]T [ ν ]T})
              ≅⟨ apd (λ x → (σ ∘ ν) ∘ (wk {A = x})) P ⟩
            (σ ∘ ν) ∘ (wk {A = A [ σ ∘ ν ]T}) ≅∎)
        r : A [ σ ∘ (ν ∘ (wk {A = A [ σ ]T [ ν ]T})) ]T
            ≡[ ap Ty p ]≡
            A [ (σ ∘ ν) ∘ (wk {A = A [ σ ∘ ν ]T}) ]T
        r = apd (A [_]T) q
        s : tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹)
               (tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ]T [ ν ]T}))
            ≅[ (λ (x : Σ Con Ty) → Tm (fst x) (snd x)) ]
            tr (Tm (Γ , A [ σ ∘ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ∘ ν ]T})
        s = tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹)
               (tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ]T [ ν ]T}))
              ≅⟨ ap (_ ,,_) [][]T ∣ trfill (Tm _) ([][]T ⁻¹) _ ⁻¹ ⟩
            tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ]T [ ν ]T})
              ≅⟨ ap (_ ,,_) [][]T ∣ trfill (Tm _) ([][]T ⁻¹) _ ⁻¹ ⟩
            vz {A = A [ σ ]T [ ν ]T}
              ≅⟨ ap (λ x → Γ , x ,, x [ wk {A = x} ]T) P ∣ apd (λ x → vz {A = x}) P ⟩
            vz {A = A [ σ ∘ ν ]T}
              ≅⟨ ap (_ ,,_) [][]T ⁻¹ ∣ trfill (Tm _) ([][]T ⁻¹) _ ⟩
            tr (Tm (Γ , A [ σ ∘ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ∘ ν ]T})
              ≅∎
        t : tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹)
               (tr (Tm (Γ , A [ σ ]T [ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ]T [ ν ]T}))
            ≡[ (λ i → Tm (p i) (r i)) ]≡
            tr (Tm (Γ , A [ σ ∘ ν ]T)) ([][]T ⁻¹) (vz {A = A [ σ ∘ ν ]T})
        t = ≅-to-≡[] (isSetΣ isSetCon isSetTy) s {P = λ i → p i ,, r i}
    in (σ ↑ A) ∘ (ν ↑ (A [ σ ]T))
         ≅⟨ ↑∘, ⟩
       σ ∘ (ν ∘ wk) , tr (Tm _) ([][]T ⁻¹) (tr (Tm _) ([][]T ⁻¹) vz)
         ≅⟨ (λ i → q i , t i) ⟩
       (σ ∘ ν) ∘ wk , tr (Tm _) ([][]T ⁻¹) vz ≅∎


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
    (app f) [ < u > ] [ σ ]               ≅⟨ [][] ≅⁻¹ ⟩'
    (app f) [ < u > ∘ σ ]                 ≅⟨ apd (app f [_]) <>∘ ⟩
    (app f) [ σ , u [ σ ] ]               ≅⟨ apd (app f [_]) ↑∘<> ⁻¹ ⟩
    (app f) [ (σ ↑ A) ∘ < u [ σ ] > ]     ≅⟨ [][] ⟩'
    (app f) [ σ ↑ A ] [ < u [ σ ] > ]     ≅⟨ ap≅ (_[ < u [ σ ] > ]) []app ≅⁻¹ ⟩'
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
