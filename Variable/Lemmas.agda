{-# OPTIONS --cubical #-}

module Variable.Lemmas where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Sets
open import Variable.Variable


abstract
  -- Other identities.
  +vwk : {Γ Δ : Con} {A : Ty Δ} {B : Ty Γ} {x : Var Δ A} {σ : Wk Γ Δ} →
         x +v (wkw {A = B} σ) ≅[ Var _ ] s {B = B} (x +v σ)
  +vwk {Γ} {Δ} {A} {B} {z} {σ , y} =
    tr (Var _) []wk,
       (tr (Var _) _ (s y))
      ≅⟨ trfill (Var _) []wk, _ ⁻¹ ⟩
    tr (Var _) _ (s y)
      ≅⟨ trfill (Var _) _ (s y) ⁻¹ ⟩
    s y
      ≅⟨ apd s (trfill (Var _) []wk, y) ⟩
    s (tr (Var _) []wk, y) ≅∎
  +vwk {Γ} {Δ} {A} {B} {s x} {σ , y} =
    tr (Var _) []wk, (x +v (wkw σ))
      ≅⟨ trfill (Var _) []wk, _ ⁻¹ ⟩
    x +v (wkw σ)
      ≅⟨ +vwk {x = x} {σ} ⟩'
    s (x +v σ)
      ≅⟨ apd s (trfill (Var _) []wk, _) ⟩
    s (tr (Var _) []wk, (x +v σ)) ≅∎

  +vid : {Γ : Con} {A : Ty Γ} {x : Var Γ A} → x +v idw ≅[ Var _ ] x
  +vid {x = z} =
    tr (Var _) []wk,
       (tr (Var _) [⌜wkid⌝] z)
      ≅⟨ trfill (Var _) []wk, _ ⁻¹ ⟩
    tr (Var _) [⌜wkid⌝] z
      ≅⟨ trfill (Var _) [⌜wkid⌝] z ⁻¹ ⟩
    z ≅∎
  +vid {x = s x} =
    tr (Var _) []wk, (x +v (wkw idw))
      ≅⟨ trfill (Var _) []wk, (x +v (wkw idw)) ⁻¹ ⟩
    x +v (wkw idw)
      ≅⟨ +vwk {x = x} ⟩'
    s (x +v idw)
      ≅⟨ ap≅ s +vid ⟩'
    s x ≅∎

  +v∘ : {Γ Δ Θ : Con} {A : Ty Θ} {x : Var Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        x +v (σ ∘w ν) ≅[ Var Γ ] (x +v σ) +v ν
  +v∘ {x = z} {σ , y} {ν} =
    tr (Var _) []wk,
       (tr (Var _) _ (y +v ν))
      ≅⟨ trfill (Var _) []wk, _ ⁻¹ ⟩
    tr (Var _) _ (y +v ν)
      ≅⟨ trfill (Var _) _ (y +v ν) ⁻¹ ⟩
    y +v ν
      ≅⟨ apd (λ x → x +v ν) (trfill (Var _) []wk, y) ⟩
    (tr (Var _) []wk, y) +v ν ≅∎
  +v∘ {x = s x} {σ , y} {ν} =
    tr (Var _) []wk, (x +v (σ ∘w ν))
      ≅⟨ trfill (Var _) []wk, _ ⁻¹ ⟩
    x +v (σ ∘w ν)
      ≅⟨ +v∘ {x = x} ⟩'
    (x +v σ) +v ν
      ≅⟨ apd (λ x → x +v ν) (trfill (Var _) []wk, (x +v σ)) ⟩
    (tr (Var _) []wk, (x +v σ)) +v ν ≅∎



  ∘idw : {Γ Δ : Con} {σ : Wk Γ Δ} → σ ∘w idw ≡ σ
  ∘idw {Γ} {●} {ε} = refl
  ∘idw {Γ} {Δ , A} {σ , x} =
    let p : A [ ⌜ σ ⌝w ] [ ⌜ idw ⌝w ] ≡ A [ ⌜ σ ∘w idw ⌝w ]
        p = A [ ⌜ σ ⌝w ] [ ⌜ idw ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ idw ⌝w ]    ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ σ ∘w idw ⌝w ]       ∎
        q : tr (Var _) p (x +v idw) ≅[ Var Γ ] x
        q = tr (Var _) p (x +v idw) ≅⟨ trfill (Var _) p (x +v idw) ⁻¹ ⟩
            x +v idw                ≅⟨ +vid ⟩'
            x                       ≅∎
    in λ i → ∘idw {σ = σ} i , ≅-to-≡[] isSetTy q {P = ap (λ x → A [ ⌜ x ⌝w ]) (∘idw {σ = σ})} i

  ∘∘w : {Γ Δ Θ Ψ : Con} {σ : Wk Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
        (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
  ∘∘w {Ψ = ●} {ε} = refl
  ∘∘w {Γ} {Δ} {Θ} {Ψ , A} {σ , x} {ν} {δ} =
    let p : A [ ⌜ σ ⌝w ] [ ⌜ ν ∘w δ ⌝w ] ≡ A [ ⌜ σ ∘w (ν ∘w δ) ⌝w ]
        p = A [ ⌜ σ ⌝w ] [ ⌜ ν ∘w δ ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ∘w δ ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ σ ∘w (ν ∘w δ) ⌝w ]    ∎
        q : A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡ A [ ⌜ σ ∘w ν ⌝w ]
        q = A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ σ ∘w ν ⌝w ]      ∎
        r : A [ ⌜ σ ∘w ν ⌝w ] [ ⌜ δ ⌝w ] ≡ A [ ⌜ (σ ∘w ν) ∘w δ ⌝w ]
        r = A [ ⌜ σ ∘w ν ⌝w ] [ ⌜ δ ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ∘w ν ⌝w ∘ ⌜ δ ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ (σ ∘w ν) ∘w δ ⌝w ]    ∎
        s : (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
        s = ∘∘w
        t : tr (Var _) r
               ((tr (Var _) q (x +v ν))
                +v δ)
            ≅[ Var Γ ]
            tr (Var _) p (x +v (ν ∘w δ))
        t = tr (Var _) r
               ((tr (Var _) q (x +v ν)) +v δ)
              ≅⟨ trfill (Var _) r _ ⁻¹ ⟩
            (tr (Var _) q (x +v ν)) +v δ
              ≅⟨ apd (λ x → x +v δ) (trfill (Var _) q (x +v ν)) ⁻¹ ⟩
            (x +v ν) +v δ
              ≅⟨ +v∘ {x = x} ≅⁻¹ ⟩'
            x +v (ν ∘w δ)
              ≅⟨ trfill (Var _) p _ ⟩
            tr (Var _) p (x +v (ν ∘w δ)) ≅∎
    in λ i → s i , ≅-to-≡[] isSetTy t {P = apd (λ x → A [ ⌜ x ⌝w ]) s} i


  wkw∘w : {Γ Δ Θ : Con} {A : Ty Δ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} {y : Var Γ (A [ ⌜ ν ⌝w ])} →
           (wkw σ) ∘w (ν , y) ≡ σ ∘w ν
  wkw∘w {Θ = ●} {σ = ε} = refl
  wkw∘w {Γ} {Δ} {Θ , B} {A} {σ , x} {ν} {y} =
    let p : ((wkw σ) ∘w (ν , y)) ≡ σ ∘w ν
        p = wkw∘w {σ = σ} {ν} {y}
        q : B [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡ B [ ⌜ σ ∘w ν ⌝w ]
        q = B [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ B [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            B [ ⌜ σ ∘w ν ⌝w ]      ∎
        q' = B [ ⌜ wkw σ ⌝w ] Ty.[ ⌜ ν , y ⌝w ] ≡ B [ ⌜ (wkw σ) ∘w (ν , y) ⌝w ]
        q' = B [ ⌜ wkw σ ⌝w ] [ ⌜ ν , y ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
             B [ ⌜ wkw σ ⌝w ∘ ⌜ ν , y ⌝w ]   ≡⟨ B [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
             B [ ⌜ (wkw σ) ∘w (ν , y) ⌝w ]  ∎
        r : B [ ⌜ σ ⌝w ] [ wk {A = A} ] ≡ B [ ⌜ wkw σ ⌝w ]
        r = B [ ⌜ σ ⌝w ] [ wk ] ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ wk ]    ≡⟨ B [ ⌜wkw⌝ ≋⁻¹ ]≈T ⟩
            B [ ⌜ wkw σ ⌝w ]     ∎
        s : tr (Var Γ) q' ((tr (Var _) r (s x)) +v (ν , y))
            ≅[ Var Γ ]
            tr (Var Γ) q (x +v ν)
        s = tr (Var Γ) q' ((tr (Var _) r (s x)) +v (ν , y))
              ≅⟨ trfill (Var Γ) q' _ ⁻¹ ⟩
            (tr (Var _) r (s x)) +v (ν , y)
              ≅⟨ apd (λ x → x +v (ν , y)) (trfill (Var _) r (s x)) ⁻¹ ⟩
            (s x) +v (ν , y)
              ≅⟨ trfill (Var Γ) []wk, (x +v ν) ⁻¹ ⟩
            x +v ν
              ≅⟨ trfill (Var Γ) q (x +v ν) ⟩
            tr (Var Γ) q (x +v ν) ≅∎
    in λ i → p i , ≅-to-≡[] isSetTy s {P = ap (λ x → B [ ⌜ x ⌝w ]) p} i

  id∘w : {Γ Δ : Con} {σ : Wk Γ Δ} → idw ∘w σ ≡ σ
  id∘w {Δ = ●} {ε} = refl
  id∘w {Γ} {Δ , A} {σ , x} =
    let p : (wkw idw) ∘w (σ , x) ≡ σ
        p = (wkw idw) ∘w (σ , x) ≡⟨ wkw∘w ⟩
            idw ∘w σ             ≡⟨ id∘w ⟩
            σ                    ∎
        q : A [ ⌜ wkw idw ⌝w ] [ ⌜ σ , x ⌝w ] ≡ A [ ⌜ (wkw idw) ∘w (σ , x) ⌝w ]
        q = A [ ⌜ wkw idw ⌝w ] [ ⌜ σ , x ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ wkw idw ⌝w ∘ ⌜ σ , x ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ (wkw idw) ∘w (σ , x) ⌝w ]  ∎
        r : tr (Var _) q ((tr (Var _) [⌜wkid⌝] z) +v (σ , x))
            ≅[ Var Γ ] x
        r = tr (Var _) q ((tr (Var _) [⌜wkid⌝] z) +v (σ , x))
              ≅⟨ trfill (Var _) q _ ⁻¹ ⟩
            (tr (Var _) [⌜wkid⌝] z) +v (σ , x)
              ≅⟨ apd (λ y → y +v (σ , x)) (trfill (Var _) [⌜wkid⌝] z) ⁻¹ ⟩
            tr (Var _) []wk, x   -- z +v (σ , x)
              ≅⟨ trfill (Var _) []wk, x ⁻¹ ⟩
            x ≅∎
    in λ i → p i , ≅-to-≡[] isSetTy r {P = ap (λ x → A [ ⌜ x ⌝w ]) p} i


  ⌜↑w⌝ : {Γ Δ : Con} {A : Ty Δ} {σ : Wk Γ Δ} → ⌜ σ ↑w A ⌝w ≋ ⌜ σ ⌝w ↑ A
  ⌜↑w⌝ {Γ} {Δ} {A} {σ} =
    let p : ⌜ wkw σ ⌝w ≋ ⌜ σ ⌝w ∘ wk
        p = ⌜wkw⌝
        q : ⌜ tr (Var _) [⌜wkw⌝] z ⌝v ≈ tr (Tm _) ([][]T ⁻¹) vz
        q = ⌜ tr (Var _) [⌜wkw⌝] z ⌝v ≈⟨ apd ⌜_⌝v (trfill (Var _) [⌜wkw⌝] z ⁻¹) ⟩'
            ⌜ z ⌝v                   ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⟩'
            tr (Tm _) ([][]T ⁻¹) vz  ≈∎
    in ⌜ wkw σ ⌝w , ⌜ tr (Var _) [⌜wkw⌝] z ⌝v
         ≋⟨ p ,≋ q ⟩
       ⌜ σ ⌝w ∘ wk , tr (Tm _) ([][]T ⁻¹) vz ≋∎

  ↑wid : {Γ : Con} {A : Ty Γ} → idw {Γ} ↑w A ≅[ (λ x → Wk x (Γ , A)) ] idw {Γ , A}
  ↑wid {Γ} {A} =
    let p : A [ ⌜ idw ⌝w ] ≡ A
        p = A [ ⌜ idw ⌝w ] ≡⟨ A [ ⌜idw⌝ ]≈T ⟩
            A [ id ]      ≡⟨ [id]T ⟩
            A              ∎
        q : wkw {A = A [ ⌜ idw ⌝w ]} idw
            ≡[ ap (λ x → Wk (Γ , x) Γ) p ]≡
            wkw {A = A} idw
        q = apd (λ x → wkw {A = x} idw) p
        r : tr (Var _) [⌜wkw⌝] (z {A = A [ ⌜ idw ⌝w ]})
            ≅[ (λ (x : Σ Con Ty) → Var (fst x) (snd x)) ]
            tr (Var _) [⌜wkid⌝] (z {A = A})
        r = tr (Var _) [⌜wkw⌝] (z {A = A [ ⌜ idw ⌝w ]})
              ≅⟨ ap (_ ,,_) [⌜wkw⌝] ⁻¹ ∣ trfill (Var _) [⌜wkw⌝] z ⁻¹ ⟩
            z {A = A [ ⌜ idw ⌝w ]}
              ≅⟨ ap (λ x → Γ , x ,, x [ wk {A = x} ]) p ∣ apd (λ x → z {A = x}) p ⟩
            z {A = A}
              ≅⟨ ap (_ ,,_) [⌜wkid⌝] ∣ trfill (Var _) [⌜wkid⌝] z ⟩
            tr (Var _) [⌜wkid⌝] (z {A = A}) ≅∎
        s : (Γ , A [ ⌜ idw ⌝w ] ,, A [ ⌜ wkw {A = A [ ⌜ idw ⌝w ]} idw ⌝w ])
            ≡ (Γ , A ,, A [ ⌜ wkw {A = A} idw ⌝w ])
        s i = Γ , p i ,, A [ ⌜ wkw {A = p i} idw ⌝w ]
    in wkw {A = A [ ⌜ idw ⌝w ]} idw , tr (Var (Γ , A [ ⌜ idw ⌝w ])) [⌜wkw⌝] z
         ≅⟨ (λ i → q i , ≅-to-≡[] (isSetΣ isSetCon isSetTy) r {P = s} i) ⟩
       wkw {A = A} idw , tr (Var (Γ , A)) [⌜wkid⌝] z ≅∎


  -- Usefull lemma.
  wkid∘↑ : {Γ Δ : Con} {A : Ty Δ} {σ : Wk Γ Δ} →
           (wkw idw) ∘w (σ ↑w A) ≡ σ ∘w (wkw idw)
  wkid∘↑ {A = A} {σ} =
    (wkw idw) ∘w (σ ↑w A) ≡⟨ wkw∘w ⟩
    idw ∘w (wkw σ)        ≡⟨ id∘w ⟩
    wkw σ                 ≡⟨ ∘idw ⁻¹ ⟩
    (wkw σ) ∘w idw        ≡⟨ wkw∘w ⟩
    σ ∘w (wkw idw)        ∎
