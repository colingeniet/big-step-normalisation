{-# OPTIONS --safe --cubical #-}

{-
  Definition of variables and weakenings.
  Weakenings are defined in the very broad sense of lists of variables
  (aka renamings).
-}

module Variable.Variable where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas

-- Definition
data Var : (Γ : Con) → Ty Γ → Set where
  z : {Γ : Con} {A : Ty Γ} → Var (Γ , A) (A [ wk ]T)
  s : {Γ : Con} {A B : Ty Γ} → Var Γ A → Var (Γ , B) (A [ wk ]T)

⌜_⌝v : {Γ : Con} {A : Ty Γ} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

data Wk : Con → Con → Set
⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ

data Wk where
  ε : {Γ : Con} → Wk Γ ●
  _,_ : {Γ Δ : Con} {A : Ty Δ} →
        (σ : Wk Γ Δ) → Var Γ (A [ ⌜ σ ⌝w ]T) → Wk Γ (Δ , A)

⌜ ε ⌝w = ε
⌜ σ , x ⌝w = ⌜ σ ⌝w , ⌜ x ⌝v


-- Weakening of variables, composition
private
  abstract
    []wk, : {Γ Δ : Con} {A B : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (B [ σ ]T)} →
            A [ σ ]T ≡ A [ wk ]T [ σ , u ]T
    []wk, {Γ} {Δ} {A} {B} {σ} {u} =
      A [ σ ]T             ≡⟨ ap (λ x → A [ x ]T) (wk, ⁻¹) ⟩
      A [ wk ∘ (σ , u) ]T  ≡⟨ [][]T ⟩
      A [ wk ]T [ σ , u ]T ∎

_+v_ : {Γ Δ : Con} {A : Ty Δ} → Var Δ A → (σ : Wk Γ Δ) → Var Γ (A [ ⌜ σ ⌝w ]T)
z +v (_ , y) = tr (Var _) []wk, y
(s x) +v (σ , _) = tr (Var _) []wk, (x +v σ)

abstract
  ⌜⌝+v : {Γ Δ : Con} {A : Ty Δ} {x : Var Δ A} {σ : Wk Γ Δ} →
         ⌜ x +v σ ⌝v ≡ ⌜ x ⌝v [ ⌜ σ ⌝w ]
  ⌜⌝+v {Γ} {Δ} {A} {z} {σ , y} = ≅-to-≡ isSetTy (
    ⌜ tr (Var Γ) []wk, y ⌝v ≅⟨ apd ⌜_⌝v (trfill (Var Γ) []wk, y) ⁻¹ ⟩
    ⌜ y ⌝v                  ≅⟨ vz[,] ≅⁻¹ ⟩'
    vz [ ⌜ σ ⌝w , ⌜ y ⌝v ]  ≅∎)
  ⌜⌝+v {Γ} {Δ} {A} {s x} {σ , y} = ≅-to-≡ isSetTy (
    ⌜ tr (Var Γ) []wk, (x +v σ) ⌝v   ≅⟨ apd ⌜_⌝v (trfill (Var Γ) []wk, _) ⁻¹ ⟩
    ⌜ x +v σ ⌝v                      ≅⟨ ⌜⌝+v ⟩
    ⌜ x ⌝v [ ⌜ σ ⌝w ]                ≅⟨ apd (λ σ → ⌜ x ⌝v [ σ ]) (wk, ⁻¹) ⟩
    ⌜ x ⌝v [ wk ∘ (⌜ σ ⌝w , ⌜ y ⌝v) ] ≅⟨ [][] ⟩'
    ⌜ x ⌝v [ wk ] [ ⌜ σ ⌝w , ⌜ y ⌝v ] ≅∎)


_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ

⌜∘⌝w : {Γ Δ Θ : Con} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       ⌜ σ ∘w ν ⌝w ≡ ⌜ σ ⌝w ∘ ⌜ ν ⌝w


ε ∘w ν = ε
_∘w_ {Γ} {Δ} {Θ , A} (σ , x) ν =
  let p : A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡ A [ ⌜ σ ∘w ν ⌝w ]T
      p = A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
          A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
          A [ ⌜ σ ∘w ν ⌝w ]T       ∎
  in (σ ∘w ν) , tr (Var _) p (x +v ν)

abstract
  ⌜∘⌝w {σ = ε} {ν} =
    ε         ≡⟨ εη ⁻¹ ⟩
    ε ∘ ⌜ ν ⌝w ∎
  ⌜∘⌝w {Γ} {Δ} {Θ , A} {σ = σ , x} {ν} = 
    let p : A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡ A [ ⌜ σ ∘w ν ⌝w ]T
        p = A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ σ ∘w ν ⌝w ]T       ∎
        q : ⌜ σ ∘w ν ⌝w ≡ ⌜ σ ⌝w ∘ ⌜ ν ⌝w
        q = ⌜∘⌝w
        r : ⌜ tr (Var Γ) p (x +v ν) ⌝v
            ≅[ Tm Γ ]
            tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ])
        r = ⌜ tr (Var Γ) p (x +v ν) ⌝v
              ≅⟨ apd ⌜_⌝v (trfill (Var Γ) p (x +v ν)) ⁻¹ ⟩
            ⌜ x +v ν ⌝v
              ≅⟨ ⌜⌝+v ⟩
            ⌜ x ⌝v [ ⌜ ν ⌝w ]
              ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩
            tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ]) ≅∎
        s : ⌜ (σ , x) ∘w ν ⌝w ≅[ Tms Γ ] ⌜ σ , x ⌝w ∘ ⌜ ν ⌝w
        s = ⌜ σ ∘w ν ⌝w , ⌜ tr (Var Γ) p (x +v ν) ⌝v
              ≅⟨ (λ i → q i , ≅-to-≡[] isSetTy r {P = ap (λ x → A [ x ]T) q} i)⟩
            (⌜ σ ⌝w ∘ ⌜ ν ⌝w) , tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ])
              ≅⟨ ,∘ {σ = ⌜ σ ⌝w} {⌜ ν ⌝w} {⌜ x ⌝v} ⁻¹ ⟩
            (⌜ σ ⌝w , ⌜ x ⌝v) ∘ ⌜ ν ⌝w ≅∎
        in ≅-to-≡ isSetCon s


-- Identity environment
wkw : {Γ Δ : Con} {A : Ty Γ} → Wk Γ Δ → Wk (Γ , A) Δ

⌜wkw⌝ : {Γ Δ : Con} {A : Ty Γ} {σ : Wk Γ Δ} →
        ⌜ wkw {A = A} σ ⌝w ≡ ⌜ σ ⌝w ∘ wk

wkw {Δ = ●} _ = ε
wkw {Δ = Δ , B} {A} (σ , x) =
  let p : B [ ⌜ σ ⌝w ]T [ wk {A = A} ]T ≡ B [ ⌜ wkw σ ⌝w ]T
      p = B [ ⌜ σ ⌝w ]T [ wk ]T ≡⟨ [][]T ⁻¹ ⟩
          B [ ⌜ σ ⌝w ∘ wk ]T    ≡⟨ ap (λ x → B [ x ]T) ⌜wkw⌝ ⁻¹ ⟩
          B [ ⌜ wkw σ ⌝w ]T     ∎
  in (wkw σ) , tr (Var _) p (s x)

abstract
  ⌜wkw⌝ {Δ = ●} = εη ⁻¹
  ⌜wkw⌝ {Γ} {Δ , B} {A} {σ , x} =
    let p : B [ ⌜ σ ⌝w ]T [ wk {A = A} ]T ≡ B [ ⌜ wkw σ ⌝w ]T
        p = B [ ⌜ σ ⌝w ]T [ wk ]T ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ wk ]T    ≡⟨ ap (λ x → B [ x ]T) ⌜wkw⌝ ⁻¹ ⟩
            B [ ⌜ wkw σ ⌝w ]T     ∎
        q : ⌜ wkw σ ⌝w ≡ ⌜ σ ⌝w ∘ wk
        q = ⌜wkw⌝
        r : ⌜ tr (Var _) p (s x) ⌝v
            ≅[ Tm (Γ , A) ]
            tr (Tm (Γ , A)) ([][]T ⁻¹) (⌜ x ⌝v [ wk ])
        r = ⌜ tr (Var _) p (s x) ⌝v
              ≅⟨ apd ⌜_⌝v (trfill (Var _) p (s x)) ⁻¹ ⟩
            ⌜ s x ⌝v
              ≅⟨ trfill (Tm _) ([][]T ⁻¹) _ ⟩
            tr (Tm _) ([][]T ⁻¹) ⌜ s x ⌝v ≅∎
        s : ⌜ wkw (σ , x) ⌝w ≅[ Tms (Γ , A) ] ⌜ σ , x ⌝w ∘ wk
        s = ⌜ wkw σ ⌝w , ⌜ tr (Var _) p (s x) ⌝v
              ≅⟨ (λ i → q i , ≅-to-≡[] isSetTy r {P = ap (λ x → B [ x ]T) q} i) ⟩
            ⌜ σ ⌝w ∘ wk , tr (Tm (Γ , A)) ([][]T ⁻¹) (⌜ x ⌝v [ wk ])
              ≅⟨ ,∘ ⁻¹ ⟩
            (⌜ σ ⌝w , ⌜ x ⌝v) ∘ wk ≅∎
    in ≅-to-≡ isSetCon s


idw : {Γ : Con} → Wk Γ Γ
⌜idw⌝ : {Γ : Con} → ⌜ idw {Γ} ⌝w ≡ id

private
  abstract
    [⌜wkid⌝] : {Γ : Con} {A : Ty Γ} → A [ wk ]T ≡ A [ ⌜ wkw {A = A} idw ⌝w ]T
    [⌜wkid⌝] {Γ} {A} =
      A [ wk ]T           ≡⟨ ap (λ x → A [ x ]T) id∘ ⁻¹ ⟩
      A [ id ∘ wk ]T      ≡⟨ ap (λ x → A [ x ∘ wk ]T) ⌜idw⌝ ⁻¹ ⟩
      A [ ⌜ idw ⌝w ∘ wk ]T ≡⟨ ap (λ x → A [ x ]T) ⌜wkw⌝ ⁻¹ ⟩
      A [ ⌜ wkw idw ⌝w ]T  ∎    

idw {●} = ε
idw {Γ , A} = wkw (idw {Γ}) , tr (Var _) [⌜wkid⌝] z

abstract
  ⌜idw⌝ {●} = εη ⁻¹
  ⌜idw⌝ {Γ , A} =
    let p : ⌜ wkw idw ⌝w ≡ wk
        p = ⌜ wkw idw ⌝w  ≡⟨ ⌜wkw⌝ ⟩
            ⌜ idw ⌝w ∘ wk ≡⟨ ap (λ x → x ∘ wk) ⌜idw⌝ ⟩
            id ∘ wk      ≡⟨ id∘ ⟩
            wk           ∎
        q : ⌜ tr (Var _) [⌜wkid⌝] z ⌝v ≅[ Tm _ ] vz
        q = ⌜ tr (Var _) [⌜wkid⌝] z ⌝v ≅⟨ apd ⌜_⌝v (trfill (Var _) [⌜wkid⌝] z) ⁻¹ ⟩
            ⌜ z ⌝v                    ≅∎
        s : ⌜ idw ⌝w ≅[ Tms (Γ , A) ] id
        s = ⌜ wkw idw ⌝w , ⌜ tr (Var _) [⌜wkid⌝] z ⌝v
              ≅⟨ (λ i → p i , ≅-to-≡[] isSetTy q {P = ap (λ x → A [ x ]T) p} i) ⟩
            wk , vz
              ≅⟨ πη ⟩
            id ≅∎
    in ≅-to-≡ isSetCon s



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
    let p : A [ ⌜ σ ⌝w ]T [ ⌜ idw ⌝w ]T ≡ A [ ⌜ σ ∘w idw ⌝w ]T
        p = A [ ⌜ σ ⌝w ]T [ ⌜ idw ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ idw ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ σ ∘w idw ⌝w ]T       ∎
        q : tr (Var _) p (x +v idw) ≅[ Var Γ ] x
        q = tr (Var _) p (x +v idw) ≅⟨ trfill (Var _) p (x +v idw) ⁻¹ ⟩
            x +v idw                ≅⟨ +vid ⟩'
            x                       ≅∎
    in λ i → ∘idw {σ = σ} i , ≅-to-≡[] isSetTy q {P = ap (λ x → A [ ⌜ x ⌝w ]T) (∘idw {σ = σ})} i

  ∘∘w : {Γ Δ Θ Ψ : Con} {σ : Wk Θ Ψ} {ν : Wk Δ Θ} {δ : Wk Γ Δ} →
        (σ ∘w ν) ∘w δ ≡ σ ∘w (ν ∘w δ)
  ∘∘w {Ψ = ●} {ε} = refl
  ∘∘w {Γ} {Δ} {Θ} {Ψ , A} {σ , x} {ν} {δ} =
    let p : A [ ⌜ σ ⌝w ]T [ ⌜ ν ∘w δ ⌝w ]T ≡ A [ ⌜ σ ∘w (ν ∘w δ) ⌝w ]T
        p = A [ ⌜ σ ⌝w ]T [ ⌜ ν ∘w δ ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ∘w δ ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ σ ∘w (ν ∘w δ) ⌝w ]T     ∎
        q : A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡ A [ ⌜ σ ∘w ν ⌝w ]T
        q = A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ σ ∘w ν ⌝w ]T       ∎
        r : A [ ⌜ σ ∘w ν ⌝w ]T [ ⌜ δ ⌝w ]T ≡ A [ ⌜ (σ ∘w ν) ∘w δ ⌝w ]T
        r = A [ ⌜ σ ∘w ν ⌝w ]T [ ⌜ δ ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ∘w ν ⌝w ∘ ⌜ δ ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ (σ ∘w ν) ∘w δ ⌝w ]T     ∎
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
    in λ i → s i , ≅-to-≡[] isSetTy t {P = apd (λ x → A [ ⌜ x ⌝w ]T) s} i


  wkw∘w : {Γ Δ Θ : Con} {A : Ty Δ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} {y : Var Γ (A [ ⌜ ν ⌝w ]T)} →
           (wkw σ) ∘w (ν , y) ≡ σ ∘w ν
  wkw∘w {Θ = ●} {σ = ε} = refl
  wkw∘w {Γ} {Δ} {Θ , B} {A} {σ , x} {ν} {y} =
    let p : ((wkw σ) ∘w (ν , y)) ≡ σ ∘w ν
        p = wkw∘w {σ = σ} {ν} {y}
        q : B [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡ B [ ⌜ σ ∘w ν ⌝w ]T
        q = B [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]T    ≡⟨ ap (λ x → B [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            B [ ⌜ σ ∘w ν ⌝w ]T       ∎
        q' = B [ ⌜ wkw σ ⌝w ]T [ ⌜ ν , y ⌝w ]T ≡ B [ ⌜ (wkw σ) ∘w (ν , y) ⌝w ]T
        q' = B [ ⌜ wkw σ ⌝w ]T [ ⌜ ν , y ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
             B [ ⌜ wkw σ ⌝w ∘ ⌜ ν , y ⌝w ]T    ≡⟨ ap (λ x → B [ x ]T) ⌜∘⌝w ⁻¹ ⟩
             B [ ⌜ (wkw σ) ∘w (ν , y) ⌝w ]T   ∎
        r : B [ ⌜ σ ⌝w ]T [ wk {A = A} ]T ≡ B [ ⌜ wkw σ ⌝w ]T
        r = B [ ⌜ σ ⌝w ]T [ wk ]T ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ wk ]T    ≡⟨ ap (λ x → B [ x ]T) ⌜wkw⌝ ⁻¹ ⟩
            B [ ⌜ wkw σ ⌝w ]T     ∎
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
    in λ i → p i , ≅-to-≡[] isSetTy s {P = ap (λ x → B [ ⌜ x ⌝w ]T) p} i

  id∘w : {Γ Δ : Con} {σ : Wk Γ Δ} → idw ∘w σ ≡ σ
  id∘w {Δ = ●} {ε} = refl
  id∘w {Γ} {Δ , A} {σ , x} =
    let p : (wkw idw) ∘w (σ , x) ≡ σ
        p = (wkw idw) ∘w (σ , x) ≡⟨ wkw∘w ⟩
            idw ∘w σ             ≡⟨ id∘w ⟩
            σ                    ∎
        q : A [ ⌜ wkw idw ⌝w ]T [ ⌜ σ , x ⌝w ]T ≡ A [ ⌜ (wkw idw) ∘w (σ , x) ⌝w ]T
        q = A [ ⌜ wkw idw ⌝w ]T [ ⌜ σ , x ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ wkw idw ⌝w ∘ ⌜ σ , x ⌝w ]T    ≡⟨ ap (λ x → A [ x ]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ (wkw idw) ∘w (σ , x) ⌝w ]T       ∎
        r : tr (Var _) q ((tr (Var _) [⌜wkid⌝] z) +v (σ , x))
            ≅[ Var Γ ] x
        r = tr (Var _) q ((tr (Var _) [⌜wkid⌝] z) +v (σ , x))
              ≅⟨ trfill (Var _) q _ ⁻¹ ⟩
            (tr (Var _) [⌜wkid⌝] z) +v (σ , x)
              ≅⟨ apd (λ y → y +v (σ , x)) (trfill (Var _) [⌜wkid⌝] z) ⁻¹ ⟩
            tr (Var _) []wk, x   -- z +v (σ , x)
              ≅⟨ trfill (Var _) []wk, x ⁻¹ ⟩
            x ≅∎
    in λ i → p i , ≅-to-≡[] isSetTy r {P = ap (λ x → A [ ⌜ x ⌝w ]T) p} i

{-
wk∘↑w : {Γ Δ Θ : Con} {A : Ty} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       wkwk A (σ ∘w ν) ≡ (wkwk A σ) ∘w (wk↑ A ν)
wk∘↑w {Θ = ●} = refl
wk∘↑w {Θ = Θ , A} {σ = σ ,, x} = ap2 _,,_ (wk∘↑w {σ = σ}) (+vwk {x = x} ⁻¹)


-- Usefull lemma.
wkid∘↑ : {Γ Δ : Con} {A : Ty} {σ : Wk Γ Δ} →
         (wkwk A idw) ∘w (wk↑ A σ) ≡ σ ∘w (wkwk A idw)
wkid∘↑ {A = A} {σ = σ} =
  (wkwk A idw) ∘w (wk↑ A σ) ≡⟨ wk∘↑w ⁻¹ ⟩
  wkwk A (idw ∘w σ)         ≡⟨ ap (λ x → wkwk A x) id∘w ⟩
  wkwk A σ                  ≡⟨ ∘idw ⁻¹ ⟩
  (wkwk A σ) ∘w idw         ≡⟨ wkwk∘w ⟩
  σ ∘w (wkwk A idw) ∎
-}
