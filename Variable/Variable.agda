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

abstract
  ⌜wkid⌝ : {Γ : Con} {A : Ty Γ} → ⌜ wkw {A = A} idw ⌝w ≡ wk
  ⌜wkid⌝ {Γ} {A} =
    ⌜ wkw idw ⌝w  ≡⟨ ⌜wkw⌝ ⟩
    ⌜ idw ⌝w ∘ wk ≡⟨ ap (_∘ wk) ⌜idw⌝ ⟩
    id ∘ wk      ≡⟨ id∘ ⟩
    wk           ∎

[⌜wkid⌝] : {Γ : Con} {A : Ty Γ} → A [ wk ]T ≡ A [ ⌜ wkw {A = A} idw ⌝w ]T
[⌜wkid⌝] {Γ} {A} = ap (A [_]T) ⌜wkid⌝ ⁻¹


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
  [⌜wkw⌝] : {Γ Δ : Con} {A : Ty Δ} {σ : Wk Γ Δ} →
            A [ ⌜ σ ⌝w ]T [ wk {A = A [ ⌜ σ ⌝w ]T} ]T ≡ A [ ⌜ wkw σ ⌝w ]T
  [⌜wkw⌝] {Γ} {Δ} {A} {σ} =
    A [ ⌜ σ ⌝w ]T [ wk ]T ≡⟨ [][]T ⁻¹ ⟩
    A [ ⌜ σ ⌝w ∘ wk ]T    ≡⟨ ap (A [_]T) ⌜wkw⌝ ⁻¹ ⟩
    A [ ⌜ wkw σ ⌝w ]T     ∎

_↑w_ : {Γ Δ : Con} (σ : Wk Γ Δ) (A : Ty Δ) → Wk (Γ , A [ ⌜ σ ⌝w ]T) (Δ , A)
σ ↑w A = wkw σ , tr (Var _) [⌜wkw⌝] z
