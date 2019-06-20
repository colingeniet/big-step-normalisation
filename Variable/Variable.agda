{-# OPTIONS --cubical #-}

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
open import Syntax.Sets

-- Definition
data Var : (Γ : Con) → Ty Γ → Set where
  z : {Γ : Con} {A : Ty Γ} → Var (Γ , A) (A [ wk ])
  s : {Γ : Con} {A B : Ty Γ} → Var Γ A → Var (Γ , B) (A [ wk ])

⌜_⌝v : {Γ : Con} {A : Ty Γ} → Var Γ A → Tm Γ A
⌜ z ⌝v = vz
⌜ s x ⌝v = vs ⌜ x ⌝v

data Wk : Con → Con → Set
⌜_⌝w : {Γ Δ : Con} → Wk Γ Δ → Tms Γ Δ

data Wk where
  ε : {Γ : Con} → Wk Γ ●
  _,_ : {Γ Δ : Con} {A : Ty Δ} →
        (σ : Wk Γ Δ) → Var Γ (A [ ⌜ σ ⌝w ]) → Wk Γ (Δ , A)

⌜ ε ⌝w = ε
⌜ σ , x ⌝w = ⌜ σ ⌝w , ⌜ x ⌝v


-- Weakening of variables, composition
abstract
  []wk, : {Γ Δ : Con} {A B : Ty Δ} {σ : Tms Γ Δ} {u : Tm Γ (B [ σ ])} →
          A Ty.[ σ ] ≡ A [ wk ] [ σ , u ]
  []wk, {Γ} {Δ} {A} {B} {σ} {u} =
    A [ σ ]            ≡⟨ A [ wk, ≋⁻¹ ]≈T ⟩
    A [ wk ∘ (σ , u) ] ≡⟨ [][]T ⟩
    A [ wk ] [ σ , u ] ∎

_+v_ : {Γ Δ : Con} {A : Ty Δ} → Var Δ A → (σ : Wk Γ Δ) → Var Γ (A [ ⌜ σ ⌝w ])
z +v (_ , y) = tr (Var _) []wk, y
(s x) +v (σ , _) = tr (Var _) []wk, (x +v σ)

abstract
  ⌜⌝+v : {Γ Δ : Con} {A : Ty Δ} {x : Var Δ A} {σ : Wk Γ Δ} →
         ⌜ x +v σ ⌝v ≈ ⌜ x ⌝v [ ⌜ σ ⌝w ]
  ⌜⌝+v {Γ} {Δ} {A} {z} {σ , y} =
    ⌜ tr (Var Γ) []wk, y ⌝v ≈⟨ apd ⌜_⌝v (trfill (Var Γ) []wk, y) ⁻¹ ⟩'
    ⌜ y ⌝v                  ≈⟨ vz[,] ≈⁻¹ ⟩
    vz [ ⌜ σ ⌝w , ⌜ y ⌝v ]  ≈∎
  ⌜⌝+v {Γ} {Δ} {A} {s x} {σ , y} =
    ⌜ tr (Var Γ) []wk, (x +v σ) ⌝v   ≈⟨ apd ⌜_⌝v (trfill (Var Γ) []wk, _) ⁻¹ ⟩'
    ⌜ x +v σ ⌝v                      ≈⟨ ⌜⌝+v ⟩
    ⌜ x ⌝v [ ⌜ σ ⌝w ]                ≈⟨ refl≈ [ wk, ≋⁻¹ ]≈ ⟩
    ⌜ x ⌝v [ wk ∘ (⌜ σ ⌝w , ⌜ y ⌝v) ] ≈⟨ [][] ⟩
    ⌜ x ⌝v [ wk ] [ ⌜ σ ⌝w , ⌜ y ⌝v ] ≈∎


_∘w_ : {Γ Δ Θ : Con} → Wk Δ Θ → Wk Γ Δ → Wk Γ Θ

⌜∘⌝w : {Γ Δ Θ : Con} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
       ⌜ σ ∘w ν ⌝w ≋ ⌜ σ ⌝w ∘ ⌜ ν ⌝w


ε ∘w ν = ε
_∘w_ {Γ} {Δ} {Θ , A} (σ , x) ν =
  let p : A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡ A [ ⌜ σ ∘w ν ⌝w ]
      p = A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
          A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
          A [ ⌜ σ ∘w ν ⌝w ]       ∎
  in (σ ∘w ν) , tr (Var _) p (x +v ν)

abstract
  ⌜∘⌝w {σ = ε} {ν} =
    ε         ≋⟨ εη ≋⁻¹ ⟩
    ε ∘ ⌜ ν ⌝w ≋∎
  ⌜∘⌝w {Γ} {Δ} {Θ , A} {σ = σ , x} {ν} = 
    let p : A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡ A [ ⌜ σ ∘w ν ⌝w ]
        p = A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ A [ ⌜∘⌝w ≋⁻¹ ]≈T ⟩
            A [ ⌜ σ ∘w ν ⌝w ]       ∎
        q : ⌜ σ ∘w ν ⌝w ≋ ⌜ σ ⌝w ∘ ⌜ ν ⌝w
        q = ⌜∘⌝w
        r : ⌜ tr (Var Γ) p (x +v ν) ⌝v ≈ tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ])
        r = ⌜ tr (Var Γ) p (x +v ν) ⌝v ≈⟨ apd ⌜_⌝v (trfill (Var Γ) p (x +v ν)) ⁻¹ ⟩'
            ⌜ x +v ν ⌝v                ≈⟨ ⌜⌝+v ⟩
            ⌜ x ⌝v [ ⌜ ν ⌝w ]           ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩'
            tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ]) ≈∎
        in ⌜ σ ∘w ν ⌝w , ⌜ tr (Var Γ) p (x +v ν) ⌝v
             ≋⟨ q ,≋ r ⟩
           (⌜ σ ⌝w ∘ ⌜ ν ⌝w) , tr (Tm Γ) ([][]T ⁻¹) (⌜ x ⌝v [ ⌜ ν ⌝w ])
             ≋⟨ ,∘ {σ = ⌜ σ ⌝w} {⌜ ν ⌝w} {⌜ x ⌝v} ≋⁻¹ ⟩
           (⌜ σ ⌝w , ⌜ x ⌝v) ∘ ⌜ ν ⌝w ≋∎


-- Identity environment
wkw : {Γ Δ : Con} {A : Ty Γ} → Wk Γ Δ → Wk (Γ , A) Δ

⌜wkw⌝ : {Γ Δ : Con} {A : Ty Γ} {σ : Wk Γ Δ} →
        ⌜ wkw {A = A} σ ⌝w ≋ ⌜ σ ⌝w ∘ wk

wkw {Δ = ●} _ = ε
wkw {Δ = Δ , B} {A} (σ , x) =
  let p : B [ ⌜ σ ⌝w ] [ wk {A = A} ] ≡ B [ ⌜ wkw σ ⌝w ]
      p = B [ ⌜ σ ⌝w ] [ wk ] ≡⟨ [][]T ⁻¹ ⟩
          B [ ⌜ σ ⌝w ∘ wk ]   ≡⟨ B [ ⌜wkw⌝ ≋⁻¹ ]≈T ⟩
          B [ ⌜ wkw σ ⌝w ]    ∎
  in (wkw σ) , tr (Var _) p (s x)

abstract
  ⌜wkw⌝ {Δ = ●} {σ = σ} =
    ε          ≋⟨ εη ≋⁻¹ ⟩
    ⌜ σ ⌝w ∘ wk ≋∎
  ⌜wkw⌝ {Γ} {Δ , B} {A} {σ , x} =
    let p : B [ ⌜ σ ⌝w ] [ wk {A = A} ] ≡ B [ ⌜ wkw σ ⌝w ]
        p = B [ ⌜ σ ⌝w ] [ wk ] ≡⟨ [][]T ⁻¹ ⟩
            B [ ⌜ σ ⌝w ∘ wk ]   ≡⟨ B [ ⌜wkw⌝ ≋⁻¹ ]≈T ⟩
            B [ ⌜ wkw σ ⌝w ]    ∎
        q : ⌜ wkw σ ⌝w ≋ ⌜ σ ⌝w ∘ wk
        q = ⌜wkw⌝
        r : ⌜ tr (Var _) p (s x) ⌝v ≈ tr (Tm (Γ , A)) ([][]T ⁻¹) (⌜ x ⌝v [ wk ])
        r = ⌜ tr (Var _) p (s x) ⌝v ≈⟨ apd ⌜_⌝v (trfill (Var _) p (s x)) ⁻¹ ⟩'
            ⌜ s x ⌝v                ≈⟨ trfill (Tm _) ([][]T ⁻¹) _ ⟩'
            tr (Tm _) ([][]T ⁻¹) ⌜ s x ⌝v ≈∎
    in ⌜ wkw σ ⌝w , ⌜ tr (Var _) p (s x) ⌝v
         ≋⟨ q ,≋ r ⟩
       ⌜ σ ⌝w ∘ wk , tr (Tm (Γ , A)) ([][]T ⁻¹) (⌜ x ⌝v [ wk ])
         ≋⟨ ,∘ ≋⁻¹ ⟩
       (⌜ σ ⌝w , ⌜ x ⌝v) ∘ wk ≋∎


idw : {Γ : Con} → Wk Γ Γ
⌜idw⌝ : {Γ : Con} → ⌜ idw {Γ} ⌝w ≋ id {Γ}

abstract
  ⌜wkid⌝ : {Γ : Con} {A : Ty Γ} → ⌜ wkw {A = A} idw ⌝w ≋ wk {A = A}
  ⌜wkid⌝ {Γ} {A} =
    ⌜ wkw idw ⌝w  ≋⟨ ⌜wkw⌝ ⟩
    ⌜ idw ⌝w ∘ wk ≋⟨ ⌜idw⌝ ∘≋ refl≋ ⟩
    id ∘ wk      ≋⟨ id∘ ⟩
    wk           ≋∎

[⌜wkid⌝] : {Γ : Con} {A : Ty Γ} → A [ wk ] ≡ A [ ⌜ wkw {A = A} idw ⌝w ]
[⌜wkid⌝] {Γ} {A} = A [ ⌜wkid⌝ ≋⁻¹ ]≈T


idw {●} = ε
idw {Γ , A} = wkw (idw {Γ}) , tr (Var _) [⌜wkid⌝] z

abstract
  ⌜idw⌝ {●} =
    ε  ≋⟨ εη ≋⁻¹ ⟩
    id ≋∎
  ⌜idw⌝ {Γ , A} =
    let p : ⌜ wkw idw ⌝w ≋ wk
        p = ⌜wkid⌝
        q : ⌜ tr (Var _) [⌜wkid⌝] z ⌝v ≈ vz
        q = ⌜ tr (Var _) [⌜wkid⌝] z ⌝v ≈⟨ apd ⌜_⌝v (trfill (Var _) [⌜wkid⌝] z) ⁻¹ ⟩'
            ⌜ z ⌝v                    ≈∎
    in ⌜ wkw idw ⌝w , ⌜ tr (Var _) [⌜wkid⌝] z ⌝v
         ≋⟨ p ,≋ q ⟩
       wk , vz
         ≋⟨ πη ⟩
       id ≋∎


abstract
  [⌜wkw⌝] : {Γ Δ : Con} {A : Ty Δ} {σ : Wk Γ Δ} →
            A [ ⌜ σ ⌝w ] Ty.[ wk {A = A [ ⌜ σ ⌝w ]} ] ≡ A [ ⌜ wkw σ ⌝w ]
  [⌜wkw⌝] {Γ} {Δ} {A} {σ} =
    A [ ⌜ σ ⌝w ] [ wk ] ≡⟨ [][]T ⁻¹ ⟩
    A [ ⌜ σ ⌝w ∘ wk ]    ≡⟨ A [ ⌜wkw⌝ ≋⁻¹ ]≈T ⟩
    A [ ⌜ wkw σ ⌝w ]     ∎

_↑w_ : {Γ Δ : Con} (σ : Wk Γ Δ) (A : Ty Δ) → Wk (Γ , A [ ⌜ σ ⌝w ]) (Δ , A)
σ ↑w A = wkw σ , tr (Var _) [⌜wkw⌝] z
