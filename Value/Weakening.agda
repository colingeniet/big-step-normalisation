{-# OPTIONS --safe --cubical #-}

module Value.Weakening where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Variable.Variable
open import Variable.Lemmas
open import Value.Value


-- Weakening of values.
_+V_ : {Γ Δ : Con} {A : Ty Δ} → Val Δ A → (σ : Wk Γ Δ) → Val Γ (A [ ⌜ σ ⌝w ]T)
_+NV_ : {Γ Δ : Con} {A : Ty Δ} → NV Δ A → (σ : Wk Γ Δ) → NV Γ (A [ ⌜ σ ⌝w ]T)
_+E_ : {Γ Δ Θ : Con} → Env Δ Θ → Wk Γ Δ → Env Γ Θ

-- Weakening commutes with embedding (required to define weakening of the
-- veq path constructor).
⌜⌝+V : {Γ Δ : Con} {A : Ty Δ} {v : Val Δ A} {σ : Wk Γ Δ} →
       ⌜ v +V σ ⌝V ≡ ⌜ v ⌝V +t σ
⌜⌝+NV : {Γ Δ : Con} {A : Ty Δ} {v : NV Δ A} {σ : Wk Γ Δ} →
       ⌜ v +NV σ ⌝NV ≡ ⌜ v ⌝NV +t σ
⌜⌝+E : {Γ Δ Θ : Con} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
       ⌜ ρ +E σ ⌝E ≡ ⌜ ρ ⌝E +s σ


private
  abstract
    [+E] : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
           A [ ⌜ ρ +E σ ⌝E ]T ≡ A [ ⌜ ρ ⌝E ]T [ ⌜ σ ⌝w ]T
    [+E] {Γ} {Δ} {Θ} {A} {ρ} {σ} =
      A [ ⌜ ρ +E σ ⌝E ]T       ≡⟨ ap (λ x → A [ x ]T) ⌜⌝+E ⟩
      A [ ⌜ ρ ⌝E ∘ ⌜ σ ⌝w ]T    ≡⟨ [][]T ⟩
      A [ ⌜ ρ ⌝E ]T [ ⌜ σ ⌝w ]T ∎

    [<>][] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {v : Val Δ A} {σ : Wk Γ Δ} →
             B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ v +V σ ⌝V > ]T ≡ B [ < ⌜ v ⌝V > ]T [ ⌜ σ ⌝w ]T
    [<>][] {Γ} {Δ} {A} {B} {v} {σ} =
      B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ v +V σ ⌝V > ]T ≡⟨ [][]T ⁻¹ ⟩
      B [ (⌜ σ ⌝w ↑ A) ∘ < ⌜ v +V σ ⌝V > ]T  ≡⟨ ap (λ x → B [ x ]T) ↑∘<> ⟩
      B [ ⌜ σ ⌝w , ⌜ v +V σ ⌝V ]T            ≡⟨ ap (λ x → B [ _ , x ]T) ⌜⌝+V ⟩
      B [ ⌜ σ ⌝w , ⌜ v ⌝V [ ⌜ σ ⌝w ] ]T      ≡⟨ ap (B [_]T) <>∘ ⁻¹ ⟩
      B [ < ⌜ v ⌝V > ∘ ⌜ σ ⌝w ]T             ≡⟨ [][]T ⟩
      B [ < ⌜ v ⌝V > ]T [ ⌜ σ ⌝w ]T          ∎


(lam u ρ) +V σ = tr (Val _) [+E] (lam u (ρ +E σ))
(neu v) +V σ = neu (v +NV σ)
(veq {u = u} {v} p i) +V σ = veq {u = u +V σ} {v +V σ}
                                 (⌜⌝+V {v = u}
                                 ∙ ap (λ x → x +t σ) p
                                 ∙ ⌜⌝+V {v = v} ⁻¹) i
(isSetVal p q i j) +V σ = isSetVal (λ k → p k +V σ) (λ k → q k +V σ) i j
(var x) +NV σ = var (x +v σ)
(app f v) +NV σ = tr (NV _) ([<>][] {v = v})
                     (app (tr (NV _) Π[] (f +NV σ)) (v +V σ))
ε +E _ = ε
(ρ , v) +E σ = ρ +E σ , tr (Val _) ([+E] ⁻¹) (v +V σ)

abstract
  ⌜⌝+V {Γ} {Δ} {A} {lam u ρ} {σ} = ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (Val _) [+E] (lam u (ρ +E σ)) ⌝V ≅⟨ apd ⌜_⌝V (trfill (Val _) [+E] (lam u (ρ +E σ))) ⁻¹ ⟩
    (lam u) [ ⌜ ρ +E σ ⌝E ]               ≅⟨ apd (lam u [_]) ⌜⌝+E ⟩
    (lam u) [ ⌜ ρ ⌝E ∘ ⌜ σ ⌝w ]           ≅⟨ [][] ⟩'
    (lam u) [ ⌜ ρ ⌝E ] [ ⌜ σ ⌝w ]         ≅∎)
  ⌜⌝+V {v = neu v} = ⌜⌝+NV {v = v}
  ⌜⌝+V {v = veq {u = u} {v} p j} {σ} i =
    let IHu = ⌜⌝+V {v = u} {σ}
        IHv = ⌜⌝+V {v = v} {σ}
        -- This is just  (veq p) +V σ
        -- but the termination checker wants it expanded.
        r = λ j → ⌜ veq {u = u +V σ} {v +V σ}
                        (⌜⌝+V {v = u}
                        ∙ ap (λ x → x +t σ) p
                        ∙ ⌜⌝+V {v = v} ⁻¹) j ⌝V
        s = λ j → ⌜ veq {u = u} {v} p j ⌝V +t σ
    in ouc (isSetFillSquare isSetTm r s IHu IHv i j)
  ⌜⌝+V {v = isSetVal {x = u} {v} p q i j} {σ} k =
    ouc (isSetPartial isSetTm
                      (λ j → ⌜⌝+V {v = p j} {σ} k)
                      (λ j → ⌜⌝+V {v = q j} {σ} k)
                      (λ {(k = i0) → λ i j →
                          ⌜ isSetVal (λ j → p j +V σ) (λ j → q j +V σ) i j ⌝V;
                          (k = i1) → λ i j →
                          ⌜ isSetVal p q i j ⌝V +t σ}))
        i j
  ⌜⌝+NV {v = var x} = ⌜⌝+v
  ⌜⌝+NV {Γ} {Δ} {A} {app {B = B} f v} {σ} =
    let p : ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV ≅[ Tm Γ ] tr (Tm Γ) Π[] ⌜ f +NV σ ⌝NV
        p = ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV ≅⟨ apd ⌜_⌝NV (trfill (NV Γ) Π[] (f +NV σ)) ⁻¹ ⟩
            ⌜ f +NV σ ⌝NV                 ≅⟨ trfill (Tm Γ) Π[] ⌜ f +NV σ ⌝NV ⟩
            tr (Tm Γ) Π[] ⌜ f +NV σ ⌝NV   ≅∎
    in ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV σ)) (v +V σ)) ⌝NV
      ≅⟨ apd ⌜_⌝NV (trfill (NV Γ) ([<>][] {v = v})
                           (app (tr (NV Γ) Π[] (f +NV σ)) (v +V σ))) ⁻¹ ⟩
    ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV $ ⌜ v +V σ ⌝V
      ≅⟨ (λ i → ≅-to-≡ isSetTy p i $ ⌜ v +V σ ⌝V) ⟩
    (tr (Tm Γ) Π[] ⌜ f +NV σ ⌝NV) $ ⌜ v +V σ ⌝V
      ≅⟨ apd (λ x → tr (Tm Γ) Π[] x $ ⌜ v +V σ ⌝V) (⌜⌝+NV {v = f}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NV [ ⌜ σ ⌝w ])) $ ⌜ v +V σ ⌝V
      ≅⟨ apd ((tr (Tm Γ) Π[] (⌜ f ⌝NV [ ⌜ σ ⌝w ])) $_) (⌜⌝+V {v = v}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NV [ ⌜ σ ⌝w ])) $ (⌜ v ⌝V [ ⌜ σ ⌝w ])
      ≅⟨ $[] ≅⁻¹ ⟩'
    (⌜ f ⌝NV $ ⌜ v ⌝V) [ ⌜ σ ⌝w ] ≅∎)

  ⌜⌝+E {ρ = ε} = εη ⁻¹
  ⌜⌝+E {Γ} {Δ} {Θ , A} {ρ , v} {σ} =
    let p : ⌜ ρ +E σ ⌝E ≡ ⌜ ρ ⌝E ∘ ⌜ σ ⌝w
        p = ⌜⌝+E
        q : ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V
            ≅[ Tm Γ ]
            tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V [ ⌜ σ ⌝w ])
        q = ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V
              ≅⟨ apd ⌜_⌝V (trfill (Val Γ) ([+E] ⁻¹) (v +V σ)) ⁻¹ ⟩
            ⌜ v +V σ ⌝V
              ≅⟨ ⌜⌝+V {v = v} ⟩
            ⌜ v ⌝V [ ⌜ σ ⌝w ]
              ≅⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩
            tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V [ ⌜ σ ⌝w ]) ≅∎
    in ≅-to-≡ {B = Tms Γ} isSetCon (
    ⌜ ρ +E σ ⌝E , ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V
      ≅⟨ (λ i → p i , ≅-to-≡[] isSetTy q {P = ap (A [_]T) p} i) ⟩
    (⌜ ρ ⌝E ∘ ⌜ σ ⌝w) , (tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V [ ⌜ σ ⌝w ]))
      ≅⟨ ,∘ ⁻¹ ⟩
    (⌜ ρ ⌝E , ⌜ v ⌝V) ∘ ⌜ σ ⌝w ≅∎)



-- Functoriality of weakening (values form a presheaf over the category of weakenings).
private
  abstract
    [⌜id⌝]T : {Γ : Con} {A : Ty Γ} → A [ ⌜ idw ⌝w ]T ≡ A
    [⌜id⌝]T {Γ} {A} =
      A [ ⌜ idw ⌝w ]T ≡⟨ ap (A [_]T) ⌜idw⌝ ⟩
      A [ id ]T      ≡⟨ [id]T ⟩
      A              ∎
    [⌜∘⌝]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
             A [ ⌜ σ ∘w ν ⌝w ]T ≡ A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T
    [⌜∘⌝]T {Γ} {Δ} {Θ} {A} {σ} {ν} =
      A [ ⌜ σ ∘w ν ⌝w ]T       ≡⟨ ap (A [_]T) ⌜∘⌝w ⟩
      A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]T    ≡⟨ [][]T ⟩
      A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T ∎

abstract
  -- The path/truncation constructor make it hard to use heterogeneous equality only.
  +Vid : {Γ : Con} {A : Ty Γ} {v : Val Γ A} → v +V idw ≡[ ap (Val Γ) [⌜id⌝]T ]≡ v
  +NVid : {Γ : Con} {A : Ty Γ} {v : NV Γ A} → v +NV idw ≡[ ap (NV Γ) [⌜id⌝]T ]≡ v
  +Eid : {Γ Δ : Con} {ρ : Env Γ Δ} → ρ +E idw ≡ ρ

  +Vid {Γ} {A} {lam u ρ} = ≅-to-≡[] {B = Val Γ} isSetTy (
    tr (Val Γ) [+E] (lam u (ρ +E idw))
      ≅⟨ trfill (Val Γ) [+E] (lam u (ρ +E idw)) ⁻¹ ⟩
    lam u (ρ +E idw)
      ≅⟨ apd (Val.lam u) (+Eid {ρ = ρ}) ⟩
    lam u ρ ≅∎)
  +Vid {v = neu v} = apd neu +NVid
  +Vid {v = veq {u = u} {v} p j} i =
    let IHu = +Vid {v = u}
        IHv = +Vid {v = v}
        r = λ j → (veq {u = u} {v} p j) +V idw
        s = veq {u = u} {v} p
    in ouc (isSetFillDependentSquare isSetVal r s IHu IHv i j)
  +Vid {v = isSetVal {x = u} {v} p q i j} k =
    ouc (isSetPartial isSetVal
                      (λ j → +Vid {v = p j} k)
                      (λ j → +Vid {v = q j} k)
                      (λ {(k = i0) → λ i j →
                          (isSetVal p q i j) +V idw;
                          (k = i1) → isSetVal p q}))
        i j
  +NVid {v = var x} = apd var (≅-to-≡[] isSetTy +vid)
  +NVid {Γ} {v = app {A = A} {B} f v} =
    let p : tr (NV Γ) Π[] (f +NV idw) ≅[ NV Γ ] f
        p = tr (NV Γ) Π[] (f +NV idw) ≅⟨ trfill (NV Γ) Π[] _ ⁻¹ ⟩
            f +NV idw                 ≅⟨ +NVid ⟩
            f                         ≅∎
        q : v +V idw ≅[ Val Γ ] v
        q = v +V idw ≅⟨ +Vid ⟩
            v ≅∎
        r : A [ ⌜ idw ⌝w ]T ≡ A
        r = [⌜id⌝]T
        s : B [ ⌜ idw ⌝w ↑ A ]T ≡[ ap (λ x → Ty (Γ , x)) r ]≡ B
        s = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ]T ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜idw⌝ ⟩
            B [ id ↑ A ]T      ≅⟨ ap≅ (B [_]T) ↑id ⟩'
            B [ id ]T          ≅⟨ [id]T ⟩
            B                  ≅∎)
    in ≅-to-≡[] {B = NV Γ} isSetTy (
      tr (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV idw)) (v +V idw))
        ≅⟨ trfill (NV Γ) ([<>][] {v = v}) _ ⁻¹ ⟩
      app (tr (NV Γ) Π[] (f +NV idw)) (v +V idw)
        ≅⟨ (λ i → app (≅-to-≡[] isSetTy p {P = λ i → Π (r i) (s i)} i)
                      (≅-to-≡[] isSetTy q {P = r} i)) ⟩
      app f v ≅∎)
  +Eid {ρ = ε} = refl
  +Eid {Γ} {Δ , A} {ρ , v} i =
    let p : ρ +E idw ≡ ρ
        p = +Eid
        q : tr (Val Γ) ([+E] ⁻¹) (v +V idw) ≅[ Val Γ ] v
        q = tr (Val Γ) ([+E] ⁻¹) (v +V idw) ≅⟨ trfill (Val Γ) ([+E] ⁻¹) (v +V idw) ⁻¹ ⟩
            v +V idw                        ≅⟨ +Vid ⟩
            v                               ≅∎
    in p i , ≅-to-≡[] isSetTy q {P = apd (λ x → A [ ⌜ x ⌝E ]T) p} i



  +V∘ : {Γ Δ Θ : Con} {A : Ty Θ} {v : Val Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        v +V (σ ∘w ν) ≡[ ap (Val Γ) [⌜∘⌝]T ]≡ (v +V σ) +V ν
  +NV∘ : {Γ Δ Θ : Con} {A : Ty Θ} {v : NV Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
         v +NV (σ ∘w ν) ≡[ ap (NV Γ) [⌜∘⌝]T ]≡ (v +NV σ) +NV ν
  +E∘ : {Γ Δ Θ Ψ : Con} {ρ : Env Θ Ψ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        ρ +E (σ ∘w ν) ≡ (ρ +E σ) +E ν

  +V∘ {Γ} {Δ} {Θ} {_} {lam {Δ = Ψ} {A} {B} u ρ} {σ} {ν} = ≅-to-≡[] {B = Val Γ} isSetTy (
    tr (Val Γ) ([+E] {ρ = ρ} {σ ∘w ν}) (lam u (ρ +E (σ ∘w ν)))
      ≅⟨ trfill (Val Γ) [+E] _ ⁻¹ ⟩
    lam u (ρ +E (σ ∘w ν))
      ≅⟨ apd {B = λ ρ → Val Γ ((Π A B) [ ⌜ ρ ⌝E ]T)} (lam u) +E∘ ⟩
    lam u ((ρ +E σ) +E ν)
      ≅⟨ trfill (Val Γ) [+E] _ ⟩
    (lam u (ρ +E σ)) +V ν
      ≅⟨ apd (λ x → x +V ν) (trfill (Val Δ) [+E] (lam u (ρ +E σ))) ⟩
    ((lam u ρ) +V σ) +V ν ≅∎)
  +V∘ {v = neu v} = apd neu (+NV∘ {v = v})
  +V∘ {v = veq {u = u} {v} p j} {σ} {ν} i =
    let IHu = +V∘ {v = u} {σ} {ν}
        IHv = +V∘ {v = v} {σ} {ν}
        r = λ j → (veq {u = u} {v} p j) +V (σ ∘w ν)
        s = λ j → ((veq {u = u} {v} p j) +V σ) +V ν
    in ouc (isSetFillDependentSquare isSetVal r s IHu IHv i j)
  +V∘ {v = isSetVal {x = u} {v} p q i j} {σ} {ν} k =
    ouc (isSetPartial isSetVal
                      (λ j → +V∘ {v = p j} {σ} {ν} k)
                      (λ j → +V∘ {v = q j} {σ} {ν} k)
                      (λ {(k = i0) → λ i j →
                          (isSetVal p q i j) +V (σ ∘w ν);
                          (k = i1) → λ i j →
                          ((isSetVal p q i j) +V σ) +V ν}))
        i j

  +NV∘ {v = var x} = apd var (≅-to-≡[] isSetTy (+v∘ {x = x}))
  +NV∘ {Γ} {Δ} {Θ} {_} {app {A = A} {B} f v} {σ} {ν} =
    let p : tr (NV Γ) Π[] (f +NV (σ ∘w ν))
            ≅[ NV Γ ]
            tr (NV Γ) Π[]
               ((tr (NV Δ) Π[] (f +NV σ)) +NV ν)
        p = tr (NV Γ) Π[] (f +NV (σ ∘w ν))
              ≅⟨ trfill (NV Γ) Π[] (f +NV (σ ∘w ν)) ⁻¹ ⟩
            f +NV (σ ∘w ν)
              ≅⟨ +NV∘ {v = f} ⟩
            (f +NV σ) +NV ν
              ≅⟨ apd (λ x → x +NV ν) (trfill (NV Δ) Π[] (f +NV σ)) ⟩
            (tr (NV Δ) Π[] (f +NV σ)) +NV ν
              ≅⟨ trfill (NV Γ) Π[] _ ⟩
            tr (NV Γ) Π[]
               ((tr (NV Δ) Π[] (f +NV σ)) +NV ν) ≅∎
        q : v +V (σ ∘w ν) ≅[ Val Γ ] (v +V σ) +V ν
        q = ≡[]-to-≅ (+V∘ {v = v})
        r : A [ ⌜ σ ∘w ν ⌝w ]T ≡ A [ ⌜ σ ⌝w ]T [ ⌜ ν ⌝w ]T
        r = [⌜∘⌝]T
        s : B [ ⌜ σ ∘w ν ⌝w ↑ A ]T
            ≡[ ap (λ x → Ty (Γ , x)) r ]≡
            B [ ⌜ σ ⌝w ↑ A ]T [ ⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ]T) ]T
        s = ≅-to-≡[] {B = Ty} isSetCon ((
            B [ ⌜ σ ∘w ν ⌝w ↑ A ]T
              ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜∘⌝w ⟩
            B [ (⌜ σ ⌝w ∘ ⌜ ν ⌝w) ↑ A ]T
              ≅⟨ ap≅ (B [_]T) ↑∘↑ ≅⁻¹ ⟩'
            B [ (⌜ σ ⌝w ↑ A) ∘ (⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ]T)) ]T
              ≅⟨ [][]T ⟩
            B [ ⌜ σ ⌝w ↑ A ]T [ ⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ]T) ]T ≅∎))
    in ≅-to-≡[] {B = NV Γ} isSetTy (
       (app f v) +NV (σ ∘w ν)
         ≅⟨ trfill (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV (σ ∘w ν))) (v +V (σ ∘w ν))) ⁻¹ ⟩
       app (tr (NV Γ) Π[] (f +NV (σ ∘w ν))) (v +V (σ ∘w ν))
         ≅⟨ (λ i → app (≅-to-≡[] isSetTy p {P = λ i → Π (r i) (s i)} i)
                       (≅-to-≡[] isSetTy q {P = r} i)) ⟩
       app (tr (NV Γ) Π[] ((tr (NV Δ) Π[] (f +NV σ)) +NV ν)) ((v +V σ) +V ν)
         ≅⟨ trfill (NV Γ) ([<>][] {v = v +V σ}) _ ⟩
       (app (tr (NV Δ) Π[] (f +NV σ)) (v +V σ)) +NV ν
         ≅⟨ apd (_+NV ν) (trfill (NV Δ) ([<>][] {v = v}) _) ⟩
       ((app f v) +NV σ) +NV ν ≅∎)
  +E∘ {ρ = ε} = refl
  +E∘ {Γ} {Δ} {Θ} {Ψ , A} {ρ , v} {σ} {ν} i =
    let p : ρ +E (σ ∘w ν) ≡ (ρ +E σ) +E ν
        p = +E∘
        q : tr (Val Γ) ([+E] ⁻¹) (v +V (σ ∘w ν))
            ≅[ Val Γ ]
            tr (Val Γ) ([+E] ⁻¹)
               ((tr (Val Δ) ([+E] ⁻¹) (v +V σ)) +V ν)
        q = tr (Val Γ) ([+E] ⁻¹) (v +V (σ ∘w ν))
              ≅⟨ trfill (Val Γ) ([+E] ⁻¹) (v +V (σ ∘w ν)) ⁻¹ ⟩
            v +V (σ ∘w ν)
              ≅⟨ +V∘ {v = v} ⟩
            (v +V σ) +V ν
              ≅⟨ apd (λ x → x +V ν) (trfill (Val Δ) ([+E] ⁻¹) (v +V σ)) ⟩
            (tr (Val Δ) ([+E] ⁻¹) (v +V σ)) +V ν
              ≅⟨ trfill (Val Γ) ([+E] ⁻¹) _ ⟩
            tr (Val Γ) ([+E] ⁻¹)
               ((tr (Val Δ) ([+E] ⁻¹) (v +V σ)) +V ν) ≅∎
    in p i , ≅-to-≡[] isSetTy q {P = apd (λ x → A [ ⌜ x ⌝E ]T) p} i

