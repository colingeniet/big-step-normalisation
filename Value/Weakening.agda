{-# OPTIONS --cubical #-}

module Value.Weakening where

open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Syntax.Sets
open import Syntax.Equivalence
open import Variable.Variable
open import Variable.Lemmas
open import Value.Value


-- Weakening of values.
_+V_ : {Γ Δ : Con} {A : Ty Δ} → Val Δ A → (σ : Wk Γ Δ) → Val Γ (A [ ⌜ σ ⌝w ])
_+NV_ : {Γ Δ : Con} {A : Ty Δ} → NV Δ A → (σ : Wk Γ Δ) → NV Γ (A [ ⌜ σ ⌝w ])
_+E_ : {Γ Δ Θ : Con} → Env Δ Θ → Wk Γ Δ → Env Γ Θ

-- Weakening commutes with embedding (required to define weakening of the
-- veq path constructor).
⌜⌝+V : {Γ Δ : Con} {A : Ty Δ} {v : Val Δ A} {σ : Wk Γ Δ} →
       ⌜ v +V σ ⌝V ≈ ⌜ v ⌝V +t σ
⌜⌝+NV : {Γ Δ : Con} {A : Ty Δ} {v : NV Δ A} {σ : Wk Γ Δ} →
       ⌜ v +NV σ ⌝NV ≈ ⌜ v ⌝NV +t σ
⌜⌝+E : {Γ Δ Θ : Con} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
       ⌜ ρ +E σ ⌝E ≋ ⌜ ρ ⌝E +s σ


abstract
  [+E] : {Γ Δ Θ : Con} {A : Ty Θ} {ρ : Env Δ Θ} {σ : Wk Γ Δ} →
         A Ty.[ ⌜ ρ +E σ ⌝E ] ≡ A [ ⌜ ρ ⌝E ] [ ⌜ σ ⌝w ]
  [+E] {Γ} {Δ} {Θ} {A} {ρ} {σ} =
    A [ ⌜ ρ +E σ ⌝E ]      ≡⟨ A [ ⌜⌝+E ]≈T ⟩
    A [ ⌜ ρ ⌝E ∘ ⌜ σ ⌝w ]   ≡⟨ [][]T ⟩
    A [ ⌜ ρ ⌝E ] [ ⌜ σ ⌝w ] ∎

  [<>][] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {v : Val Δ A} {σ : Wk Γ Δ} →
           B [ ⌜ σ ⌝w ↑ A ] Ty.[ < ⌜ v +V σ ⌝V > ] ≡ B [ < ⌜ v ⌝V > ] [ ⌜ σ ⌝w ]
  [<>][] {Γ} {Δ} {A} {B} {v} {σ} =
    B [ ⌜ σ ⌝w ↑ A ] [ < ⌜ v +V σ ⌝V > ] ≡⟨ [][]T ⁻¹ ⟩
    B [ (⌜ σ ⌝w ↑ A) ∘ < ⌜ v +V σ ⌝V > ] ≡⟨ B [ ↑∘<> ]≈T ⟩
    B [ ⌜ σ ⌝w , ⌜ v +V σ ⌝V ]           ≡⟨ B [ refl≋ ,≋ ⌜⌝+V ]≈T  ⟩
    B [ ⌜ σ ⌝w , ⌜ v ⌝V [ ⌜ σ ⌝w ] ]     ≡⟨ B [ <>∘ ≋⁻¹ ]≈T ⟩
    B [ < ⌜ v ⌝V > ∘ ⌜ σ ⌝w ]            ≡⟨ [][]T ⟩
    B [ < ⌜ v ⌝V > ] [ ⌜ σ ⌝w ]          ∎


(lam u ρ) +V σ = tr (Val _) [+E] (lam u (ρ +E σ))
(neu v) +V σ = neu (v +NV σ)
(var x) +NV σ = var (x +v σ)
(app f v) +NV σ = tr (NV _) ([<>][] {v = v})
                     (app (tr (NV _) Π[] (f +NV σ)) (v +V σ))
ε +E _ = ε
(ρ , v) +E σ = ρ +E σ , tr (Val _) ([+E] ⁻¹) (v +V σ)

abstract
  ⌜⌝+V {Γ} {Δ} {A} {lam u ρ} {σ} =
    ⌜ tr (Val _) [+E] (lam u (ρ +E σ)) ⌝V ≈⟨ apd ⌜_⌝V (trfill (Val _) [+E] (lam u (ρ +E σ))) ⁻¹ ⟩'
    (lam u) [ ⌜ ρ +E σ ⌝E ]               ≈⟨ refl≈ [ ⌜⌝+E ]≈ ⟩
    (lam u) [ ⌜ ρ ⌝E ∘ ⌜ σ ⌝w ]           ≈⟨ [][] ⟩
    (lam u) [ ⌜ ρ ⌝E ] [ ⌜ σ ⌝w ]         ≈∎
  ⌜⌝+V {v = neu v} = ⌜⌝+NV {v = v}

  ⌜⌝+NV {v = var x} = ⌜⌝+v
  ⌜⌝+NV {Γ} {Δ} {A} {app {B = B} f v} {σ} =
    let p : ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV ≈ tr (Tm Γ) Π[] (⌜ f ⌝NV +t σ)
        p = ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV ≈⟨ apd ⌜_⌝NV (trfill (NV Γ) Π[] (f +NV σ)) ⁻¹ ⟩'
            ⌜ f +NV σ ⌝NV                 ≈⟨ ⌜⌝+NV {v = f} ⟩
            ⌜ f ⌝NV +t σ                  ≈⟨ trfill (Tm Γ) Π[] (⌜ f ⌝NV +t σ) ⟩'
            tr (Tm Γ) Π[] (⌜ f ⌝NV +t σ ) ≈∎
        q : tr (Tm Γ) ([id]T ⁻¹) ⌜ v +V σ ⌝V ≈ tr (Tm Γ) ([id]T ⁻¹) (⌜ v ⌝V +t σ)
        q = tr (Tm Γ) ([id]T ⁻¹) ⌜ v +V σ ⌝V ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) ⌜ v +V σ ⌝V ⁻¹ ⟩'
            ⌜ v +V σ ⌝V                      ≈⟨ ⌜⌝+V {v = v} ⟩
            ⌜ v ⌝V +t σ                      ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) (⌜ v ⌝V +t σ) ⟩'
            tr (Tm Γ) ([id]T ⁻¹) (⌜ v ⌝V +t σ) ≈∎
    in ⌜ tr (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV σ)) (v +V σ)) ⌝NV
         ≈⟨ apd ⌜_⌝NV (trfill (NV Γ) ([<>][] {v = v})
                              (app (tr (NV Γ) Π[] (f +NV σ)) (v +V σ))) ⁻¹ ⟩'
       ⌜ tr (NV Γ) Π[] (f +NV σ) ⌝NV $ ⌜ v +V σ ⌝V
         ≈⟨ (app≈ p) [ refl≋ ,≋ q ]≈ ⟩
       (tr (Tm Γ) Π[] (⌜ f ⌝NV +t σ)) $ (⌜ v ⌝V +t σ)
         ≈⟨ $[] ≈⁻¹ ⟩
       (⌜ f ⌝NV $ ⌜ v ⌝V) +t σ ≈∎

  ⌜⌝+E {ρ = ε} = εη ≋⁻¹
  ⌜⌝+E {Γ} {Δ} {Θ , A} {ρ , v} {σ} =
    let q : ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V ≈ tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V +t σ)
        q = ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V
              ≈⟨ apd ⌜_⌝V (trfill (Val Γ) ([+E] ⁻¹) (v +V σ)) ⁻¹ ⟩'
            ⌜ v +V σ ⌝V
              ≈⟨ ⌜⌝+V {v = v} ⟩
            ⌜ v ⌝V +t σ
              ≈⟨ trfill (Tm Γ) ([][]T ⁻¹) _ ⟩'
            tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V +t σ) ≈∎
    in ⌜ ρ +E σ ⌝E , ⌜ tr (Val Γ) ([+E] ⁻¹) (v +V σ) ⌝V        ≋⟨ ⌜⌝+E ,≋ q ⟩
       (⌜ ρ ⌝E ∘ ⌜ σ ⌝w) , (tr (Tm Γ) ([][]T ⁻¹) (⌜ v ⌝V +t σ)) ≋⟨ ,∘ ≋⁻¹ ⟩
       (⌜ ρ ⌝E , ⌜ v ⌝V) ∘ ⌜ σ ⌝w ≋∎



-- Functoriality of weakening (values form a presheaf over the category of weakenings).
private
  abstract
    [⌜id⌝]T : {Γ : Con} {A : Ty Γ} → A [ ⌜ idw ⌝w ] ≡ A
    [⌜id⌝]T {Γ} {A} =
      A [ ⌜ idw ⌝w ] ≡⟨ A [ ⌜idw⌝ ]≈T ⟩
      A [ id ]       ≡⟨ [id]T ⟩
      A              ∎
    [⌜∘⌝]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
             A [ ⌜ σ ∘w ν ⌝w ] ≡ A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ]
    [⌜∘⌝]T {Γ} {Δ} {Θ} {A} {σ} {ν} =
      A [ ⌜ σ ∘w ν ⌝w ]      ≡⟨ A [ ⌜∘⌝w ]≈T ⟩
      A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]   ≡⟨ [][]T ⟩
      A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ∎

abstract
  +Vid : {Γ : Con} {A : Ty Γ} {v : Val Γ A} → v +V idw ≅[ Val Γ ] v
  +NVid : {Γ : Con} {A : Ty Γ} {v : NV Γ A} → v +NV idw ≅[ NV Γ ] v
  +Eid : {Γ Δ : Con} {ρ : Env Γ Δ} → ρ +E idw ≡ ρ

  +Vid {Γ} {A} {lam u ρ} =
    tr (Val Γ) [+E] (lam u (ρ +E idw))
      ≅⟨ trfill (Val Γ) [+E] (lam u (ρ +E idw)) ⁻¹ ⟩
    lam u (ρ +E idw)
      ≅⟨ apd (Val.lam u) (+Eid {ρ = ρ}) ⟩
    lam u ρ ≅∎
  +Vid {v = neu v} = ap≅ neu +NVid
  +NVid {v = var x} = ap≅ var +vid
  +NVid {Γ} {v = app {A = A} {B} f v} =
    let p : tr (NV Γ) Π[] (f +NV idw) ≅[ NV Γ ] f
        p = tr (NV Γ) Π[] (f +NV idw) ≅⟨ trfill (NV Γ) Π[] _ ⁻¹ ⟩
            f +NV idw                 ≅⟨ +NVid ⟩'
            f                         ≅∎
        q : v +V idw ≅[ Val Γ ] v
        q = v +V idw ≅⟨ +Vid ⟩'
            v ≅∎
        r : A [ ⌜ idw ⌝w ] ≡ A
        r = [⌜id⌝]T
        t : B [ ⌜ idw ⌝w ↑ A ] ≡[ ap (λ x → Ty (Γ , x)) r ]≡ B
        t = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ] ≅⟨ refl≅ [ ⌜idw⌝ ↑≋ refl≅ ]≈d ⟩'
            B [ id ↑ A ]      ≅⟨ refl≅ [ ↑id ]≈d ⟩'
            B [ id ]          ≅⟨ [id]T ⟩
            B                 ≅∎)
    in tr (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV idw)) (v +V idw))
         ≅⟨ trfill (NV Γ) ([<>][] {v = v}) _ ⁻¹ ⟩
       app (tr (NV Γ) Π[] (f +NV idw)) (v +V idw)
         ≅⟨ (λ i → app (≅-to-≡[] isSetTy p {P = λ i → Π (r i) (t i)} i)
                       (≅-to-≡[] isSetTy q {P = r} i)) ⟩
       app f v ≅∎
  +Eid {ρ = ε} = refl
  +Eid {Γ} {Δ , A} {ρ , v} i =
    let p : ρ +E idw ≡ ρ
        p = +Eid
        q : tr (Val Γ) ([+E] ⁻¹) (v +V idw) ≅[ Val Γ ] v
        q = tr (Val Γ) ([+E] ⁻¹) (v +V idw) ≅⟨ trfill (Val Γ) ([+E] ⁻¹) (v +V idw) ⁻¹ ⟩
            v +V idw                        ≅⟨ +Vid ⟩'
            v                               ≅∎
    in p i , ≅-to-≡[] isSetTy q {P = apd (λ x → A [ ⌜ x ⌝E ]) p} i



  +V∘ : {Γ Δ Θ : Con} {A : Ty Θ} {v : Val Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        v +V (σ ∘w ν) ≅[ Val Γ ] (v +V σ) +V ν
  +NV∘ : {Γ Δ Θ : Con} {A : Ty Θ} {v : NV Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
         v +NV (σ ∘w ν) ≅[ NV Γ ] (v +NV σ) +NV ν
  +E∘ : {Γ Δ Θ Ψ : Con} {ρ : Env Θ Ψ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        ρ +E (σ ∘w ν) ≡ (ρ +E σ) +E ν

  +V∘ {Γ} {Δ} {Θ} {_} {lam {Δ = Ψ} {A} {B} u ρ} {σ} {ν} =
    tr (Val Γ) ([+E] {ρ = ρ} {σ ∘w ν}) (lam u (ρ +E (σ ∘w ν)))
      ≅⟨ trfill (Val Γ) [+E] _ ⁻¹ ⟩
    lam u (ρ +E (σ ∘w ν))
      ≅⟨ apd {B = λ ρ → Val Γ ((Π A B) [ ⌜ ρ ⌝E ])} (lam u) +E∘ ⟩
    lam u ((ρ +E σ) +E ν)
      ≅⟨ trfill (Val Γ) [+E] _ ⟩
    (lam u (ρ +E σ)) +V ν
      ≅⟨ apd (λ x → x +V ν) (trfill (Val Δ) [+E] (lam u (ρ +E σ))) ⟩
    ((lam u ρ) +V σ) +V ν ≅∎
  +V∘ {v = neu v} = ap≅ neu (+NV∘ {v = v})

  +NV∘ {v = var x} = ap≅ var (+v∘ {x = x})
  +NV∘ {Γ} {Δ} {Θ} {_} {app {A = A} {B} f v} {σ} {ν} =
    let p : tr (NV Γ) Π[] (f +NV (σ ∘w ν))
            ≅[ NV Γ ]
            tr (NV Γ) Π[]
               ((tr (NV Δ) Π[] (f +NV σ)) +NV ν)
        p = tr (NV Γ) Π[] (f +NV (σ ∘w ν))
              ≅⟨ trfill (NV Γ) Π[] (f +NV (σ ∘w ν)) ⁻¹ ⟩
            f +NV (σ ∘w ν)
              ≅⟨ +NV∘ {v = f} ⟩'
            (f +NV σ) +NV ν
              ≅⟨ apd (λ x → x +NV ν) (trfill (NV Δ) Π[] (f +NV σ)) ⟩
            (tr (NV Δ) Π[] (f +NV σ)) +NV ν
              ≅⟨ trfill (NV Γ) Π[] _ ⟩
            tr (NV Γ) Π[]
               ((tr (NV Δ) Π[] (f +NV σ)) +NV ν) ≅∎
        q : v +V (σ ∘w ν) ≅[ Val Γ ] (v +V σ) +V ν
        q = +V∘ {v = v}
        r : A [ ⌜ σ ∘w ν ⌝w ] ≡ A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ]
        r = [⌜∘⌝]T
        s : B [ ⌜ σ ∘w ν ⌝w ↑ A ]
            ≡[ ap (λ x → Ty (Γ , x)) r ]≡
            B [ ⌜ σ ⌝w ↑ A ] [ ⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ]) ]
        s = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ σ ∘w ν ⌝w ↑ A ]
              ≅⟨ refl≅ [ ⌜∘⌝w ↑≋ refl≅ ]≈d ⟩'
            B [ (⌜ σ ⌝w ∘ ⌜ ν ⌝w) ↑ A ]
              ≅⟨ refl≅ [ ↑∘↑ ≋⁻¹ ]≈d ⟩'
            B [ (⌜ σ ⌝w ↑ A) ∘ (⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ])) ]
              ≅⟨ [][]T ⟩
            B [ ⌜ σ ⌝w ↑ A ] [ ⌜ ν ⌝w ↑ (A [ ⌜ σ ⌝w ]) ] ≅∎)
    in (app f v) +NV (σ ∘w ν)
         ≅⟨ trfill (NV Γ) ([<>][] {v = v}) (app (tr (NV Γ) Π[] (f +NV (σ ∘w ν))) (v +V (σ ∘w ν))) ⁻¹ ⟩
       app (tr (NV Γ) Π[] (f +NV (σ ∘w ν))) (v +V (σ ∘w ν))
         ≅⟨ (λ i → app (≅-to-≡[] isSetTy p {P = λ i → Π (r i) (s i)} i)
                       (≅-to-≡[] isSetTy q {P = r} i)) ⟩
       app (tr (NV Γ) Π[] ((tr (NV Δ) Π[] (f +NV σ)) +NV ν)) ((v +V σ) +V ν)
         ≅⟨ trfill (NV Γ) ([<>][] {v = v +V σ}) _ ⟩
       (app (tr (NV Δ) Π[] (f +NV σ)) (v +V σ)) +NV ν
         ≅⟨ apd (_+NV ν) (trfill (NV Δ) ([<>][] {v = v}) _) ⟩
       ((app f v) +NV σ) +NV ν ≅∎

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
              ≅⟨ +V∘ {v = v} ⟩'
            (v +V σ) +V ν
              ≅⟨ apd (λ x → x +V ν) (trfill (Val Δ) ([+E] ⁻¹) (v +V σ)) ⟩
            (tr (Val Δ) ([+E] ⁻¹) (v +V σ)) +V ν
              ≅⟨ trfill (Val Γ) ([+E] ⁻¹) _ ⟩
            tr (Val Γ) ([+E] ⁻¹)
               ((tr (Val Δ) ([+E] ⁻¹) (v +V σ)) +V ν) ≅∎
    in p i , ≅-to-≡[] isSetTy q {P = apd (λ x → A [ ⌜ x ⌝E ]) p} i

