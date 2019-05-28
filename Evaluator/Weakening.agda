{-# OPTIONS --cubical #-}

module Evaluator.Weakening where


open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator


[↑][<>] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {v : Val Δ A} {σ : Wk Γ Δ} →
          B [ < ⌜ v ⌝V > ]T [ ⌜ σ ⌝w ]T ≡ B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ v +V σ ⌝V > ]T
[↑][<>] {Γ} {Δ} {A} {B} {v} {σ} = ≅-to-≡ {B = Ty} isSetCon (
  B [ < ⌜ v ⌝V > ]T [ ⌜ σ ⌝w ]T
    ≅⟨ [][]T ⁻¹ ⟩
  B [ < ⌜ v ⌝V > ∘ ⌜ σ ⌝w ]T
    ≅⟨ ap (B [_]T) <>∘ ⟩
  B [ ⌜ σ ⌝w , ⌜ v ⌝V [ ⌜ σ ⌝w ] ]T
    ≅⟨ ap (λ x → B [ ⌜ σ ⌝w , x ]T) (⌜⌝+V {v = v} ⁻¹) ⟩
  B [ ⌜ σ ⌝w , ⌜ v +V σ ⌝V ]T
    ≅⟨ [↑∘<>] ⟩
  B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ v +V σ ⌝V > ]T ≅∎)

-- All computations can be weakened.
_+eval_ : {Γ Δ Θ : Con} {A : Ty Θ} {u : Tm Θ A} {ρ : Env Δ Θ}
          {uρ : Val Δ (A [ ⌜ ρ ⌝E ]T)} → eval u > ρ ⇒ uρ → (σ : Wk Γ Δ) →
          eval u > (ρ +E σ) ⇒ tr (Val Γ) ([+E] ⁻¹) (uρ +V σ)
_+evals_ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ρ : Env Δ Θ}
           {σρ : Env Δ Ψ} → evals σ > ρ ⇒ σρ → (ν : Wk Γ Δ) →
           evals σ > (ρ +E ν) ⇒ (σρ +E ν)
_+$_ : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {f : Val Δ (Π A B)} {v : Val Δ A}
       {fv : Val Δ (B [ < ⌜ v ⌝V > ]T)} → f $ v ⇒ fv → (σ : Wk Γ Δ) →
       tr (Val _) Π[] (f +V σ) $ (v +V σ) ⇒ tr (Val Γ) ([↑][<>] {v = v}) (fv +V σ)

evalsid +evals δ = evalsid
(evals∘ cν cσ) +evals δ = evals∘ (cν +evals δ) (cσ +evals δ)
evalsε +evals δ = evalsε
(evals, {σ = σ} {u} {ρ} {σρ} {uρ} cσ cu) +evals δ =
  let evalsσu : evals σ , u > ρ +E δ ⇒
                  ((σρ +E δ) ,
                   tr (Val _) ([evals≡] (cσ +evals δ) ⁻¹)
                   (tr (Val _) ([+E] ⁻¹) (uρ +V δ)))
      evalsσu = evals, (cσ +evals δ) (cu +eval δ)
      p : tr (Val _) ([evals≡] (cσ +evals δ) ⁻¹) (tr (Val _) ([+E] ⁻¹) (uρ +V δ))
          ≡ tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] cσ ⁻¹) uρ +V δ)
      p = ≅-to-≡ {B = Val _} isSetTy (
          tr (Val _) ([evals≡] (cσ +evals δ) ⁻¹) (tr (Val _) ([+E] ⁻¹) (uρ +V δ))
            ≅⟨ trfill (Val _) ([evals≡] (cσ +evals δ) ⁻¹) _ ⁻¹ ⟩
          tr (Val _) ([+E] ⁻¹) (uρ +V δ)
            ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⁻¹ ⟩
          uρ +V δ
            ≅⟨ apd (_+V δ) (trfill (Val _) ([evals≡] cσ ⁻¹) uρ) ⟩
          (tr (Val _) ([evals≡] cσ ⁻¹) uρ) +V δ
            ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⟩
          tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] cσ ⁻¹) uρ +V δ) ≅∎)
  in tr (λ x → evals σ , u > ρ +E δ ⇒ (σρ +E δ , x)) p evalsσu
(evalsπ₁ {σρ = σρ} cσ) +evals δ =
  tr (λ x → evals _ > _ ⇒ x) (π₁+ {ρ = σρ} {σ = δ}) (evalsπ₁ (cσ +evals δ))
(isPropevals x y i) +evals δ = isPropevals (x +evals δ) (y +evals δ) i


(eval[] {u = u} {σ} {ρ} {σρ} {uσρ} cσ cu) +eval δ =
  let evaluσ = eval[] (cσ +evals δ) (cu +eval δ)
      p : tr (Val _) ([evals≡] (cσ +evals δ)) (tr (Val _) ([+E] ⁻¹) (uσρ +V δ))
          ≡ tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] cσ) uσρ +V δ)
      p = ≅-to-≡ {B = Val _} isSetTy (
          tr (Val _) ([evals≡] (cσ +evals δ)) (tr (Val _) ([+E] ⁻¹) (uσρ +V δ))
            ≅⟨ trfill (Val _) ([evals≡] (cσ +evals δ)) _ ⁻¹ ⟩
          tr (Val _) ([+E] ⁻¹) (uσρ +V δ)
            ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⁻¹ ⟩
          uσρ +V δ
            ≅⟨ apd (_+V δ) (trfill (Val _) ([evals≡] cσ) uσρ) ⟩
          (tr (Val _) ([evals≡] cσ) uσρ) +V δ
            ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⟩
          tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] cσ) uσρ +V δ) ≅∎)
  in tr (λ x → eval u [ σ ] > ρ +E δ ⇒ x) p evaluσ
(evalπ₂ {σ = σ} {ρ} {σρ} cσ) +eval δ =
  let evalπσ = evalπ₂ (cσ +evals δ)
      p : tr (Val _) ([evals≡] (evalsπ₁ (cσ +evals δ))) (π₂E (σρ +E δ))
          ≡ tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ) +V δ)
      p = ≅-to-≡ {B = Val _} isSetTy (
          tr (Val _) ([evals≡] (evalsπ₁ (cσ +evals δ))) (π₂E (σρ +E δ))
            ≅⟨ trfill (Val _) ([evals≡] (evalsπ₁ (cσ +evals δ))) (π₂E (σρ +E δ)) ⁻¹ ⟩
          π₂E (σρ +E δ)
            ≅⟨ π₂+ {ρ = σρ} ⟩'
          π₂E σρ +V δ
            ≅⟨ apd (_+V δ) (trfill (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ)) ⟩
          (tr (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ)) +V δ
            ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⟩
          tr (Val _) ([+E] ⁻¹) (tr (Val _) ([evals≡] (evalsπ₁ cσ)) (π₂E σρ) +V δ) ≅∎)
  in tr (λ x → eval π₂ σ > ρ +E δ ⇒ x) p evalπσ
(evallam u ρ) +eval δ =
  let evallamu = evallam u (ρ +E δ)
      p : lam u (ρ +E δ) ≡ tr (Val _) ([+E] ⁻¹) ((lam u ρ) +V δ)
      p = ≅-to-≡ {B = Val _} isSetTy (
          lam u (ρ +E δ)
            ≅⟨ trfill (Val _) [+E] (lam u (ρ +E δ)) ⟩
          (lam u ρ) +V δ
            ≅⟨ trfill (Val _) ([+E] ⁻¹) ((lam u ρ) +V δ) ⟩
          tr (Val _) ([+E] ⁻¹) (lam u ρ +V δ) ≅∎)
  in tr (λ x → eval lam u > ρ +E δ ⇒ x) p evallamu
(evalapp {f = f} {ρ} {v} {fρ} {fρv} cf $fρ) +eval δ =
  let v+ = v +V δ
      v+' = tr (Val _) ([+E] ⁻¹) (v +V δ)
      v+≡v+' : v+ ≡[ ap (Val _) ([+E] ⁻¹) ]≡ v+'
      v+≡v+' = trfill (Val _) ([+E] ⁻¹) (v +V δ)
      fρ+ = tr (Val _) ([+E] ⁻¹) (fρ +V δ)
      fρ+' = tr (Val _) Π[] fρ +V δ
      fρ+≡fρ+' : fρ+ ≅[ Val _ ] fρ+'
      fρ+≡fρ+' = tr (Val _) ([+E] ⁻¹) (fρ +V δ) ≅⟨ trfill (Val _) ([+E] ⁻¹) (fρ +V δ) ⁻¹ ⟩
                 fρ +V δ                        ≅⟨ apd (_+V δ) (trfill (Val _) Π[] fρ) ⟩
                 (tr (Val _) Π[] fρ) +V δ ≅∎
      evalf+ : eval f > ρ +E δ ⇒ fρ+
      evalf+ = cf +eval δ
      p : tr (Val _) Π[] fρ+ ≅[ Val _ ] tr (Val _) Π[] fρ+'
      p = tr (Val _) Π[] fρ+ ≅⟨ trfill (Val _) Π[] fρ+ ⁻¹ ⟩
          fρ+                ≅⟨ fρ+≡fρ+' ⟩'
          fρ+'               ≅⟨ trfill (Val _) Π[] fρ+' ⟩
          tr (Val _) Π[] fρ+' ≅∎
      $fρ+ : tr (Val _) Π[] fρ+' $ v+
               ⇒ tr (Val _) ([↑][<>] {v = v}) (fρv +V δ)
      $fρ+ = $fρ +$ δ
      $fρ+' : tr (Val _) Π[] fρ+ $ v+'
                ⇒ tr (Val _) {!!} (fρv +V δ)
      $fρ+' = (λ i → ≅-to-≡[] isSetTy p {P = {!!}} i
                     $ v+≡v+' i
                     ⇒ {!!})
              * $fρ+
      evalappf : eval app f > (ρ , v) +E δ ⇒ {!!}
      evalappf = evalapp evalf+ $fρ+'
  in {!evalapp evalf+ $fρ+'!}
(isPropeval x y i) +eval δ = isPropeval (x +eval δ) (y +eval δ) i


($lam {u = u} {ρ} {v} {uρv} cu) +$ σ =
  let lamu+ = lam u (ρ +E σ)
      lamu+' = (tr (Val _) Π[] (lam u ρ)) +V σ
      v+' = v +V σ
      v+ = tr (Val _) ([+E] ⁻¹) v+'
      uρv+ = tr (Val _) [↑∘<>] (tr (Val _) ([+E] ⁻¹) (uρv +V σ))
      uρv+' = tr (Val _) [↑][<>] (tr (Val _) [↑∘<>] uρv +V σ)
      $lamuρv+ = $lam (cu +eval σ)
  in {!!} * $lamuρv+
($app n v) +$ σ =
  let n+ = tr (NV _) Π[] (n +NV σ)
      n+' = tr (Val _) Π[] (neu (n +NV σ))
      n+≡n+' : neu n+ ≡ n+'
      n+≡n+' = ≅-to-≡ {B = Val _} isSetTy (
               neu n+        ≅⟨ apd neu (trfill (NV _) Π[] (n +NV σ)) ⁻¹ ⟩
               neu (n +NV σ) ≅⟨ trfill (Val _) Π[] (neu (n +NV σ)) ⟩
               n+'           ≅∎)
      nv = neu (app n+ (v +V σ))
      nv' = tr (Val _) ([↑][<>] {v = v}) (neu (tr (NV _) ([<>][] {v = v}) (app n+ (v +V σ))))
      nv≡nv' : nv ≡ nv'
      nv≡nv' = ≅-to-≡ {B = Val _} isSetTy (
               neu (app n+ (v +V σ))
                 ≅⟨ apd neu (trfill (NV _) ([<>][] {v = v}) _) ⟩
               neu (tr (NV _) ([<>][] {v = v}) (app n+ (v +V σ)))
                 ≅⟨ trfill (Val _) ([↑][<>] {v = v}) _ ⟩
               tr (Val _) ([↑][<>] {v = v}) (neu (tr (NV _) ([<>][] {v = v}) (app n+ (v +V σ)))) ≅∎)
      $nv : neu n+ $ v +V σ ⇒ nv
      $nv = $app n+ (v +V σ)
  in (λ i → n+≡n+' i $ v +V σ ⇒ nv≡nv' i) * $nv
(isProp$ x y i) +$ σ = isProp$ (x +$ σ) (y +$ σ) i


{-
_+q_ : {Γ Δ : Con} {A : Ty} {v : Val Δ A} {n : Nf Δ A} →
       q v ⇒ n → (σ : Wk Γ Δ) → q (v +V σ) ⇒ (n +N σ)
_+qs_ : {Γ Δ : Con} {A : Ty} {v : NV Δ A} {n : NN Δ A} →
        qs v ⇒ n → (σ : Wk Γ Δ) → qs (v +NV σ) ⇒ (n +NN σ)
(qo qv) +q δ = qo (qv +qs δ)
(q⟶ {A = A} {f = f} {fz = fz} $f qf) +q δ =
  let $f+ : ((f +V (wkwk A idw)) +V (wk↑ A δ))
            $ (neu (var z))
            ⇒ (fz +V (wk↑ A δ))
      $f+ = $f +$ (wk↑ A δ)
      p : (f +V wkwk A idw) +V wk↑ A δ
          ≡ (f +V δ) +V wkwk A idw
      p = (f +V wkwk A idw) +V wk↑ A δ     ≡⟨ +V∘ {v = f} ⁻¹ ⟩
          f +V ((wkwk A idw) ∘w (wk↑ A δ)) ≡⟨ ap (λ x → f +V x) wkid∘↑ ⟩
          f +V (δ ∘w (wkwk A idw))         ≡⟨ +V∘ {v = f} ⟩
          (f +V δ) +V (wkwk A idw)         ∎
      $f+' : ((f +V δ) +V (wkwk A idw))
             $ (neu (var z))
             ⇒ (fz +V (wk↑ A δ))
      $f+' = tr (λ x → x $ _ ⇒ _) p $f+
  in q⟶ $f+' (qf +q (wk↑ A δ))
(isPropq x y i) +q δ = isPropq (x +q δ) (y +q δ) i
qsvar +qs δ = qsvar
(qsapp qsf qv) +qs δ = qsapp (qsf +qs δ) (qv +q δ)
(isPropqs x y i) +qs δ = isPropqs (x +qs δ) (y +qs δ) i
-}
