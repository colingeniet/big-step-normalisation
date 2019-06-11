{-# OPTIONS --cubical --allow-unsolved-meta  #-}

{-
  Values are invariant by evaluation (in the identity environment),
  normal forms are invariant by normalisation.
-}

module Evaluator.Stability where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable
open import Variable.Lemmas
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import Evaluator.Evaluator
open import Evaluator.Weakening


abstract
  stable-var-aux : {Γ Δ : Con} {A : Ty Δ} (x : Var Δ A) (σ : Wk Γ Δ) →
                   eval ⌜ x ⌝v > (idenv +E σ) ⇒ neu (var (x +v σ))
  stable-var-aux z σ =
    let p : π₂E (idenv +E σ) ≅[ Val _ ] neu (var (z +v σ))
        p = tr (Val _) ([+E] ⁻¹) (tr (Val _) [⌜id+E⌝] (neu (var z)) +V σ)
              ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⁻¹ ⟩
            ((tr (Val _) [⌜id+E⌝] (neu (var z))) +V σ)
              ≅⟨ apd (_+V σ) (trfill (Val _) [⌜id+E⌝] (neu (var z))) ⁻¹ ⟩
            (neu (var z)) +V σ ≅∎
    in trd (eval ⌜ z ⌝v > (idenv +E σ) ⇒_)
           (≅-to-≡[] isSetTy p {P = [+E] ∙ ap (_[ ⌜ σ ⌝w ]T) [⌜id+E⌝] ⁻¹})
           (evalπ₂ evalsid)
  stable-var-aux (s x) (σ , y) =
    let evalx : eval ⌜ x ⌝v > (idenv +E σ) ⇒ neu (var (x +v σ))
        evalx = stable-var-aux x σ
        p : idenv +E σ ≡ (idenv +E wkw idw) +E (σ , y)
        p = idenv +E σ                    ≡⟨ ap (idenv +E_) id∘w ⁻¹ ⟩
            idenv +E (idw ∘w σ)           ≡⟨ ap (idenv +E_) wkw∘w ⁻¹ ⟩
            idenv +E (wkw idw ∘w (σ , y)) ≡⟨ +E∘ ⟩
            (idenv +E wkw idw) +E (σ , y) ∎
        evalx' : eval ⌜ x ⌝v > (idenv +E wkw idw) +E (σ , y)
                   ⇒ neu (var (tr (Var _) []wk, (x +v σ)))
        evalx' = (λ i → eval ⌜ x ⌝v > (p i)
                        ⇒ neu (var (trfill (Var _) ([]wk, {u = ⌜ y ⌝v}) (x +v σ) i)))
                 * evalx
    in eval[] (evalsπ₁ evalsid) evalx'

  stable-var : {Γ : Con} {A : Ty Γ} (x : Var Γ A) →
               eval ⌜ x ⌝v > idenv ⇒ neu (var x)
  stable-var x =
    (λ i → eval ⌜ x ⌝v > (+Eid {ρ = idenv} i)
           ⇒ neu (var (≅-to-≡[] isSetTy (+vid {x = x}) {P = ap (_ [_]T) ⌜idw⌝ ∙ [id]T} i)))
    * stable-var-aux x idw


  eval$-idenv : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} {f : Tm Γ (Π A B)} {u : Tm Γ A}
                {g : Val Γ (Π A B)} {v : Val Γ A} {gv : Val Γ (B [ < ⌜ v ⌝V > ]T)} →
                eval f > idenv ⇒ g → eval u > idenv ⇒ v → g $ v ⇒ gv →
                eval (f $ u) > idenv ⇒ gv
  eval$-idenv {Γ} {A} {B} {f} {u} {g} {v} {gv} evalf evalu $gv =
    let evalu' : eval (tr (Tm _) ([id]T ⁻¹) u) > idenv ⇒ v
        evalu' = trd (eval_> idenv ⇒ v) (trfill (Tm _) ([id]T ⁻¹) u) evalu
        P : A ≡ A [ ⌜ idenv ⌝E ]T
        P = evals,-aux evalsid evalu'
        Q : B ≡[ ap (λ x → Ty (Γ , x)) P ]≡ B [ ⌜ idenv ⌝E ↑ A ]T
        Q = ≅-to-≡[] {B = Ty} isSetCon (
            B                    ≅⟨ [id]T ⁻¹ ⟩
            B [ id ]T            ≅⟨ ap≅ (B [_]T) ↑id ≅⁻¹ ⟩'
            B [ id ↑ A ]T        ≅⟨ apd (λ x → B [ x ↑ A ]T) idenv≡ ⁻¹ ⟩
            B [ ⌜ idenv ⌝E ↑ A ]T ≅∎)
        R : Π A B ≡ Π (A [ ⌜ idenv ⌝E ]T) (B [ ⌜ idenv ⌝E ↑ A ]T)
        R i = Π (P i) (Q i)
        v' : Val Γ (A [ ⌜ idenv ⌝E ]T)
        v' = tr (Val Γ) P v
        v≡v' : v ≡[ ap (Val Γ) P ]≡ v'
        v≡v' = trfill (Val Γ) P v
        g' : Val Γ (Π (A [ ⌜ idenv ⌝E ]T) (B [ ⌜ idenv ⌝E ↑ A ]T))
        g' = tr (Val Γ) R g
        g≡g' : g ≡[ ap (Val Γ) R ]≡ g'
        g≡g' = trfill (Val Γ) R g
        evalf' : eval f > idenv ⇒ g'
        evalf' = trd (eval f > idenv ⇒_) g≡g' evalf
        $gv' : g' $ v' ⇒ gv
        $gv' = (λ i → (g≡g' i) $ (v≡v' i) ⇒ gv) * $gv
    in eval[] (evals, evalsid evalu')
              (evalapp evalf' $gv')


  -- Stability by evaluation for values, neutral values and environments.
  stable-val : {Γ : Con} {A : Ty Γ} (v : Val Γ A) →
               eval ⌜ v ⌝V > idenv ⇒ v
  stable-neval : {Γ : Con} {A : Ty Γ} (n : NV Γ A) →
                 eval ⌜ n ⌝NV > idenv ⇒ neu n
  stable-env : {Γ Δ : Con} (ρ : Env Γ Δ) →
               evals ⌜ ρ ⌝E > idenv ⇒ ρ

  stable-val (lam u ρ) = eval[] (stable-env ρ) (evallam u ρ)
  stable-val (neu n) = stable-neval n
  stable-val (veq {u = u} {v} p i) =
    isPropDependent {B = λ v → eval ⌜ v ⌝V > idenv ⇒ v}
                    isPropeval
                    (veq p) (stable-val u) (stable-val v) i
  stable-val (isSetVal p q i j) =
    isSetDependent2 {B = λ v → eval ⌜ v ⌝V > idenv ⇒ v}
                    isSetVal (PropisSet isPropeval)
                    (λ k → stable-val (p k))
                    (λ k → stable-val (q k)) i j

  stable-neval (var x) = stable-var x
  stable-neval (app n v) =
    eval$-idenv (stable-neval n) (stable-val v) ($app n v)

  stable-env ε = evalsε
  stable-env (ρ , v) =
    let evalρv : evals ⌜ ρ , v ⌝E > idenv
                   ⇒ (ρ , tr (Val _) (evals,-aux (stable-env ρ) (stable-val v)) v)
        evalρv = evals, (stable-env ρ) (stable-val v)
        p : tr (Val _) (evals,-aux (stable-env ρ) (stable-val v)) v ≡ v
        p = make-non-dependent {B = Val _} isSetTy
                               (trfill (Val _) (evals,-aux (stable-env ρ) (stable-val v)) v ⁻¹)
    in tr (λ x → evals ⌜ ρ , v ⌝E > idenv ⇒ (ρ , x)) p evalρv



  -- Stability by normalisation for normal forms and neutral normal forms.
  stable-nf : {Γ : Con} {A : Ty Γ} (n : Nf Γ A) →
              Σ[ v ∈ Val Γ A ] (eval ⌜ n ⌝N > idenv ⇒ v  ×  q v ⇒ n)
  stable-nenf : {Γ : Con} {A : Ty Γ} (n : NN Γ A) →
                Σ[ v ∈ NV Γ A ] (eval ⌜ n ⌝NN > idenv ⇒ neu v  ×  qs v ⇒ n)

  stable-nf (lam {Γ} {A} {B} n) =
    let v ,, evaln ,, qv = stable-nf n
        P : (Π A B) [ ⌜ idenv ⌝E ]T ≡ Π A B
        P = (Π A B) [ ⌜ idenv ⌝E ]T ≡⟨ ap (Π A B [_]T) idenv≡ ⟩
            (Π A B) [ id ]T        ≡⟨ [id]T ⟩
            Π A B                  ∎
        lamn : Val Γ (Π A B [ ⌜ idenv ⌝E ]T)
        lamn = lam ⌜ n ⌝N idenv
        evallamn : eval ⌜ lam n ⌝N > idenv ⇒ lamn
        evallamn = evallam ⌜ n ⌝N idenv
        lamn' : Val Γ (Π A B)
        lamn' = tr (Val Γ) P lamn
        evallamn' : eval ⌜ lam n ⌝N > idenv ⇒ lamn'
        evallamn' = trd (eval ⌜ lam n ⌝N > idenv ⇒_) (trfill (Val Γ) P lamn) evallamn
        lamn+ = lam ⌜ n ⌝N (idenv +E wkw idw)
        lamn+' = lamn' +V wkw idw
        $lamn+ : tr (Val _) Π[] lamn+ $ tr (Val _) [⌜id+E⌝] (neu (var z)) ⇒ v
        $lamn+ = $lam evaln
        p : ⌜ idenv +E wkw idw ⌝E ≡ ⌜ wkw idw ⌝w
        p = ⌜ idenv +E wkw idw ⌝E ≡⟨ ⌜id+Ewk⌝ ⟩
            wk          ≡⟨ ⌜wkid⌝ ⁻¹ ⟩
            ⌜ wkw idw ⌝w ∎
        q : tr (Val _) [⌜id+E⌝] (neu (var z))
            ≡[ ap (λ x → Val (Γ , A) (A [ x ]T)) p ]≡
            tr (Val _) [⌜wkid⌝] (neu (var z))
        q = ≅-to-≡[] {B = Val _} isSetTy (
              tr (Val _) [⌜id+E⌝] (neu (var z)) ≅⟨ trfill (Val _) [⌜id+E⌝] (neu (var z)) ⁻¹ ⟩
              neu (var z)                      ≅⟨ trfill (Val _) [⌜wkid⌝] (neu (var z)) ⟩
              tr (Val _) [⌜wkid⌝] (neu (var z)) ≅∎)
        r : tr (Val _) Π[] lamn+
            ≡[ ap (λ x → Val (Γ , A) (Π (A [ x ]T) (B [ x ↑ A ]T))) p ]≡
            tr (Val _) Π[] lamn+'
        r = ≅-to-≡[] {B = Val _} isSetTy (
              tr (Val _) Π[] lamn+
                ≅⟨ trfill (Val _) Π[] lamn+ ⁻¹ ⟩
              lam ⌜ n ⌝N (idenv +E wkw idw)
                ≅⟨ trfill (Val _) [+E] lamn+ ⟩
              lamn +V wkw idw
                ≅⟨ apd (_+V wkw {A = A} idw) (trfill (Val Γ) P lamn) ⟩
              lamn' +V wkw idw
                ≅⟨ trfill (Val _) Π[] lamn+' ⟩
              tr (Val _) Π[] lamn+' ≅∎)
        $lamn+' : tr (Val _) Π[] lamn+' $ tr (Val _) [⌜wkid⌝] (neu (var z)) ⇒ v
        $lamn+' = (λ i → (r i) $ (q i) ⇒ v)
                  * $lamn+
    in lamn' ,, evallamn' ,, qΠ $lamn+' qv
  stable-nf (neuU n) =
    let v ,, evaln ,, qv = stable-nenf n in
    neu v ,, evaln ,, qU qv
  stable-nf (neuEl n) =
    let v ,, evaln ,, qv = stable-nenf n in
    neu v ,, evaln ,, qEl qv
  stable-nf (isSetNf p q i j) = {!!}

  stable-nenf (var x) =
    var x ,, stable-var x ,, qsvar
  stable-nenf (app {Γ} {A} {B} n m) =
    let f ,, evaln ,, qf = stable-nenf n
        v ,, evalm ,, qv = stable-nf m
        fv : NV Γ (B [ < ⌜ v ⌝V > ]T)
        fv = app f v
        fv' : NV Γ (B [ < ⌜ m ⌝N > ]T)
        fv' = tr (λ x → NV Γ (B [ < x > ]T)) (q≡ qv) fv
        evalnm : eval ⌜ n ⌝NN $ ⌜ m ⌝N > idenv ⇒ neu (app f v)
        evalnm = eval$-idenv evaln evalm ($app f v)
        evalnm' : eval ⌜ n ⌝NN $ ⌜ m ⌝N > idenv
                  ⇒ neu (tr (λ x → NV Γ (B [ < x > ]T)) (q≡ qv) (app f v))
        evalnm' = trd (λ x → eval ⌜ n ⌝NN $ ⌜ m ⌝N > idenv ⇒ neu x)
                      (trfill (λ x → NV Γ (B [ < x > ]T)) (q≡ qv) (app f v))
                      evalnm
        qfv : qs fv ⇒ tr (NN Γ) (ap (λ x → B [ < x > ]T) (q≡ qv) ⁻¹) (app n m)
        qfv = qsapp qf qv
        qfv' : qs fv' ⇒ app n m
        qfv' = (λ i → qs (trfill (λ x → NV Γ (B [ < x > ]T)) (q≡ qv) fv i)
                       ⇒ trfill (NN Γ) (ap (λ x → B [ < x > ]T) (q≡ qv) ⁻¹) (app n m) (1- i))
               * qfv
    in fv' ,, evalnm' ,, qfv'
  stable-nenf (isSetNN p q i j) = {!!}
