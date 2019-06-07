{-# OPTIONS --safe --cubical #-}

module Evaluator.Weakening where


open import Library.Equality
open import Library.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Variable.Variable
open import Variable.Lemmas
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator


abstract
  -- Evaluation is stable by weakening.
  _+eval_ : {Γ Δ Θ : Con} {A : Ty Θ} {B : Ty Δ}
            {u : Tm Θ A} {ρ : Env Δ Θ} {uρ : Val Δ B} →
            eval u > ρ ⇒ uρ → (σ : Wk Γ Δ) → eval u > (ρ +E σ) ⇒ (uρ +V σ)
  _+evals_ : {Γ Δ Θ Ψ : Con} {σ : Tms Θ Ψ} {ρ : Env Δ Θ} {σρ : Env Δ Ψ} →
             evals σ > ρ ⇒ σρ → (ν : Wk Γ Δ) → evals σ > (ρ +E ν) ⇒ (σρ +E ν)
  _+$_ : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {C : Ty Δ}
         {f : Val Δ (Π A B)} {v : Val Δ A} {fv : Val Δ C} →
         f $ v ⇒ fv → (σ : Wk Γ Δ) → (tr (Val Γ) Π[] (f +V σ)) $ (v +V σ) ⇒ (fv +V σ)

  evalsid +evals δ = evalsid
  (evals∘ cν cσ) +evals δ = evals∘ (cν +evals δ) (cσ +evals δ)
  evalsε +evals δ = evalsε
  (evals, {σ = σ} {u} {ρ} {σρ} {uρ} cσ cu) +evals δ =
    let cσ+ = cσ +evals δ
        cu+ = cu +eval δ
        p = evals,-aux cσ+ cu+
        cσu+ : evals (σ , u) > (ρ +E δ) ⇒ ((σρ +E δ) , tr (Val _) p (uρ +V δ))
        cσu+ = evals, cσ+ cu+
        q : tr (Val _) p (uρ +V δ) ≅[ Val _ ] tr (Val _) ([+E] ⁻¹) (tr (Val _) (evals,-aux cσ cu) uρ +V δ)
        q = tr (Val _) p (uρ +V δ)
              ≅⟨ trfill (Val _) p (uρ +V δ) ⁻¹ ⟩
            uρ +V δ
              ≅⟨ apd (_+V δ) (trfill (Val _) (evals,-aux cσ cu) uρ) ⟩
            tr (Val _) (evals,-aux cσ cu) uρ +V δ
              ≅⟨ trfill (Val _) ([+E] ⁻¹) _ ⟩
            tr (Val _) ([+E] ⁻¹) (tr (Val _) (evals,-aux cσ cu) uρ +V δ) ≅∎
        r : (σρ +E δ) , tr (Val _) p (uρ +V δ)
            ≡ (σρ , tr (Val _) (evals,-aux cσ cu) uρ) +E δ
        r = ap (σρ +E δ ,_) (≅-to-≡ isSetTy q)
    in tr (evals (σ , u) > (ρ +E δ) ⇒_) r cσu+
  (evalsπ₁ {σ = σ} {ρ} {σρ} cσ) +evals δ = tr (evals (π₁ σ) > (ρ +E δ)  ⇒_)
                                       (π₁+ {ρ = σρ} {σ = δ})
                                       (evalsπ₁ (cσ +evals δ))
  (isPropevals x y i) +evals δ = isPropevals (x +evals δ) (y +evals δ) i

  (eval[] {u = u} {σ} {ρ} {σρ} {uσρ} cσ cu) +eval δ = eval[] (cσ +evals δ) (cu +eval δ)
  (evalπ₂ {σ = σ} {ρ} {σρ} cσ) +eval δ = trd (eval (π₂ σ) > (ρ +E δ) ⇒_)
                                             (snd (π₂+ {ρ = σρ} {σ = δ}))
                                             (evalπ₂ (cσ +evals δ))
  (evallam u ρ) +eval δ = trd (eval (lam u) > (ρ +E δ) ⇒_)
                              (trfill (Val _) [+E] (lam u (ρ +E δ)))
                              (evallam u (ρ +E δ))
  (evalapp {A = A} {B} {f} {ρ} {v} {C} {D} {fρ} {fρv} cf $fρ) +eval δ =
    let ρ+ = ρ +E δ
        P : A [ ⌜ ρ ⌝E ]T [ ⌜ δ ⌝w ]T ≡ A [ ⌜ ρ+ ⌝E ]T
        P = [+E] ⁻¹
        v+ = v +V δ
        v+' = tr (Val _) P v+
        v+≡v+' : v+ ≡[ ap (Val _) P ]≡ v+'
        v+≡v+' = trfill (Val _) P v+
        C+ = C [ ⌜ δ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T
        C+' = tr Ty (ap (_ ,_) P) C+
        C+≡C+' : C+ ≡[ ap Ty (ap (_ ,_) P) ]≡ C+'
        C+≡C+' = trfill Ty (ap (_ ,_) P) C+
        Q i = Π (P i) (C+≡C+' i)
        fρ+ = fρ +V δ
        fρ+' = tr (Val _) Π[] fρ+
        fρ+'' = tr (Val _) Q fρ+'
        fρ+≡fρ+'' = fρ+ ≡[ ap (Val _) (Π[] ∙ Q) ]≡ fρ+''
        fρ+≡fρ+'' = ≅-to-≡[] {B = Val _} isSetTy (
          fρ+   ≅⟨ trfill (Val _) Π[] fρ+ ⟩
          fρ+'  ≅⟨ trfill (Val _) Q fρ+' ⟩
          fρ+'' ≅∎)
        fρv+ = fρv +V δ
        cf+ : eval f > ρ+ ⇒ fρ+
        cf+ = cf +eval δ
        cf+' : eval f > ρ+ ⇒ fρ+''
        cf+' = trd {A = λ i → Val _ ((Π[] ∙ Q) i)} (eval f > ρ+ ⇒_) fρ+≡fρ+'' cf+
        $fρ+ : fρ+' $ v+ ⇒ fρv+
        $fρ+ = $fρ +$ δ
        $fρ+' : fρ+'' $ v+' ⇒ fρv+
        $fρ+' = (λ i → (trfill (Val _) Q fρ+' i) $ (v+≡v+' i) ⇒ fρv+)
                * $fρ+
    in evalapp cf+' $fρ+'
  (isPropeval x y i) +eval δ = isPropeval (x +eval δ) (y +eval δ) i

  ($lam {A = A} {B} {C} {u} {ρ} {v} {uρv} cu) +$ σ =
    let v+ = v +V σ
        v+' = tr (Val _) ([+E] ⁻¹) v+
        v+≡v+' = trfill (Val _) ([+E] ⁻¹) v+
        lamu+ = tr (Val _) Π[] (lam u (ρ +E σ))
        lamu+' = tr (Val _) Π[] (tr (Val _) Π[] (lam u ρ) +V σ)
        lamu+≡lamu+' : lamu+ ≅[ Val _ ] lamu+'
        lamu+≡lamu+' = tr (Val _) Π[] (lam u (ρ +E σ))
                           ≅⟨ trfill (Val _) Π[] _ ⁻¹ ⟩
                         lam u (ρ +E σ)
                           ≅⟨ trfill (Val _) [+E] (lam u (ρ +E σ)) ⟩
                         (lam u ρ) +V σ
                           ≅⟨ apd (_+V σ) (trfill (Val _) Π[] (lam u ρ)) ⟩
                         (tr (Val _) Π[] (lam u ρ)) +V σ
                           ≅⟨ trfill (Val _) Π[] _ ⟩
                         tr (Val _) Π[] (tr (Val _) Π[] (lam u ρ) +V σ) ≅∎
        P : A [ ⌜ ρ +E σ ⌝E ]T ≡ A [ ⌜ ρ ⌝E ]T [ ⌜ σ ⌝w ]T
        P = [+E]
        Q : B [ ⌜ ρ +E σ ⌝E ↑ A ]T
            ≡[ ap (λ x → Ty (_ , x)) P ]≡
            B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T
        Q = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ ρ +E σ ⌝E ↑ A ]T
              ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜⌝+E ⟩
            B [ (⌜ ρ ⌝E ∘ ⌜ σ ⌝w) ↑ A ]T
              ≅⟨ ap≅ (B [_]T) (↑∘↑ ≅⁻¹) ⟩'
            B [ (⌜ ρ ⌝E ↑ A) ∘ (⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T)) ]T
              ≅⟨ [][]T ⟩
            B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T ≅∎)
        $lamu+ : lamu+ $ v+' ⇒ (uρv +V σ)
        $lamu+ = $lam (cu +eval σ)
    in (λ i → ≅-to-≡[] isSetTy lamu+≡lamu+' {P = λ i → Π (P i) (Q i)} i
              $ (v+≡v+' (1- i)) ⇒ (uρv +V σ))
       * $lamu+
  ($app n v) +$ σ =
    let v+ = v +V σ
        n+ = tr (NV _) Π[] (n +NV σ)
        n+' = tr (Val _) Π[] (neu (n +NV σ))
        n+≡n+' : neu n+ ≡ n+'
        n+≡n+' = ≅-to-≡ {B = Val _} isSetTy (
                 neu (tr (NV _) Π[] (n +NV σ))  ≅⟨ apd neu (trfill (NV _) Π[] (n +NV σ)) ⁻¹ ⟩
                 neu (n +NV σ)                  ≅⟨ trfill (Val _) Π[] (neu (n +NV σ)) ⟩
                 tr (Val _) Π[] (neu (n +NV σ)) ≅∎)
        n$v+ : (neu n+) $ v+ ⇒ neu (app n+ v+)
        n$v+ = $app n+ v+
        p = trfill (NV _) ([<>][] {v = v}) (app n+ v+) 
    in (λ i → (n+≡n+' i) $ v+ ⇒ neu (p i)) * n$v+
  (isProp$ x y i) +$ σ = isProp$ (x +$ σ) (y +$ σ) i



  _+q_ : {Γ Δ : Con} {A : Ty Δ} {v : Val Δ A} {n : Nf Δ A} →
         q v ⇒ n → (σ : Wk Γ Δ) → q (v +V σ) ⇒ (n +N σ)
  _+qs_ : {Γ Δ : Con} {A : Ty Δ} {v : NV Δ A} {n : NN Δ A} →
          qs v ⇒ n → (σ : Wk Γ Δ) → qs (v +NV σ) ⇒ (n +NN σ)

  (qU {n = v} {n} qv) +q δ =
    let qsv+ : qs (v +NV δ) ⇒ (n +NN δ)
        qsv+ = qv +qs δ
        qsv+' : qs (tr (NV _) U[] (v +NV δ)) ⇒ (tr (NN _) U[] (n +NN δ))
        qsv+' = (λ i → qs (trfill (NV _) U[] (v +NV δ) i) ⇒ (trfill (NN _) U[] (n +NN δ) i))
                * qsv+
        qv+ : q neu (tr (NV _) U[] (v +NV δ)) ⇒ neuU (tr (NN _) U[] (n +NN δ))
        qv+ = qU qsv+'
        qv+' : q neu (v +NV δ) ⇒ (neuU n +N δ)
        qv+' = (λ i → q neu (trfill (NV _) U[] (v +NV δ) (1- i))
                      ⇒ (trfill (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN δ))) i))
               * qv+
    in qv+'
  (qEl {n = v} {n} qv) +q δ =
    let qsv+ : qs (v +NV δ) ⇒ (n +NN δ)
        qsv+ = qv +qs δ
        qsv+' : qs (tr (NV _) El[] (v +NV δ)) ⇒ (tr (NN _) El[] (n +NN δ))
        qsv+' = (λ i → qs (trfill (NV _) El[] (v +NV δ) i) ⇒ (trfill (NN _) El[] (n +NN δ) i))
                * qsv+
        qv+ : q neu (tr (NV _) El[] (v +NV δ)) ⇒ neuEl (tr (NN _) El[] (n +NN δ))
        qv+ = qEl qsv+'
        qv+' : q neu (v +NV δ) ⇒ (neuEl n +N δ)
        qv+' = (λ i → q neu (trfill (NV _) El[] (v +NV δ) (1- i))
                      ⇒ (trfill (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN δ))) i))
               * qv+
    in qv+'
  (qΠ {A = A} {B} {f} {fz} {nfz} $f qf) +q δ =
    let f+ = f +V δ
        f+' = tr (Val _) Π[] f+
        f+'w = tr (Val _) Π[] (f+' +V wkw idw)
        fw = tr (Val _) Π[] (f +V wkw idw)
        fw+ = tr (Val _) Π[] (fw +V (δ ↑w A))
        p : f+'w ≅[ Val _ ] fw+
        p = tr (Val _) Π[] (f+' +V wkw idw) ≅⟨ trfill (Val _) Π[] (f+' +V wkw idw) ⁻¹ ⟩
            (tr (Val _) Π[] f+) +V wkw idw  ≅⟨ (λ i → (trfill (Val _) Π[] f+ (1- i)) +V wkw idw) ⟩
            (f +V δ) +V wkw idw             ≅⟨ +V∘ {v = f} ⁻¹ ⟩
            f +V (δ ∘w wkw idw)             ≅⟨ apd (f +V_) wkid∘↑ ⁻¹ ⟩
            f +V (wkw idw ∘w (δ ↑w A))      ≅⟨ +V∘ {v = f} ⟩
            (f +V wkw idw) +V (δ ↑w A)      ≅⟨ apd (_+V (δ ↑w A)) (trfill (Val _) Π[] (f +V wkw idw)) ⟩
            (tr (Val _) Π[] (f +V wkw idw)) +V (δ ↑w A)
              ≅⟨ trfill (Val _) Π[] (fw +V (δ ↑w A)) ⟩
            tr (Val _) Π[] (fw +V (δ ↑w A)) ≅∎
        z+ = tr (Val _) [⌜wkid⌝] (neu (var z)) +V (δ ↑w A)
        z+' = tr (Val _) [⌜wkid⌝] (neu (var z))
        q : z+ ≅[ Val _ ] z+'
        q = tr (Val _) [⌜wkid⌝] (neu (var z)) +V (δ ↑w A)
              ≅⟨ (λ i → (trfill (Val _) [⌜wkid⌝] (neu (var z)) (1- i)) +V (δ ↑w A)) ⟩
            -- (neu (var z)) +V (δ ↑w A)
            neu (var (tr (Var _) []wk, (tr (Var _) [⌜wkw⌝] z)))
              ≅⟨ apd (λ x → neu (var x)) (trfill (Var _) []wk, _) ⁻¹ ⟩
            neu (var (tr (Var _) [⌜wkw⌝] z))
              ≅⟨ apd (λ x → neu (var x)) (trfill (Var _) [⌜wkw⌝] _) ⁻¹ ⟩
            neu (var z)
              ≅⟨ trfill (Val _) [⌜wkid⌝] (neu (var z)) ⟩
            tr (Val _) [⌜wkid⌝] (neu (var z)) ≅∎
        P : B [ ⌜ δ ↑w A ⌝w ]T ≡ B [ ⌜ δ ⌝w ↑ A ]T
        P = ap (B [_]T) ⌜↑w⌝
        Q : A [ ⌜ wkw idw ⌝w ]T [ ⌜ δ ↑w A ⌝w ]T ≡ A [ ⌜ δ ⌝w ]T [ ⌜ wkw idw ⌝w ]T
        Q = A [ ⌜ wkw idw ⌝w ]T [ ⌜ δ ↑w A ⌝w ]T ≡⟨ [][]T ⁻¹ ⟩
            A [ ⌜ wkw idw ⌝w ∘ ⌜ δ ↑w A ⌝w ]T    ≡⟨ ap (A [_]T) ⌜∘⌝w ⁻¹ ⟩
            A [ ⌜ (wkw idw) ∘w (δ ↑w A) ⌝w ]T   ≡⟨ ap (λ x → A [ ⌜ x ⌝w ]T) wkid∘↑ ⟩
            A [ ⌜ δ ∘w (wkw idw) ⌝w ]T          ≡⟨ ap (A [_]T) ⌜∘⌝w ⟩
            A [ ⌜ δ ⌝w ∘ ⌜ wkw idw ⌝w ]T         ≡⟨ [][]T ⟩
            A [ ⌜ δ ⌝w ]T [ ⌜ wkw idw ⌝w ]T      ∎
        R : B [ ⌜ wkw idw ⌝w ↑ A ]T [ ⌜ δ ↑w A ⌝w ↑ (A [ ⌜ wkw idw ⌝w ]T) ]T
            ≡[ ap (λ x → Ty (_ , x)) Q ]≡
            B [ ⌜ δ ⌝w ↑ A ]T [ ⌜ wkw idw ⌝w ↑ (A [ ⌜ δ ⌝w ]T) ]T
        R = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ wkw idw ⌝w ↑ A ]T [ ⌜ δ ↑w A ⌝w ↑ (A [ ⌜ wkw idw ⌝w ]T) ]T
              ≅⟨ [][]T ⁻¹ ⟩
            B [ (⌜ wkw idw ⌝w ↑ A) ∘ (⌜ δ ↑w A ⌝w ↑ (A [ ⌜ wkw idw ⌝w ]T)) ]T
              ≅⟨ ap≅ (B [_]T) ↑∘↑ ⟩'
            B [ (⌜ wkw idw ⌝w ∘ ⌜ δ ↑w A ⌝w) ↑ A ]T
              ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜∘⌝w ⁻¹ ⟩
            B [ ⌜ (wkw idw) ∘w (δ ↑w A) ⌝w ↑ A ]T
              ≅⟨ apd (λ x → B [ ⌜ x ⌝w ↑ A ]T) wkid∘↑ ⟩
            B [ ⌜ δ ∘w wkw idw ⌝w ↑ A ]T
              ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜∘⌝w ⟩
            B [ (⌜ δ ⌝w ∘ ⌜ wkw idw ⌝w) ↑ A ]T
              ≅⟨ ap≅ (B [_]T) ↑∘↑ ≅⁻¹ ⟩'
            B [ (⌜ δ ⌝w ↑ A) ∘ (⌜ wkw idw ⌝w ↑ (A [ ⌜ δ ⌝w ]T)) ]T
              ≅⟨ [][]T ⟩
            B [ ⌜ δ ⌝w ↑ A ]T [ ⌜ wkw idw ⌝w ↑ (A [ ⌜ δ ⌝w ]T) ]T ≅∎)
        fz+ = fz +V (δ ↑w A)
        fz+' = tr (Val _) P fz+
        r : fz+ ≡[ ap (Val _) P ]≡ fz+'
        r = trfill (Val _) P fz+
        $f+ : fw+ $ z+ ⇒ fz+
        $f+ = $f +$ (δ ↑w A)
        $f+' : f+'w $ z+' ⇒ fz+'
        $f+' = (λ i → ≅-to-≡[] isSetTy (p ≅⁻¹) {P = λ i → Π (Q i) (R i)} i
                      $ ≅-to-≡[] isSetTy q {P = Q} i
                      ⇒ r i)
               * $f+
        nfz+ = nfz +N (δ ↑w A)
        nfz+' = tr (Nf _) P nfz+
        s : nfz+ ≡[ ap (Nf _) P ]≡ nfz+'
        s = trfill (Nf _) P nfz+
        qfz+ : q fz+ ⇒ nfz+
        qfz+ = qf +q (δ ↑w A)
        qfz+' : q fz+' ⇒ nfz+'
        qfz+' = (λ i → q (r i) ⇒ (s i)) * qfz+
        qf+ : q f+' ⇒ lam nfz+'
        qf+ = qΠ $f+' qfz+'
        nf+ = (lam nfz) +N δ
        t : lam nfz+' ≅[ Nf _ ] nf+
        t = lam (tr (Nf _) P nfz+) ≅⟨ (λ i → lam (trfill (Nf _) P nfz+ (1- i))) ⟩
            lam (nfz +N (δ ↑w A))  ≅⟨ (λ i → lam (trfill (Nf _) [⌜↑⌝] (nfz +N (δ ↑w A)) i)) ⟩
            lam (tr (Nf _) [⌜↑⌝] (nfz +N (δ ↑w A)))
              ≅⟨ trfill (Nf _) (Π[] ⁻¹) _ ⟩
            tr (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (nfz +N (δ ↑w A)))) ≅∎
        qf+' : q f+ ⇒ nf+
        qf+' = (λ i → q trfill (Val _) Π[] f+ (1- i) ⇒ (≅-to-≡[] isSetTy t {P = Π[] ⁻¹} i))
               * qf+
    in qf+'
  (isPropq x y i) +q δ = isPropq (x +q δ) (y +q δ) i

  qsvar +qs δ = qsvar
  (qsapp {A = A} {B} {f} {v} {nf} {nv} qsf qv) +qs δ =
    let v+ = v +V δ
        nv+ = nv +N δ
        f+ = f +NV δ
        f+' = tr (NV _) Π[] f+
        nf+ = nf +NN δ
        nf+' = tr (NN _) Π[] nf+
        qv+ : q v+ ⇒ nv+
        qv+ = qv +q δ
        qsf+ : qs f+ ⇒ nf+
        qsf+ = qsf +qs δ
        qsf+' : qs f+' ⇒ nf+'
        qsf+' = (λ i → qs (trfill (NV _) Π[] f+ i) ⇒ (trfill (NN _) Π[] nf+ i))
                * qsf+
        fv+ = app f+' v+
        fv+' = tr (NV _) ([<>][] {v = v}) fv+
        nfv+ = tr (NN _)
                  (ap (λ x → B [ ⌜ δ ⌝w ↑ A ]T [ < x > ]T) (q≡ qv+) ⁻¹)
                  (app nf+' nv+)
        nfv+' = (tr (NN _)
                    (ap (λ x → B [ < x > ]T) (q≡ qv) ⁻¹)
                    (app nf nv))
                +NN δ
        p : nfv+ ≅[ NN _ ] nfv+'
        p = nfv+
              ≅⟨ trfill (NN _) (ap (λ x → B [ ⌜ δ ⌝w ↑ A ]T [ < x > ]T) (q≡ qv+) ⁻¹) (app nf+' nv+) ⁻¹ ⟩
            app nf+' nv+
              ≅⟨ trfill (NN _) _ (app nf+' nv+) ⟩
            tr (NN _) _ (app nf+' nv+)
              ≅⟨ apd (_+NN δ) (trfill (NN _) (ap (λ x → B [ < x > ]T) (q≡ qv) ⁻¹) (app nf nv))  ⟩
            nfv+' ≅∎
        qfv+ : qs fv+ ⇒ nfv+
        qfv+ = qsapp qsf+' qv+
        qfv+' : qs fv+' ⇒ nfv+'
        qfv+' = (λ i → qs (trfill (NV _) ([<>][] {v = v}) fv+ i)
                       ⇒ (≅-to-≡[] isSetTy p {P = [<>][] {v = v}} i))
                * qfv+
    in qfv+'
  (isPropqs x y i) +qs δ = isPropqs (x +qs δ) (y +qs δ) i
