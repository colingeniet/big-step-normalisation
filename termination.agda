{-# OPTIONS --cubical #-}

open import equality
open import types
open import terms
open import normal-forms
open import evaluator

open import Agda.Builtin.Sigma

-- Strongly computable values.
SCV : {Γ : Con} {A : Ty} {u : Tm Γ A} → Val u → Set
-- At the base type, a value is strongly computable if it can be normalized by q.
SCV {A = o} {u = u} valu =
  Σ (Nf u) (λ nfu → q valu ⇒ nfu)
-- For function types, a value is strongly computable if for any SC argument value
-- in an extended context, the application of that function to that argument
-- gives a SCV.
SCV {Γ = Γ} {A = A ⟶ B} {u = f} valf =
  {Δ : Con} {u : Tm (Γ ++ Δ) A} {valu : Val u} → SCV valu →
  Σ (Val ((f ++t Δ) $ u)) (λ valfu →
  Σ ((valf ++V Δ) $ valu ⇒ valfu) (λ _ →
    SCV valfu))


-- Lemma : SCV is stable by context extension.
{-
_+SCV_ : {Γ : Con} {B : Ty} {u : Tm Γ B} {valu : Val u} → SCV valu → (A : Ty) →
         SCV (valu +V A)
_+SCV_ {B = o} ((nneu neuu)  Σ., qu) A = (nneu (neuu +NN A)) Σ., {!!}
-}

-- Main lemma : SCV is ~ equivalent to the termination of q.
-- Main direction (actual goal).
scv-q : {Γ : Con} {A : Ty} {u : Tm Γ A} {valu : Val u} →
        SCV valu → Σ (Nf u) (λ nfu → q valu ⇒ nfu)
-- The reciprocal on neutral terms is required for the induction
q-scv : {Γ : Con} {A : Ty} {u : Tm Γ A} {neuu : Ne Val u} {nefu : Ne Nf u} →
        qs neuu ⇒ nefu → SCV (vneu neuu)

-- The second part of the lemma allows to prove that variables --- in particular
-- vz --- are strongly computable, which is what is required to prove the first part.
vzscv : {Γ : Con} {A : Ty} → SCV (vneu (var (z {Γ} {A})))
vzscv = q-scv qsvar

scv-q {A = o} scvu = scvu
scv-q {A = A ⟶ B} scvu = let res = scvu {Δ = ● Con., A} (vzscv) in
                          let valuz = fst res in
                          let cuz = fst (snd res) in
                          let scvuz = snd (snd res) in
                          let res2 = scv-q scvuz in
                          let nfappu = fst res2 in
                          let cappu = snd res2 in
                          tr Nf classicη (nlam nfappu) Σ., qs⟶ cuz cappu
q-scv {A = o} {neuu = neuu} {nefu = nefu} cu = (nneu nefu) Σ., qso cu
q-scv {A = A ⟶ B} {u = f} {neuu = neuf} {nefu = neff} cf {Δ = Δ} {u = u} {valu = valu} scvu =
  {!!}
