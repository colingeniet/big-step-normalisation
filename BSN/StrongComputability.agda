{-# OPTIONS --cubical #-}

{-
  Definition of the notion of strong computability, which is central in the
  proof of termination.
  This notion can be seen as a (a priori) stronger requirement than the
  termination of quote, which will allow the induction to go through.
-}

module BSN.StrongComputability where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import Value.Sets
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator
open import Evaluator.Weakening
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Sets
open import TypeEvaluator.Evaluator
open import BSN.Stability
open import BSN.Soundness


scvTV : {S : TSk} {Γ : Con} (A : TV S Γ) → Val Γ ⌜ A ⌝T → Set
scvTV {Γ = Γ} U v = Σ[ n ∈ Nf Γ U ] q v ⇒ n
scvTV {Γ = Γ} (El u) v = Σ[ n ∈ Nf Γ (El u) ] q v ⇒ n
scvTV {Π S T} {Γ} (Π A B) f =
  {Δ : Con} (σ : Wk Δ Γ) {v : Val Δ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T} → scvTV (A [ ⌜ σ ⌝w ]TV) v →
  Σ[ C ∈ TV T Δ ] Σ[ fv ∈ Val Δ ⌜ C ⌝T ]
  ((tr (Val Δ) Π[] (f +V σ)) $ (tr (Val Δ) (⌜[]TV⌝ ⁻¹) v) ⇒ fv  ×  scvTV C fv)

isPropscvTV : {S : TSk} {Γ : Con} {A : TV S Γ} {v : Val Γ ⌜ A ⌝T} → isProp (scvTV A v)
isPropscvTV {A = U} {v} (n ,, qn) (m ,, qm) i =
  let n≡m : n ≡ m
      n≡m = q-sound qn qm
  in n≡m i ,, isPropDependent isPropq n≡m qn qm i
isPropscvTV {A = El u} {v} (n ,, qn) (m ,, qm) i =
  let n≡m : n ≡ m
      n≡m = q-sound qn qm
  in n≡m i ,, isPropDependent isPropq n≡m qn qm i
isPropscvTV {Π S T} {Γ} {Π A B} {f} x y i {Δ} σ {v} scvv =
  let C ,, fv ,, $fv ,, scvfv = x σ scvv
      C' ,, fv' ,, $fv' ,, scvfv' = y σ scvv
      fv≅fv' = $-sound $fv $fv'
      C≡C' = ⌜⌝T-injective (fst fv≅fv')
      fv≡fv' = ≅-to-≡[] isSetTy fv≅fv' {P = ap ⌜_⌝T C≡C'}
  in C≡C' i ,, fv≡fv' i ,,
     isPropPath {B = λ i → _ $ _ ⇒ (fv≡fv' i)} isProp$ $fv $fv' i ,,
     isPropPath {B = λ i → scvTV (C≡C' i) (fv≡fv' i)} isPropscvTV scvfv scvfv' i


abstract
  _+scvTV_ : {S : TSk} {Γ Δ : Con} {A : TV S Δ} {v : Val Δ ⌜ A ⌝T} →
             scvTV A v → (σ : Wk Γ Δ) → scvTV (A [ ⌜ σ ⌝w ]TV) (tr (Val Γ) ⌜[]TV⌝ (v +V σ))
  _+scvTV_ {A = U} {v} (n ,, qn) σ =
   tr (Nf _) U[] (n +N σ) ,,
   (λ i → q trfill (Val _) U[] (v +V σ) i ⇒ trfill (Nf _) U[] (n +N σ) i) * (qn +q σ)
  _+scvTV_ {A = El u} {v} (n ,, qn) σ =
   tr (Nf _) El[] (n +N σ) ,,
   (λ i → q trfill (Val _) El[] (v +V σ) i ⇒ trfill (Nf _) El[] (n +N σ) i) * (qn +q σ)
  _+scvTV_ {Π S T} {Γ} {Δ} {Π A B} {f} scvf σ {Θ} δ {v} scvv =
    let A+ = A [ ⌜ σ ⌝w ]TV [ ⌜ δ ⌝w ]TV
        A+' = A [ ⌜ σ ∘w δ ⌝w ]TV
        P : A+ ≡ A+'
        P = A [ ⌜ σ ⌝w ]TV [ ⌜ δ ⌝w ]TV ≡⟨ [][]TV ⁻¹ ⟩
            A [ ⌜ σ ⌝w ∘ ⌜ δ ⌝w ]TV     ≡⟨ ap (A [_]TV) (⌜∘⌝w ⁻¹) ⟩
            A [ ⌜ σ ∘w δ ⌝w ]TV        ∎
        v' : Val Θ ⌜ A+' ⌝T
        v' = tr (λ x → Val Θ ⌜ x ⌝T) P v
        v≡v' = trfill (λ x → Val Θ ⌜ x ⌝T) P v
        scvv' : scvTV A+' v'
        scvv' = (λ i → scvTV (P i) (v≡v' i)) * scvv
        C ,, fv ,, $fv ,, scvfv = scvf (σ ∘w δ) scvv'
        p : tr (Val Θ) Π[] (f +V (σ ∘w δ))
            ≅[ Val Θ ] tr (Val Θ) Π[] (tr (Val Γ) ⌜[]TV⌝ (f +V σ) +V δ)
        p = tr (Val Θ) Π[] (f +V (σ ∘w δ))
              ≅⟨ trfill (Val Θ) Π[] (f +V (σ ∘w δ)) ⁻¹ ⟩
            f +V (σ ∘w δ)
              ≅⟨ +V∘ {v = f} ⟩
            (f +V σ) +V δ
              ≅⟨ apd (_+V δ) (trfill (Val Γ) ⌜[]TV⌝ (f +V σ)) ⟩
            (tr (Val Γ) ⌜[]TV⌝ (f +V σ)) +V δ
              ≅⟨ trfill (Val Θ) Π[] _ ⟩
            tr (Val Θ) Π[] (tr (Val Γ) ⌜[]TV⌝ (f +V σ) +V δ) ≅∎
        q : tr (Val Θ) (⌜[]TV⌝ ⁻¹) v' ≅[ Val  Θ ] tr (Val Θ) (⌜[]TV⌝ ⁻¹) v
        q = tr (Val Θ) (⌜[]TV⌝ ⁻¹) v' ≅⟨ trfill (Val Θ) (⌜[]TV⌝ ⁻¹) v' ⁻¹ ⟩
            v'                       ≅⟨ trfill (λ x → Val Θ ⌜ x ⌝T) P v ⁻¹ ⟩
            v                        ≅⟨ trfill (Val Θ) (⌜[]TV⌝ ⁻¹) v ⟩
            tr (Val Θ) (⌜[]TV⌝ ⁻¹) v  ≅∎
        Q : ⌜ A ⌝T [ ⌜ σ ∘w δ ⌝w ]T ≡ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T [ ⌜ δ ⌝w ]T
        Q = ⌜ A ⌝T [ ⌜ σ ∘w δ ⌝w ]T       ≡⟨ ap (⌜ A ⌝T [_]T) ⌜∘⌝w ⟩
            ⌜ A ⌝T [ ⌜ σ ⌝w ∘ ⌜ δ ⌝w ]T    ≡⟨ [][]T ⟩
            ⌜ A ⌝T [ ⌜ σ ⌝w ]T [ ⌜ δ ⌝w ]T ≡⟨ ap (_[ ⌜ δ ⌝w ]T) ⌜[]TV⌝ ⟩
            ⌜ A [ ⌜ σ ⌝w ]TV ⌝T [ ⌜ δ ⌝w ]T ∎
        R : ⌜ B ⌝T [ ⌜ σ ∘w δ ⌝w ↑ ⌜ A ⌝T ]T ≅[ Ty ]
            ⌜ tr (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) ⌝T [ ⌜ δ ⌝w ↑ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T ]T
        R = ⌜ B ⌝T [ ⌜ σ ∘w δ ⌝w ↑ ⌜ A ⌝T ]T
              ≅⟨ apd (λ x → ⌜ B ⌝T [ x ↑ ⌜ A ⌝T ]T) (⌜∘⌝w {σ = σ} {δ}) ⟩
            ⌜ B ⌝T [ (⌜ σ ⌝w ∘ ⌜ δ ⌝w) ↑ ⌜ A ⌝T ]T
              ≅⟨ ap≅ (⌜ B ⌝T [_]T) ↑∘↑ ≅⁻¹ ⟩'
            ⌜ B ⌝T [ (⌜ σ ⌝w ↑ ⌜ A ⌝T) ∘ (⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T) ]T
              ≅⟨ [][]T ⟩
            ⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T
              ≅⟨ apd (λ x → x [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T) (⌜[]TV⌝ {A = B} {⌜ σ ⌝w ↑ ⌜ A ⌝T})  ⟩
            ⌜ B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV ⌝T [ ⌜ δ ⌝w ↑ ⌜ A ⌝T [ ⌜ σ ⌝w ]T ]T
              ≅⟨ (λ i → ⌜ trfill (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) i ⌝T
                        [ ⌜ δ ⌝w ↑ (⌜[]TV⌝ {A = A} i) ]T) ⟩
            ⌜ tr (λ x → TV T (Γ , x)) ⌜[]TV⌝ (B [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]TV) ⌝T [ ⌜ δ ⌝w ↑ ⌜ A [ ⌜ σ ⌝w ]TV ⌝T ]T ≅∎
        $fv' = (λ i → (≅-to-≡[] isSetTy p {P = λ i → Π (Q i) (≅-to-≡[] isSetCon R {P = ap (Θ ,_) Q} i)} i)
                      $ (≅-to-≡[] isSetTy q {P = Q} i)
                      ⇒ fv)
               * $fv
    in C ,, fv ,, $fv' ,, scvfv




{-
-- Extension of strong computability to environments.
sce : {Γ Δ : Con} → Env Γ Δ → Set
sce ε = ⊤
sce (ρ , u) = sce ρ  ×  scv u

-- Associated projections.
π₁sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → sce (π₁E ρ)
π₁sce {ρ = _ , _} = fst

π₂sce : {Γ Δ : Con} {A : Ty} {ρ : Env Γ (Δ , A)} →
        sce ρ → scv (π₂E ρ)
π₂sce {ρ = _ , _} = snd

πηsce : {Γ Δ : Con} {A : Ty} {σ : Env Γ (Δ , A)} (sceσ : sce σ) →
        (π₁sce sceσ ,, π₂sce sceσ) ≡[ ap sce πηE ]≡ sceσ
πηsce {σ = σ , u} (sceσ ,, scvu) = refl

sceεη : {Γ : Con} {σ : Env Γ ●} (sceσ : sce σ) →
        sceσ ≡[ ap sce (envεη σ) ]≡ tt
sceεη {σ = ε} tt = refl



isPropsce : {Γ Δ : Con} {σ : Env Γ Δ} → isProp (sce σ)
isPropsce {Δ = ●} {ε} = isProp⊤
isPropsce {Δ = Δ , A} {ρ , u} = isProp× isPropsce isPropscv

-- Weakenings.
_+sce_ : {Γ Δ Θ : Con} {ρ : Env Δ Θ} → sce ρ → (σ : Wk Γ Δ) → sce (ρ +E σ)
_+sce_ {ρ = ε} tt A = tt
_+sce_ {ρ = ρ , u} (sceρ ,, scvu) σ = sceρ +sce σ ,, scvu +scv σ


π₁sce+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₁sce (sceρ +sce σ) ≡[ ap sce (π₁+ {ρ = ρ}) ]≡ (π₁sce sceρ) +sce σ
π₁sce+ {ρ = _ , _} = refl
π₂sce+ : {Γ Δ Θ : Con} {A : Ty} {ρ : Env Δ (Θ , A)} {sceρ : sce ρ} {σ : Wk Γ Δ} →
         π₂sce (sceρ +sce σ) ≡[ ap scv (π₂+ {ρ = ρ}) ]≡ (π₂sce sceρ) +scv σ
π₂sce+ {ρ = _ , _} = refl


-- The identity environment is strongly computable.
sceid : {Γ : Con} → sce (idenv {Γ})
sceid {●} = tt
sceid {Γ , A} = sceid +sce (wkwk A idw) ,, scvvar
-}
