{-# OPTIONS --cubical #-}

module StrongComputability.Quote where

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
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import Evaluator.Evaluator
open import Evaluator.Weakening
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Sets
open import TypeEvaluator.Evaluator
open import StrongComputability.StrongComputability
open import StrongComputability.Weakening


abstract
  scvTV-quote : {S : TSk} {Γ : Con} {A : TV S Γ} {v : Val Γ ⌜ A ⌝T} →
                scvTV A v → Σ[ n ∈ Nf Γ ⌜ A ⌝T ] (q v ⇒ n)
  scvTV-unquote : {S : TSk} {Γ : Con} {A : TV S Γ} {v : NV Γ ⌜ A ⌝T} →
                  (n : NN Γ ⌜ A ⌝T) → qs v ⇒ n → scvTV A (neu v)

  scvTV-var : {S : TSk} {Γ : Con} {A : TV S Γ} {x : Var Γ ⌜ A ⌝T} → scvTV A (neu (var x))
  scvTV-var {A = A} {x} = scvTV-unquote (var x) qsvar

  scvTV-quote {A = U} scvv = scvv
  scvTV-quote {A = El u} scvv = scvv
  scvTV-quote {S} {Γ} {Π A B} {f} scvf =
    let P : ⌜ A ⌝T [ wk ]T ≡ ⌜ A [ ⌜ wkw idw ⌝w ]TV ⌝T
        P = ⌜ A ⌝T [ wk ]T           ≡⟨ [⌜wkid⌝] ⟩
            ⌜ A ⌝T [ ⌜ wkw idw ⌝w ]T  ≡⟨ ⌜[]TV⌝ ⟩
            ⌜ A [ ⌜ wkw idw ⌝w ]TV ⌝T ∎
        varz : Var (Γ , ⌜ A ⌝T) (⌜ A [ ⌜ wkw idw ⌝w ]TV ⌝T)
        varz = tr (Var _) P (z {A = ⌜ A ⌝T})
        C ,, fz ,, $fz ,, scvfz = scvf (wkw idw) {neu (var varz)} (scvTV-var {x = varz})
        nfz ,, qfz = scvTV-quote scvfz
        p : ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V ≅[ Tm _ ] vz
        p = ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V
              ≅⟨ (λ i → ⌜ trfill (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) (1- i) ⌝V) ⟩
            ⌜ neu (var varz) ⌝V ≅⟨ (λ i → ⌜ neu (var (trfill (Var _) P z (1- i))) ⌝V) ⟩
            ⌜ neu (var z) ⌝V    ≅∎
        C≡B : C ≡ B
        C≡B = ⌜⌝T-injective (
                ⌜ C ⌝T ≡⟨ fst (eval$≡ $fz) ⁻¹ ⟩
                ⌜ B ⌝T [ ⌜ wkw idw ⌝w ↑ ⌜ A ⌝T ]T [ < ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V > ]T
                  ≡⟨ [][]T ⁻¹ ⟩
                ⌜ B ⌝T [ (⌜ wkw idw ⌝w ↑ ⌜ A ⌝T) ∘ < ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V > ]T
                  ≡⟨ (λ i → ⌜ B ⌝T [ ↑∘<> {u = ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V} i ]T) ⟩
                ⌜ B ⌝T [ ⌜ wkw idw ⌝w , ⌜ tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⌝V ]T
                  ≡⟨ (λ i → ⌜ B ⌝T [ ⌜wkid⌝ i , ≅-to-≡[] isSetTy p {P = ap (⌜ A ⌝T [_]T) ⌜wkid⌝} i ]T) ⟩
                ⌜ B ⌝T [ wk , vz ]T              ≡⟨ ap (⌜ B ⌝T [_]T) πη ⟩
                ⌜ B ⌝T [ id ]T                   ≡⟨ [id]T ⟩
                ⌜ B ⌝T ∎)
        fz' : Val (Γ , ⌜ A ⌝T) ⌜ B ⌝T
        fz' = tr (Val _) (ap ⌜_⌝T C≡B) fz
        nfz' : Nf (Γ , ⌜ A ⌝T) ⌜ B ⌝T
        nfz' = tr (Nf _) (ap ⌜_⌝T C≡B) nfz
        q : tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ≡ tr (Val _) [⌜wkid⌝] (neu (var z))
        q = ≅-to-≡ {B = Val _} isSetTy (
              tr (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ≅⟨ trfill (Val _) (⌜[]TV⌝ ⁻¹) (neu (var varz)) ⁻¹ ⟩
              neu (var varz)                         ≅⟨ apd (λ x → neu (var x)) (trfill (Var _) P z) ⁻¹ ⟩
              neu (var z)                            ≅⟨ trfill (Val _) [⌜wkid⌝] (neu (var z)) ⟩
              tr (Val _) [⌜wkid⌝] (neu (var z))      ≅∎)
        $fz' : tr (Val _) Π[] (f +V wkw idw) $ tr (Val _) [⌜wkid⌝] (neu (var z)) ⇒ fz'
        $fz' = (λ i → (tr (Val _) Π[] (f +V wkw idw))
                      $ (q i)
                      ⇒ (trfill (Val _) (ap ⌜_⌝T C≡B) fz i))
               * $fz
        qfz' : q fz' ⇒ nfz'
        qfz' = (λ i → q (trfill (Val _) (ap ⌜_⌝T C≡B) fz i)
                      ⇒ (trfill (Nf _) (ap ⌜_⌝T C≡B) nfz i))
               * qfz
    in lam nfz' ,, qΠ $fz' qfz'

  scvTV-unquote {A = U} n qv = neuU n ,, qU qv
  scvTV-unquote {A = El u} n qv = neuEl n ,, qEl qv
  scvTV-unquote {S} {Γ} {Π A B} {f} n qf {Δ} σ {v} scvv =
    let m ,, qv = scvTV-quote scvv
        f+ : NV Δ (Π ⌜ A ⌝T ⌜ B ⌝T [ ⌜ σ ⌝w ]T)
        f+ = f +NV σ
        f+' : NV Δ (Π (⌜ A ⌝T [ ⌜ σ ⌝w ]T) (⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T))
        f+' = tr (NV Δ) Π[] f+
        neuf+'' = Val Δ (Π (⌜ A ⌝T [ ⌜ σ ⌝w ]T) (⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T))
        neuf+'' = tr (Val Δ) Π[] (neu f+)
        p : neu f+' ≡ neuf+''
        p = ≅-to-≡ {B = Val Δ} isSetTy (
              neu (tr (NV Δ) Π[] f+)  ≅⟨ apd neu (trfill (NV Δ) Π[] f+) ⁻¹ ⟩
              neu f+                  ≅⟨ trfill (Val Δ) Π[] (neu f+) ⟩
              tr (Val Δ) Π[] (neu f+) ≅∎)
        v' : Val Δ (⌜ A ⌝T [ ⌜ σ ⌝w ]T)
        v' = tr (Val Δ) (⌜[]TV⌝ ⁻¹) v
        C : Ty Δ
        C = ⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T [ < ⌜ v' ⌝V > ]T
        C' : Ty Δ
        C' = ⌜ B [ ⌜ σ ⌝w , ⌜ v' ⌝V ]TV ⌝T
        C≡C' : C ≡ C'
        C≡C' = ⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T [ < ⌜ v' ⌝V > ]T ≡⟨ [][]T ⁻¹ ⟩
               ⌜ B ⌝T [ (⌜ σ ⌝w ↑ ⌜ A ⌝T) ∘ < ⌜ v' ⌝V > ]T  ≡⟨ ap (⌜ B ⌝T [_]T) ↑∘<> ⟩
               ⌜ B ⌝T [ ⌜ σ ⌝w , ⌜ v' ⌝V ]T                ≡⟨ ⌜[]TV⌝ ⟩
               ⌜ B [ ⌜ σ ⌝w , ⌜ v' ⌝V ]TV ⌝T               ∎
        fv = app f+' v'
        $fv = $app f+' v'
        fv' = tr (NV Δ) C≡C' fv
        $fv' : neuf+'' $ v' ⇒ neu fv'
        $fv' = (λ i → (p i) $ v' ⇒ neu (trfill (NV Δ) C≡C' fv i))
               * $fv
        n+ = n +NN σ
        n+' = tr (NN Δ) Π[] n+
        m' = tr (Nf Δ) (⌜[]TV⌝ ⁻¹) m
        qf' : qs f+' ⇒ n+'
        qf' = (λ i → qs (trfill (NV Δ) Π[] f+ i) ⇒ (trfill (NN Δ) Π[] n+ i)) * (qf +qs σ)
        qv' : q v' ⇒ m'
        qv' = (λ i → q (trfill (Val Δ) (⌜[]TV⌝ ⁻¹) v i) ⇒ (trfill (Nf Δ) (⌜[]TV⌝ ⁻¹) m i)) * qv
        nm = app n+' m'
        nm' = tr (NN Δ) (ap (λ x → ⌜ B ⌝T [ ⌜ σ ⌝w ↑ ⌜ A ⌝T ]T [ < x > ]T) (q≡ qv') ⁻¹) nm
        qfv : qs fv ⇒ nm'
        qfv = qsapp qf' qv'
        nm'' = tr (NN Δ) C≡C' nm'
        qfv' : qs fv' ⇒ nm''
        qfv' = (λ i → qs (trfill (NV Δ) C≡C' fv i)
                      ⇒ (trfill (NN Δ) C≡C' nm' i))
               * qfv
    in B [ ⌜ σ ⌝w , ⌜ v' ⌝V ]TV ,, neu fv' ,,
       $fv' ,, scvTV-unquote nm'' qfv'



  scv-quote : {Γ : Con} {A : Ty Γ} {v : Val Γ A} → scv v → Σ[ n ∈ Nf Γ A ] q v ⇒ n
  scv-quote {A = A} {v} scvv =
    let n ,, qv = scvTV-quote scvv
        p = trfill (Val _) ⌜evalT⌝ v
        q = trfill (Nf _) (⌜evalT⌝ ⁻¹) n
    in tr (Nf _) (⌜evalT⌝ ⁻¹) n ,, (λ i → q (p (1- i)) ⇒ (q i)) * qv

  scv-unquote : {Γ : Con} {A : Ty Γ} {v : NV Γ A} (n : NN Γ A) → qs v ⇒ n → scv (neu v)
  scv-unquote {A = A} {v} n qv =
    let p = trfill (NV _) ⌜evalT⌝ v
        q = trfill (NN _) ⌜evalT⌝ n
        scvv : scvTV (evalT A) (neu (tr (NV _) ⌜evalT⌝ v))
        scvv = scvTV-unquote (tr (NN _) ⌜evalT⌝ n) ((λ i → qs (p i) ⇒ (q i)) * qv)
        r : neu (tr (NV _) ⌜evalT⌝ v) ≡ tr (Val _) ⌜evalT⌝ (neu v)
        r = ≅-to-≡ {B = Val _} isSetTy (
              neu (tr (NV _) ⌜evalT⌝ v)  ≅⟨ apd neu (trfill (NV _) ⌜evalT⌝ v) ⁻¹ ⟩
              neu v                     ≅⟨ trfill (Val _) ⌜evalT⌝ (neu v) ⟩
              tr (Val _) ⌜evalT⌝ (neu v) ≅∎)
    in tr (scvTV (evalT A)) r scvv

  scvvar : {Γ : Con} {A : Ty Γ} {x : Var Γ A} → scv (neu (var x))
  scvvar {x = x} = scv-unquote (var x) qsvar

  sceid : {Γ : Con} → sce (idenv {Γ})
  sceid {●} = tt
  sceid {Γ , A} =
    (sceid {Γ}) +sce (wkw idw) ,, trd scv (trfill (Val _) [⌜id+E⌝] (neu (var z))) scvvar
