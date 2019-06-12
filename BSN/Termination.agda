{-# OPTIONS --cubical #-}

{-
  Proof of termination of eval and quote.
  
  Since eval and quote are defined as relation, termination means that
  every input is in relation with at least one output (in fact exactly one
  by determinism). The proof then allows to redifine eval/quote/nf as actual
  functions.
-}

module BSN.Termination where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Weakening
open import Syntax.Lemmas
import Syntax.Eliminator
open Syntax.Eliminator.Proposition
open import Variable.Variable
open import Value.Value
open import Value.Weakening
open import Value.Lemmas
open import Value.Sets
open import Evaluator.Evaluator
open import Evaluator.Soundness
open import Evaluator.Stability
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Evaluator
open import StrongComputability.StrongComputability
open import StrongComputability.Weakening
open import StrongComputability.Sets



{-
  Main theorem: any term in a strongly computable environment evaluates
  to a strongly computable value.
  The proof is by induction on terms. Except for the case of λ-abstractions,
  it is only a matter of applying the hypothesis to each other,
  and reorganising them to get the result.
-}
evalsce : {Δ : Con} {A : Ty Δ} (u : Tm Δ A) {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
          Σ[ B ∈ Ty Γ ] Σ[ uρ ∈ Val Γ B ] (eval u > ρ ⇒ uρ  ×  scv uρ)
evalssce : {Δ Θ : Con} (σ : Tms Δ Θ) {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
           Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ)


-- The theorem is defined using the eliminator.
evalsce-motives : Motives
open Motives evalsce-motives
Motives.Tmᴹ evalsce-motives {Δ} {A} u =
  {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
  Σ[ B ∈ Ty Γ ] Σ[ uρ ∈ Val Γ B ] (eval u > ρ ⇒ uρ  ×  scv uρ)
Motives.Tmsᴹ evalsce-motives {Δ} {Θ} σ =
  {Γ : Con} {ρ : Env Γ Δ} → sce ρ →
  Σ[ σρ ∈ Env Γ Θ ] (evals σ > ρ ⇒ σρ  ×  sce σρ)

evalsce-methods : Methods evalsce-motives
open Methods evalsce-methods

evalsce = elimTm
evalssce = elimTms

Methods.idᴹ evalsce-methods {ρ = ρ} sceρ =
  ρ ,, evalsid ,, sceρ
Methods._∘ᴹ_ evalsce-methods IHσ IHν sceρ =
  let νρ ,, evalsν ,, sceνρ = IHν sceρ
      σνρ ,, evalsσ ,, sceσνρ = IHσ sceνρ in
  σνρ ,, evals∘ evalsν evalsσ ,, sceσνρ
Methods.εᴹ evalsce-methods _ =
  ε ,, evalsε ,, tt
Methods._,ᴹ_ evalsce-methods {A = A} {σ} {u} IHσ IHu {ρ = ρ} sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      B ,, uρ ,, evalu ,, scvuρ = IHu sceρ
      p : B ≡ A [ ⌜ σρ ⌝E ]T
      p = evals,-aux evalsσ evalu
      uρ' = tr (Val _) p uρ
      scvuρ' = trd scv (trfill (Val _) p uρ) scvuρ
  in (σρ , uρ') ,, (evals, evalsσ evalu) ,, (sceσρ ,, scvuρ')
Methods.π₁ᴹ evalsce-methods IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ in
  π₁E σρ ,, evalsπ₁ evalsσ ,, π₁sce sceσρ

Methods._[_]ᴹ evalsce-methods IHu IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
      B ,, uσρ ,, evalu ,, scvuσρ = IHu sceσρ
  in B ,, uσρ ,, eval[] evalsσ evalu ,, scvuσρ
Methods.π₂ᴹ evalsce-methods IHσ sceρ =
  let σρ ,, evalsσ ,, sceσρ = IHσ sceρ
  in _ ,, π₂E σρ ,, evalπ₂ evalsσ ,, π₂sce sceσρ
Methods.lamᴹ evalsce-methods {A = A} {B} {u} IHu {ρ = ρ} sceρ =
  let luρ = lam u ρ
      luρ' = tr (Val _) Π[] luρ
      scvluρ' : scv luρ'
      scvluρ' = scvΠ-intro {f = luρ'} λ σ {v} scvv →
        let P : A [ ⌜ ρ ⌝E ]T [ ⌜ σ ⌝w ]T ≡ A [ ⌜ ρ +E σ ⌝E ]T
            P = [+E] ⁻¹
            v' : Val _ (A [ ⌜ ρ +E σ ⌝E ]T)
            v' = tr (Val _) P v
            v≡v' : v ≡[ ap (Val _) P ]≡ v'
            v≡v' = trfill (Val _) P v
            scvv' : scv v'
            scvv' = trd scv v≡v' scvv
            C ,, uρv ,, evaluρv ,, scvuρv = IHu {ρ = ρ +E σ , v'} (sceρ +sce σ ,, scvv')
            Q : B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T
                ≡[ ap (λ x → Ty (_ , x)) P ]≡ B [ ⌜ ρ +E σ ⌝E ↑ A ]T
            Q = ≅-to-≡[] {B = Ty} isSetCon (
                  B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T
                    ≅⟨ [][]T ⁻¹ ⟩
                  B [ (⌜ ρ ⌝E ↑ A) ∘ (⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T)) ]T
                    ≅⟨ ap≅ (B [_]T) ↑∘↑ ⟩'
                  B [ (⌜ ρ ⌝E ∘ ⌜ σ ⌝w) ↑ A ]T
                    ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜⌝+E ⁻¹ ⟩
                  B [ ⌜ ρ +E σ ⌝E ↑ A ]T ≅∎)
            R : Π (A [ ⌜ ρ +E σ ⌝E ]T) (B [ ⌜ ρ +E σ ⌝E ↑ A ]T)
                ≡ Π (A [ ⌜ ρ ⌝E ]T [ ⌜ σ ⌝w ]T) (B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ σ ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T)
            R i = Π (P (1- i)) (Q (1- i))
            luρ+ = tr (Val _) Π[] (lam u (ρ +E σ))
            luρ+' = tr (Val _) Π[] (tr (Val _) Π[] (lam u ρ) +V σ)
            luρ+≡luρ+' : luρ+ ≡[ ap (Val _) R ]≡ luρ+'
            luρ+≡luρ+' = ≅-to-≡[] {B = Val _} isSetTy (
                           luρ+                          ≅⟨ trfill (Val _) Π[] (lam u (ρ +E σ)) ⁻¹ ⟩
                           lam u (ρ +E σ)                ≅⟨ trfill (Val _) [+E] (lam u (ρ +E σ)) ⟩
                           (lam u ρ) +V σ                ≅⟨ apd (_+V σ) (trfill (Val _) Π[] (lam u ρ)) ⟩
                           tr (Val _) Π[] (lam u ρ) +V σ ≅⟨ trfill (Val _) Π[] _ ⟩
                           luρ+'                         ≅∎)
            $uρv : luρ+ $ v' ⇒ uρv
            $uρv = $lam evaluρv
            $uρv' = luρ+' $ v ⇒ uρv
            $uρv' = (λ i → (luρ+≡luρ+' i) $ (v≡v' (1- i)) ⇒ uρv)
                    * $uρv
        in C ,, uρv ,, $uρv' ,, scvuρv
      scvluρ : scv luρ
      scvluρ = trd scv (trfill (Val _) Π[] luρ ⁻¹) scvluρ'
  in _ ,, lam u ρ ,, evallam u ρ ,, scvluρ
Methods.appᴹ evalsce-methods {A = A} {B} {f} IHf {Γ} {ρ , v} (sceρ ,, scvv) =
  let C ,, fρ ,, evalfρ ,, scvfρ = IHf sceρ
      P : C ≡ Π (A [ ⌜ ρ ⌝E ]T) (B [ ⌜ ρ ⌝E ↑ A ]T)
      P = C                                    ≡⟨ fst (eval≡ evalfρ) ⁻¹ ⟩
          Π A B [ ⌜ ρ ⌝E ]T                    ≡⟨ Π[] ⟩
          Π (A [ ⌜ ρ ⌝E ]T) (B [ ⌜ ρ ⌝E ↑ A ]T) ∎
      fρ' = tr (Val Γ) P fρ
      fρ≡fρ' = trfill (Val Γ) P fρ
      evalfρ' = trd (eval f > ρ ⇒_) fρ≡fρ' evalfρ
      scvfρ' = trd scv fρ≡fρ' scvfρ
      Q : A [ ⌜ ρ ⌝E ]T ≡ A [ ⌜ ρ ⌝E ]T [ ⌜ idw ⌝w ]T
      Q = A [ ⌜ ρ ⌝E ]T              ≡⟨ [id]T ⁻¹ ⟩
          A [ ⌜ ρ ⌝E ]T [ id ]T      ≡⟨ ap (A [ ⌜ ρ ⌝E ]T [_]T) ⌜idw⌝ ⁻¹ ⟩
          A [ ⌜ ρ ⌝E ]T [ ⌜ idw ⌝w ]T ∎
      v' = tr (Val Γ) Q v
      v≡v' = trfill (Val Γ) Q v
      scvv' = trd scv v≡v' scvv
      D ,, fρv ,, $fρv ,, scvfρv = scvΠ-elim {f = fρ'} scvfρ' idw {v = v'} scvv'
      fρ'' = tr (Val Γ) Π[] (fρ' +V idw)
      -- $fρv : fρ'' $ v' ⇒ fρv
      R : B [ ⌜ ρ ⌝E ↑ A ]T ≡[ ap (λ x → Ty (_ , x)) Q ]≡ B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ idw ⌝w ↑ _ ]T
      R = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ ρ ⌝E ↑ A ]T         ≅⟨ [id]T ⁻¹ ⟩
            B [ ⌜ ρ ⌝E ↑ A ]T [ id ]T ≅⟨ ap≅ (B [ ⌜ ρ ⌝E ↑ A ]T [_]T) ↑id ≅⁻¹ ⟩'
            B [ ⌜ ρ ⌝E ↑ A ]T [ id ↑ (A [ ⌜ ρ ⌝E ]T) ]T
              ≅⟨ apd (λ x → B [ ⌜ ρ ⌝E ↑ A ]T [ x ↑ (A [ ⌜ ρ ⌝E ]T) ]T) ⌜idw⌝ ⁻¹ ⟩
            B [ ⌜ ρ ⌝E ↑ A ]T [ ⌜ idw ⌝w ↑ (A [ ⌜ ρ ⌝E ]T) ]T ≅∎)
      fρ''≡fρ' : fρ'' ≡[ (λ i → Val Γ (Π (Q (1- i)) (R (1- i)))) ]≡ fρ'
      fρ''≡fρ' = ≅-to-≡[] {B = Val _} isSetTy (
                   fρ''       ≅⟨ trfill (Val Γ) Π[] (fρ' +V idw) ⁻¹ ⟩
                   fρ' +V idw ≅⟨ +Vid ⟩
                   fρ'        ≅∎)
      $fρv' : fρ' $ v ⇒ fρv
      $fρv' = (λ i → (fρ''≡fρ' i) $ (v≡v' (1- i)) ⇒ fρv)
              * $fρv
  in D ,, fρv ,, evalapp evalfρ' $fρv' ,, scvfρv

Methods.isPropTmᴹ evalsce-methods {Δ} {A} {u} x y i {Γ} {ρ} sceρ =
  let B ,, uρ ,, evalu ,, scvuρ = x sceρ
      B' ,, uρ' ,, evalu' ,, scvuρ' = y sceρ
      B≡B' ,≅ uρ≡uρ' = eval-sound evalu evalu'
  in B≡B' i ,,
     uρ≡uρ' i ,,
     isPropPath {B = λ i → eval u > ρ ⇒ (uρ≡uρ' i)} isPropeval evalu evalu' i ,,
     isPropPath {B = λ i → scv (uρ≡uρ' i)} (λ {i} → isPropscv {v = uρ≡uρ' i}) scvuρ scvuρ' i
Methods.isPropTmsᴹ evalsce-methods {Δ} {Θ} {σ} x y i {Γ} {ρ} sceρ =
  let σρ ,, evalsσ ,, scvσρ = x sceρ
      σρ' ,, evalsσ' ,, scvσρ' = y sceρ
      σρ≡σρ' : σρ ≡ σρ'
      σρ≡σρ' = evals-sound evalsσ evalsσ'
  in σρ≡σρ' i ,,
     isPropDependent {B = λ x → evals σ > ρ ⇒ x} isPropevals
                     σρ≡σρ' evalsσ evalsσ' i ,,
     isPropDependent {B = sce} isPropsce σρ≡σρ' scvσρ scvσρ' i
