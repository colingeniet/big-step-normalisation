{-# OPTIONS --safe --cubical #-}

module NormalForm.Weakening where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Weakening
open import Variable.Variable
open import Variable.Lemmas
open import NormalForm.NormalForm


-- Weakening of normal forms
_+N_ : {Γ Δ : Con} {A : Ty Δ} → Nf Δ A → (σ : Wk Γ Δ) → Nf Γ (A [ ⌜ σ ⌝w ]T)
_+NN_ : {Γ Δ : Con} {A : Ty Δ} → NN Δ A → (σ : Wk Γ Δ) → NN Γ (A [ ⌜ σ ⌝w ]T)

-- Weakening commutes with embedding
⌜⌝+N : {Γ Δ : Con} {A : Ty Δ} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≡ ⌜ n ⌝N +t σ
⌜⌝+NN : {Γ Δ : Con} {A : Ty Δ} {n : NN Δ A} {σ : Wk Γ Δ} →
        ⌜ n +NN σ ⌝NN ≡ ⌜ n ⌝NN +t σ

abstract
  [⌜↑⌝] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Wk Γ Δ} →
          B [ ⌜ σ ↑w A ⌝w ]T ≡ B [ ⌜ σ ⌝w ↑ A ]T
  [⌜↑⌝] {B = B} = ap (B [_]T) ⌜↑w⌝

  private
    [<>][] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {n : Nf Δ A} {σ : Wk Γ Δ} →
             B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ n +N σ ⌝N > ]T ≡ B [ < ⌜ n ⌝N > ]T [ ⌜ σ ⌝w ]T
    [<>][] {Γ} {Δ} {A} {B} {n} {σ} =
      B [ ⌜ σ ⌝w ↑ A ]T [ < ⌜ n +N σ ⌝N > ]T ≡⟨ [][]T ⁻¹ ⟩
      B [ (⌜ σ ⌝w ↑ A) ∘ < ⌜ n +N σ ⌝N > ]T  ≡⟨ ap (λ x → B [ x ]T) ↑∘<> ⟩
      B [ ⌜ σ ⌝w , ⌜ n +N σ ⌝N ]T            ≡⟨ ap (λ x → B [ _ , x ]T) ⌜⌝+N ⟩
      B [ ⌜ σ ⌝w , ⌜ n ⌝N [ ⌜ σ ⌝w ] ]T      ≡⟨ ap (B [_]T) <>∘ ⁻¹ ⟩
      B [ < ⌜ n ⌝N > ∘ ⌜ σ ⌝w ]T             ≡⟨ [][]T ⟩
      B [ < ⌜ n ⌝N > ]T [ ⌜ σ ⌝w ]T          ∎


(lam {A = A} {B} n) +N σ =
  tr (Nf _) (Π[] ⁻¹)
     (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w _))))
(neuU n) +N σ =
  tr (Nf _) (U[] ⁻¹)
     (neuU (tr (NN _) U[] (n +NN σ)))
(neuEl n) +N σ = 
  tr (Nf _) (El[] ⁻¹)
     (neuEl (tr (NN _) El[] (n +NN σ)))
(isSetNf p q i j) +N σ =
  isSetNf (λ k → p k +N σ) (λ k → q k +N σ) i j

(var x) +NN σ = var (x +v σ)
(app f n) +NN σ =
  tr (NN _) ([<>][] {n = n})
     (app (tr (NN _) Π[] (f +NN σ)) (n +N σ))
(isSetNN p q i j) +NN σ =
  isSetNN (λ k → p k +NN σ) (λ k → q k +NN σ) i j


abstract
  ⌜⌝+N {Γ} {n = lam {A = A} {B} n} {σ} =
    let p : ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
            ≅[ Tm (Γ , A [ ⌜ σ ⌝w ]T) ]
            ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ]
        p = ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
              ≅⟨ apd ⌜_⌝N (trfill (Nf _) [⌜↑⌝] (n +N (σ ↑w A))) ⁻¹ ⟩
            ⌜ n +N (σ ↑w A) ⌝N
              ≅⟨ ⌜⌝+N {n = n} ⟩
            ⌜ n ⌝N [ ⌜ σ ↑w A ⌝w ]
              ≅⟨ apd (⌜ n ⌝N [_]) ⌜↑w⌝ ⟩
            ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ] ≅∎
    in ≅-to-≡ {B = Tm Γ} isSetTy (
       ⌜ tr (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)))) ⌝N
         ≅⟨ apd ⌜_⌝N (trfill (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A))))) ⁻¹ ⟩
       lam ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
         ≅⟨ ap≅ lam p ⟩'
       lam (⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ])
         ≅⟨ lam[] ≅⁻¹ ⟩'
       (lam ⌜ n ⌝N) [ ⌜ σ ⌝w ] ≅∎)
  ⌜⌝+N {Γ} {n = neuU n} {σ} = ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ))) ⌝N
      ≅⟨ apd ⌜_⌝N (trfill (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ)))) ⁻¹ ⟩
    ⌜ tr (NN _) U[] (n +NN σ) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN _) U[] (n +NN σ)) ⁻¹ ⟩
    ⌜ n +NN σ ⌝NN
      ≅⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≅∎)
  ⌜⌝+N {Γ} {n = neuEl n} {σ} = ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ))) ⌝N
      ≅⟨ apd ⌜_⌝N (trfill (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ)))) ⁻¹ ⟩
    ⌜ tr (NN _) El[] (n +NN σ) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN _) El[] (n +NN σ)) ⁻¹ ⟩
    ⌜ n +NN σ ⌝NN
      ≅⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≅∎)
  ⌜⌝+N {n = isSetNf p q i j} {σ} k =
    ouc (isSetPartial isSetTm
                      (λ j → ⌜⌝+N {n = p j} {σ} k)
                      (λ j → ⌜⌝+N {n = q j} {σ} k)
                      (λ {(k = i0) → λ i j →
                          ⌜ isSetNf (λ j → p j +N σ) (λ j → q j +N σ) i j ⌝N;
                          (k = i1) → λ i j →
                          ⌜ isSetNf p q i j ⌝N +t σ}))
        i j
    
  ⌜⌝+NN {n = var x} = ⌜⌝+v 
  ⌜⌝+NN {Γ} {Δ} {A} {app {B = B} f n} {σ} =
    let p : ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≅[ Tm Γ ] tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN
        p = ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≅⟨ apd ⌜_⌝NN (trfill (NN Γ) Π[] (f +NN σ)) ⁻¹ ⟩
            ⌜ f +NN σ ⌝NN                 ≅⟨ trfill (Tm Γ) Π[] ⌜ f +NN σ ⌝NN ⟩
            tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN   ≅∎
    in ≅-to-≡ {B = Tm Γ} isSetTy (
    ⌜ tr (NN Γ) ([<>][] {n = n}) (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ)) ⌝NN
      ≅⟨ apd ⌜_⌝NN (trfill (NN Γ) ([<>][] {n = n})
                           (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ))) ⁻¹ ⟩
    ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN $ ⌜ n +N σ ⌝N
      ≅⟨ (λ i → ≅-to-≡ isSetTy p i $ ⌜ n +N σ ⌝N) ⟩
    (tr (Tm Γ) Π[] ⌜ f +NN σ ⌝NN) $ ⌜ n +N σ ⌝N
      ≅⟨ apd (λ x → tr (Tm Γ) Π[] x $ ⌜ n +N σ ⌝N) (⌜⌝+NN {n = f}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $ ⌜ n +N σ ⌝N
      ≅⟨ apd ((tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $_) (⌜⌝+N {n = n}) ⟩
    (tr (Tm Γ) Π[] (⌜ f ⌝NN [ ⌜ σ ⌝w ])) $ (⌜ n ⌝N [ ⌜ σ ⌝w ])
      ≅⟨ $[] ≅⁻¹ ⟩'
    (⌜ f ⌝NN $ ⌜ n ⌝N) [ ⌜ σ ⌝w ] ≅∎)
  ⌜⌝+NN {n = isSetNN p q i j} {σ} k =
    ouc (isSetPartial isSetTm
                      (λ j → ⌜⌝+NN {n = p j} {σ} k)
                      (λ j → ⌜⌝+NN {n = q j} {σ} k)
                      (λ {(k = i0) → λ i j →
                          ⌜ isSetNN (λ j → p j +NN σ) (λ j → q j +NN σ) i j ⌝NN;
                          (k = i1) → λ i j →
                          ⌜ isSetNN p q i j ⌝NN +t σ}))
        i j


  private
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

  -- Functoriality of weakening
  +Nid : {Γ : Con} {A : Ty Γ} {n : Nf Γ A} → n +N idw ≡[ ap (Nf Γ) [⌜id⌝]T ]≡ n
  +NNid : {Γ : Con} {A : Ty Γ} {n : NN Γ A} → n +NN idw ≡[ ap (NN Γ) [⌜id⌝]T ]≡ n

  +Nid {Γ} {n = lam {A = A} {B} n} =
    let p : A [ ⌜ idw ⌝w ]T ≡ A
        p = A [ ⌜ idw ⌝w ]T ≡⟨ ap (A [_]T) ⌜idw⌝ ⟩
            A [ id ]T      ≡⟨ [id]T ⟩
            A              ∎
        q : Γ , A [ ⌜ idw ⌝w ]T ≡ Γ , A
        q = ap (Γ ,_) p
        r : B [ ⌜ idw ⌝w ↑ A ]T ≡[ ap Ty q ]≡ B
        r = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ]T ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜idw⌝ ⟩
            B [ id ↑ A ]T      ≅⟨ ap≅ (B [_]T) ↑id ⟩'
            B [ id ]T          ≅⟨ [id]T ⟩
            B ≅∎)
        r' : B [ ⌜ idw ↑w A ⌝w ]T ≡[ ap Ty q ]≡ B [ ⌜ idw ⌝w ]T
        r' = ≅-to-≡[] {B = Ty} isSetCon (
             B [ ⌜ idw ↑w A ⌝w ]T ≅⟨ ap≅ (λ x → B [ ⌜ x ⌝w ]T) ↑wid ⟩'
             B [ ⌜ idw ⌝w ]T      ≅∎)
        s : (Γ , A [ ⌜ idw ⌝w ]T ,, B [ ⌜ idw ↑w A ⌝w ]T) ≡ (Γ , A ,, B [ ⌜ idw ⌝w ]T)
        s i = q i ,, r' i
        t : tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A))
            ≅[ (λ (x : Σ Con Ty) → Nf (fst x) (snd x)) ] n
        t = tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A))
              ≅⟨ apd {B = λ _ → Σ Con Ty} ((Γ , A [ ⌜ idw ⌝w ]T) ,,_) ([⌜↑⌝] {B = B} {σ = idw} ⁻¹)
               ∣ trfill (Nf _) ([⌜↑⌝] {B = B} {σ = idw}) (n +N (idw ↑w A)) ⁻¹ ⟩
            n +N (idw ↑w A)
              ≅⟨ s ∣ change-underlying {B = λ (x : Σ Con Ty) → Nf (fst x) (snd x)}
                                       (isSetΣ isSetCon isSetTy)
                                       {p = λ i → q i ,, B [ ⌜ ≅-to-≡[] isSetCon ↑wid {P = q} i ⌝w ]T} {s}
                                       (apd (n +N_) (≅-to-≡[] isSetCon ↑wid {P = q})) ⟩
            n +N idw
              ≅⟨ ap (Γ , A ,,_) [⌜id⌝]T ∣ +Nid {n = n} ⟩
            n ≅∎
    in ≅-to-≡[] {B = Nf Γ} isSetTy (
         tr (Nf Γ) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A))))
           ≅⟨ trfill (Nf Γ) (Π[] ⁻¹) _ ⁻¹ ⟩
         lam (tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A)))
           ≅⟨ (λ i → lam (≅-to-≡[] (isSetΣ isSetCon isSetTy) t {P = λ i → q i ,, r i} i)) ⟩
         lam n ≅∎)
  +Nid {Γ} {n = neuU n} =
    let p : tr (NN Γ) U[] (n +NN idw) ≅[ NN Γ ] n
        p = tr (NN Γ) U[] (n +NN idw) ≅⟨ trfill (NN Γ) U[] (n +NN idw) ⁻¹ ⟩
            n +NN idw                 ≅⟨ +NNid ⟩
            n                         ≅∎
    in ≅-to-≡[] {B = Nf Γ} isSetTy (
         tr (Nf Γ) (U[] ⁻¹) (neuU (tr (NN Γ) U[] (n +NN idw)))
           ≅⟨ trfill (Nf Γ) (U[] ⁻¹) _ ⁻¹ ⟩
         neuU (tr (NN Γ) U[] (n +NN idw))
           ≅⟨ apd neuU (≅-to-≡ isSetTy p) ⟩
         neuU n ≅∎)
  +Nid {Γ} {n = neuEl {u = u} n} =
    let P : tr (Tm Γ) U[] (u +t idw) ≡ u
        P = ≅-to-≡ isSetTy (
            tr (Tm Γ) U[] (u +t idw) ≅⟨ trfill (Tm Γ) U[] (u +t idw) ⁻¹ ⟩
            u [ ⌜ idw ⌝w ]           ≅⟨ apd (u [_]) ⌜idw⌝ ⟩
            u [ id ]                ≅⟨ [id] ⟩'
            u                       ≅∎)
        p : tr (NN Γ) El[] (n +NN idw) ≅[ NN Γ ] n
        p = tr (NN Γ) El[] (n +NN idw) ≅⟨ trfill (NN Γ) El[] (n +NN idw) ⁻¹ ⟩
            n +NN idw                  ≅⟨ +NNid ⟩
            n                          ≅∎
    in ≅-to-≡[] {B = Nf Γ} isSetTy (
         tr (Nf Γ) (El[] ⁻¹) (neuEl (tr (NN Γ) El[] (n +NN idw)))
           ≅⟨ trfill (Nf Γ) (El[] ⁻¹) _ ⁻¹ ⟩
         neuEl (tr (NN Γ) El[] (n +NN idw))
           ≅⟨ apd neuEl (≅-to-≡[] isSetTy p {P = ap El P}) ⟩
         neuEl n ≅∎)
  +Nid {n = isSetNf p q i j} k =
    ouc (isSetPartial isSetNf
                      (λ j → +Nid {n = p j} k)
                      (λ j → +Nid {n = q j} k)
                      (λ {(k = i0) → λ i j →
                          (isSetNf p q i j) +N idw;
                          (k = i1) → isSetNf p q}))
        i j

  +NNid {n = var x} = apd var (≅-to-≡[] isSetTy +vid)
  +NNid {Γ} {n = app {A = A} {B} f n} =
    let p : tr (NN Γ) Π[] (f +NN idw) ≅[ NN Γ ] f
        p = tr (NN Γ) Π[] (f +NN idw) ≅⟨ trfill (NN Γ) Π[] _ ⁻¹ ⟩
            f +NN idw                 ≅⟨ +NNid ⟩
            f                         ≅∎
        q : n +N idw ≅[ Nf Γ ] n
        q = n +N idw ≅⟨ +Nid ⟩
            n ≅∎
        r : A [ ⌜ idw ⌝w ]T ≡ A
        r = [⌜id⌝]T
        s : B [ ⌜ idw ⌝w ↑ A ]T ≡[ ap (λ x → Ty (Γ , x)) r ]≡ B
        s = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ]T ≅⟨ apd (λ x → B [ x ↑ A ]T) ⌜idw⌝ ⟩
            B [ id ↑ A ]T      ≅⟨ ap≅ (B [_]T) ↑id ⟩'
            B [ id ]T          ≅⟨ [id]T ⟩
            B                  ≅∎)
    in ≅-to-≡[] {B = NN Γ} isSetTy (
         tr (NN Γ) ([<>][] {n = n}) (app (tr (NN Γ) Π[] (f +NN idw)) (n +N idw))
           ≅⟨ trfill (NN Γ) ([<>][] {n = n}) _ ⁻¹ ⟩
         app (tr (NN Γ) Π[] (f +NN idw)) (n +N idw)
           ≅⟨ (λ i → app (≅-to-≡[] isSetTy p {P = λ i → Π (r i) (s i)} i)
                         (≅-to-≡[] isSetTy q {P = r} i)) ⟩
         app f n ≅∎)
  +NNid {n = isSetNN p q i j} k =
    ouc (isSetPartial isSetNN
                      (λ j → +NNid {n = p j} k)
                      (λ j → +NNid {n = q j} k)
                      (λ {(k = i0) → λ i j →
                          (isSetNN p q i j) +NN idw;
                          (k = i1) → isSetNN p q}))
        i j

{-
  +N∘ : {Γ Δ Θ : Con} {A : Ty Θ} {n : Nf Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
        n +N (σ ∘w ν) ≅[ Nf Γ ] (n +N σ) +N ν
  +NN∘ : {Γ Δ Θ : Con} {A : Ty Θ} {n : NN Θ A} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
         n +NN (σ ∘w ν) ≅[ NN Γ ] (n +NN σ) +NN ν

  +NN∘ {n = var x} = ap≅ var (+v∘ {x = x})
  +NN∘ {n = app f n} = {!!}

  +N∘ {n = lam {A = A} n} {σ} {ν} =
    lam (n +N (wk↑ A (σ ∘w ν)))     ≡⟨ ap (λ ρ → lam (n +N (ρ ,, z))) wk∘↑w ⟩
    lam (n +N (wk↑ A σ ∘w wk↑ A ν)) ≡⟨ ap lam +N∘ ⟩
    (lam n +N σ) +N ν               ∎
  +N∘ {n = neu n} = ap neu +NN∘
  +NN∘ {n = var x} = ap var (+v∘ {x = x})
  +NN∘ {n = app f n} = ap2 app +NN∘ +N∘
-}
