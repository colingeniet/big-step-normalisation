{-# OPTIONS --cubical #-}

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
_+N_ : {Γ Δ : Con} {A : Ty Δ} → Nf Δ A → (σ : Wk Γ Δ) → Nf Γ (A [ ⌜ σ ⌝w ])
_+NN_ : {Γ Δ : Con} {A : Ty Δ} → NN Δ A → (σ : Wk Γ Δ) → NN Γ (A [ ⌜ σ ⌝w ])

-- Weakening commutes with embedding
⌜⌝+N : {Γ Δ : Con} {A : Ty Δ} {n : Nf Δ A} {σ : Wk Γ Δ} →
       ⌜ n +N σ ⌝N ≈ ⌜ n ⌝N +t σ
⌜⌝+NN : {Γ Δ : Con} {A : Ty Δ} {n : NN Δ A} {σ : Wk Γ Δ} →
        ⌜ n +NN σ ⌝NN ≈ ⌜ n ⌝NN +t σ

abstract
  [⌜↑⌝] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {σ : Wk Γ Δ} →
          B Ty.[ ⌜ σ ↑w A ⌝w ] ≡ B [ ⌜ σ ⌝w ↑ A ]
  [⌜↑⌝] {B = B} = B [ ⌜↑w⌝ ]≈T

  private
    [<>][] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ , A)} {n : Nf Δ A} {σ : Wk Γ Δ} →
             B [ ⌜ σ ⌝w ↑ A ] [ < ⌜ n +N σ ⌝N > ] ≡ B [ < ⌜ n ⌝N > ] [ ⌜ σ ⌝w ]
    [<>][] {Γ} {Δ} {A} {B} {n} {σ} =
      B [ ⌜ σ ⌝w ↑ A ] [ < ⌜ n +N σ ⌝N > ] ≡⟨ [][]T ⁻¹ ⟩
      B [ (⌜ σ ⌝w ↑ A) ∘ < ⌜ n +N σ ⌝N > ] ≡⟨ B [ ↑∘<> ]≈T ⟩
      B [ ⌜ σ ⌝w , ⌜ n +N σ ⌝N ]           ≡⟨ B [ refl≋ ,≋ ⌜⌝+N ]≈T ⟩
      B [ ⌜ σ ⌝w , ⌜ n ⌝N [ ⌜ σ ⌝w ] ]     ≡⟨ B [ <>∘ ≋⁻¹ ]≈T ⟩
      B [ < ⌜ n ⌝N > ∘ ⌜ σ ⌝w ]            ≡⟨ [][]T ⟩
      B [ < ⌜ n ⌝N > ] [ ⌜ σ ⌝w ]          ∎


(lam {A = A} {B} n) +N σ =
  tr (Nf _) (Π[] ⁻¹)
     (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w _))))
(neuU n) +N σ =
  tr (Nf _) (U[] ⁻¹)
     (neuU (tr (NN _) U[] (n +NN σ)))
(neuEl n) +N σ = 
  tr (Nf _) (El[] ⁻¹)
     (neuEl (tr (NN _) El[] (n +NN σ)))

(var x) +NN σ = var (x +v σ)
(app f n) +NN σ =
  tr (NN _) ([<>][] {n = n})
     (app (tr (NN _) Π[] (f +NN σ)) (n +N σ))

abstract
  ⌜⌝+N {Γ} {n = lam {A = A} {B} n} {σ} =
    let p : ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N ≈ ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ]
        p = ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
              ≈⟨ apd ⌜_⌝N (trfill (Nf _) [⌜↑⌝] (n +N (σ ↑w A))) ⁻¹ ⟩'
            ⌜ n +N (σ ↑w A) ⌝N
              ≈⟨ ⌜⌝+N {n = n} ⟩
            ⌜ n ⌝N [ ⌜ σ ↑w A ⌝w ]
              ≈⟨ refl≈ [ ⌜↑w⌝ ]≈ ⟩
            ⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ] ≈∎
    in ⌜ tr (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)))) ⌝N
         ≈⟨ apd ⌜_⌝N (trfill (Nf _) (Π[] ⁻¹) (lam (tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A))))) ⁻¹ ⟩'
       lam ⌜ tr (Nf _) [⌜↑⌝] (n +N (σ ↑w A)) ⌝N
         ≈⟨ lam≈ p ⟩
       lam (⌜ n ⌝N [ ⌜ σ ⌝w ↑ A ])
         ≈⟨ lam[] ≈⁻¹ ⟩
       (lam ⌜ n ⌝N) [ ⌜ σ ⌝w ] ≈∎
  ⌜⌝+N {Γ} {n = neuU n} {σ} =
    ⌜ tr (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ))) ⌝N
      ≈⟨ apd ⌜_⌝N (trfill (Nf _) (U[] ⁻¹) (neuU (tr (NN _) U[] (n +NN σ)))) ⁻¹ ⟩'
    ⌜ tr (NN _) U[] (n +NN σ) ⌝NN
      ≈⟨ apd ⌜_⌝NN (trfill (NN _) U[] (n +NN σ)) ⁻¹ ⟩'
    ⌜ n +NN σ ⌝NN
      ≈⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≈∎
  ⌜⌝+N {Γ} {n = neuEl n} {σ} =
    ⌜ tr (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ))) ⌝N
      ≈⟨ apd ⌜_⌝N (trfill (Nf _) (El[] ⁻¹) (neuEl (tr (NN _) El[] (n +NN σ)))) ⁻¹ ⟩'
    ⌜ tr (NN _) El[] (n +NN σ) ⌝NN
      ≈⟨ apd ⌜_⌝NN (trfill (NN _) El[] (n +NN σ)) ⁻¹ ⟩'
    ⌜ n +NN σ ⌝NN
      ≈⟨ ⌜⌝+NN {n = n} ⟩
    ⌜ n ⌝NN +t σ ≈∎

  ⌜⌝+NN {n = var x} = ⌜⌝+v 
  ⌜⌝+NN {Γ} {Δ} {A} {app {B = B} f n} {σ} =
    let p : ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≈ tr (Tm Γ) Π[] (⌜ f ⌝NN +t σ)
        p = ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN ≈⟨ apd ⌜_⌝NN (trfill (NN Γ) Π[] (f +NN σ)) ⁻¹ ⟩'
            ⌜ f +NN σ ⌝NN                 ≈⟨ ⌜⌝+NN {n = f} ⟩
            ⌜ f ⌝NN +t σ                  ≈⟨ trfill (Tm Γ) Π[] (⌜ f ⌝NN +t σ) ⟩'
            tr (Tm Γ) Π[] (⌜ f ⌝NN +t σ)  ≈∎
        q : tr (Tm Γ) ([id]T ⁻¹) ⌜ n +N σ ⌝N ≈ tr (Tm Γ) ([id]T ⁻¹) (⌜ n ⌝N +t σ)
        q = tr (Tm Γ) ([id]T ⁻¹) ⌜ n +N σ ⌝N ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) ⌜ n +N σ ⌝N ⁻¹ ⟩'
            ⌜ n +N σ ⌝N                      ≈⟨ ⌜⌝+N {n = n} ⟩
            ⌜ n ⌝N +t σ                      ≈⟨ trfill (Tm Γ) ([id]T ⁻¹) (⌜ n ⌝N +t σ) ⟩'
            tr (Tm Γ) ([id]T ⁻¹) (⌜ n ⌝N +t σ) ≈∎
    in ⌜ tr (NN Γ) ([<>][] {n = n}) (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ)) ⌝NN
         ≈⟨ apd ⌜_⌝NN (trfill (NN Γ) ([<>][] {n = n})
                              (app (tr (NN Γ) Π[] (f +NN σ)) (n +N σ))) ⁻¹ ⟩'
       ⌜ tr (NN Γ) Π[] (f +NN σ) ⌝NN $ ⌜ n +N σ ⌝N
         ≈⟨ (app≈ p) [ refl≋ ,≋ q ]≈ ⟩
       (tr (Tm Γ) Π[] (⌜ f ⌝NN +t σ)) $ (⌜ n ⌝N +t σ)
         ≈⟨ $[] ≈⁻¹ ⟩
       (⌜ f ⌝NN $ ⌜ n ⌝N) +t σ ≈∎
{-
  private
    [⌜id⌝]T : {Γ : Con} {A : Ty Γ} → A [ ⌜ idw ⌝w ] ≡ A
    [⌜id⌝]T {Γ} {A} =
      A [ ⌜ idw ⌝w ] ≡⟨ ap (A [_]T) ⌜idw⌝ ⟩
      A [ id ]      ≡⟨ [id]T ⟩
      A              ∎
    [⌜∘⌝]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Wk Δ Θ} {ν : Wk Γ Δ} →
             A [ ⌜ σ ∘w ν ⌝w ] ≡ A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ]
    [⌜∘⌝]T {Γ} {Δ} {Θ} {A} {σ} {ν} =
      A [ ⌜ σ ∘w ν ⌝w ]       ≡⟨ ap (A [_]T) ⌜∘⌝w ⟩
      A [ ⌜ σ ⌝w ∘ ⌜ ν ⌝w ]    ≡⟨ [][]T ⟩
      A [ ⌜ σ ⌝w ] [ ⌜ ν ⌝w ] ∎

  -- Functoriality of weakening
  +Nid : {Γ : Con} {A : Ty Γ} {n : Nf Γ A} → n +N idw ≡[ ap (Nf Γ) [⌜id⌝]T ]≡ n
  +NNid : {Γ : Con} {A : Ty Γ} {n : NN Γ A} → n +NN idw ≡[ ap (NN Γ) [⌜id⌝]T ]≡ n

  +Nid {Γ} {n = lam {A = A} {B} n} =
    let p : A [ ⌜ idw ⌝w ] ≡ A
        p = A [ ⌜ idw ⌝w ] ≡⟨ ap (A [_]T) ⌜idw⌝ ⟩
            A [ id ]      ≡⟨ [id]T ⟩
            A              ∎
        q : Γ , A [ ⌜ idw ⌝w ] ≡ Γ , A
        q = ap (Γ ,_) p
        r : B [ ⌜ idw ⌝w ↑ A ] ≡[ ap Ty q ]≡ B
        r = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ] ≅⟨ apd (λ x → B [ x ↑ A ]) ⌜idw⌝ ⟩
            B [ id ↑ A ]      ≅⟨ ap≅ (B [_]T) ↑id ⟩'
            B [ id ]          ≅⟨ [id]T ⟩
            B ≅∎)
        r' : B [ ⌜ idw ↑w A ⌝w ] ≡[ ap Ty q ]≡ B [ ⌜ idw ⌝w ]
        r' = ≅-to-≡[] {B = Ty} isSetCon (
             B [ ⌜ idw ↑w A ⌝w ] ≅⟨ ap≅ (λ x → B [ ⌜ x ⌝w ]) ↑wid ⟩'
             B [ ⌜ idw ⌝w ]      ≅∎)
        s : (Γ , A [ ⌜ idw ⌝w ] ,, B [ ⌜ idw ↑w A ⌝w ]) ≡ (Γ , A ,, B [ ⌜ idw ⌝w ])
        s i = q i ,, r' i
        t : tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A))
            ≅[ (λ (x : Σ Con Ty) → Nf (fst x) (snd x)) ] n
        t = tr (Nf _) [⌜↑⌝] (n +N (idw ↑w A))
              ≅⟨ apd {B = λ _ → Σ Con Ty} ((Γ , A [ ⌜ idw ⌝w ]) ,,_) ([⌜↑⌝] {B = B} {σ = idw} ⁻¹)
               ∣ trfill (Nf _) ([⌜↑⌝] {B = B} {σ = idw}) (n +N (idw ↑w A)) ⁻¹ ⟩
            n +N (idw ↑w A)
              ≅⟨ s ∣ change-underlying {B = λ (x : Σ Con Ty) → Nf (fst x) (snd x)}
                                       (isSetΣ isSetCon isSetTy)
                                       {p = λ i → q i ,, B [ ⌜ ≅-to-≡[] isSetCon ↑wid {P = q} i ⌝w ]} {s}
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
        r : A [ ⌜ idw ⌝w ] ≡ A
        r = [⌜id⌝]T
        s : B [ ⌜ idw ⌝w ↑ A ] ≡[ ap (λ x → Ty (Γ , x)) r ]≡ B
        s = ≅-to-≡[] {B = Ty} isSetCon (
            B [ ⌜ idw ⌝w ↑ A ] ≅⟨ apd (λ x → B [ x ↑ A ]) ⌜idw⌝ ⟩
            B [ id ↑ A ]      ≅⟨ ap≅ (B [_]T) ↑id ⟩'
            B [ id ]          ≅⟨ [id]T ⟩
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
-}
