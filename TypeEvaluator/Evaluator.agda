{-# OPTIONS --cubical --allow-unsolved-meta #-}

module TypeEvaluator.Evaluator where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import TypeEvaluator.Skeleton
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Sets


infixl 30 _[_]TV

_[_]TV : {S : TSk} {Γ Δ : Con} → TV S Δ → Tms Γ Δ → TV S Γ
⌜[]TV⌝ : {S : TSk} {Γ Δ : Con} {A : TV S Δ} {σ : Tms Γ Δ} →
         ⌜ A ⌝T [ σ ]T ≡ ⌜ A [ σ ]TV ⌝T

U [ σ ]TV = U
(El u) [ σ ]TV = El (tr (Tm _) U[] (u [ σ ]))
(Π A B) [ σ ]TV = Π (A [ σ ]TV) (tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV))

abstract
  ⌜[]TV⌝ {A = U} = U[]
  ⌜[]TV⌝ {A = El u} = El[]
  ⌜[]TV⌝ {A = Π A B} {σ} =
    let p : ⌜ A ⌝T [ σ ]T ≡ ⌜ A [ σ ]TV ⌝T
        p = ⌜[]TV⌝
        q : ⌜ B ⌝T [ σ ↑ ⌜ A ⌝T ]T ≅[ Ty ] ⌜ tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV) ⌝T
        q = ⌜ B ⌝T [ σ ↑ ⌜ A ⌝T ]T
              ≅⟨ ⌜[]TV⌝ ⟩
            ⌜ B [ σ ↑ ⌜ A ⌝T ]TV ⌝T
              ≅⟨ apd ⌜_⌝T (trfill (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV)) ⟩
            ⌜ tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV) ⌝T ≅∎
    in (Π ⌜ A ⌝T ⌜ B ⌝T) [ σ ]T
         ≡⟨ Π[] ⟩
       Π (⌜ A ⌝T [ σ ]T) (⌜ B ⌝T [ σ ↑ ⌜ A ⌝T ]T)
         ≡⟨ (λ i → Π (p i) (≅-to-≡[] isSetCon q {P = ap (_ ,_) p} i)) ⟩
       Π ⌜ A [ σ ]TV ⌝T ⌜ tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV) ⌝T ∎


  [id]TV : {S : TSk} {Γ : Con} {A : TV S Γ} → A [ id ]TV ≡ A
  [id]TV {A = U} = refl
  [id]TV {A = El u} =
    let p : tr (Tm _) U[] (u [ id ]) ≡ u
        p = ≅-to-≡ isSetTy (
              tr (Tm _) U[] (u [ id ]) ≅⟨ trfill (Tm _) U[] (u [ id ]) ⁻¹ ⟩
              u [ id ]                 ≅⟨ [id] ⟩'
              u                        ≅∎)
    in ap El p
  [id]TV {A = Π A B} i =
    let p : A [ id ]TV ≡ A
        p = [id]TV
        q : tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ id ↑ ⌜ A ⌝T ]TV) ≅[ TV _ ] B
        q = tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ id ↑ ⌜ A ⌝T ]TV)
              ≅⟨ trfill (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ id ↑ ⌜ A ⌝T ]TV) ⁻¹ ⟩
            B [ id ↑ ⌜ A ⌝T ]TV ≅⟨ ap≅ (B [_]TV) ↑id ⟩'
            B [ id ]TV         ≅⟨ [id]TV ⟩
            B                  ≅∎
    in Π (p i) (≅-to-≡[] isSetCon q {P = ap (λ x → _ , ⌜ x ⌝T) p} i)

  [][]TV : {S : TSk} {Γ Δ Θ : Con} {A : TV S Θ} {σ : Tms Δ Θ} {ν : Tms Γ Δ} →
            A [ σ ∘ ν ]TV ≡ A [ σ ]TV [ ν ]TV
  [][]TV {A = U} = refl
  [][]TV {A = El u} {σ} {ν} =
    let p : tr (Tm _) U[] (u [ σ ∘ ν ]) ≡ tr (Tm _) U[] (tr (Tm _) U[] (u [ σ ]) [ ν ])
        p = ≅-to-≡ {B = Tm _} isSetTy (
              tr (Tm _) U[] (u [ σ ∘ ν ])     ≅⟨ trfill (Tm _) U[] (u [ σ ∘ ν ]) ⁻¹ ⟩
              u [ σ ∘ ν ]                     ≅⟨ [][] ⟩'
              u [ σ ] [ ν ]                   ≅⟨ apd (_[ ν ]) (trfill (Tm _) U[] (u [ σ ])) ⟩
              (tr (Tm _) U[] (u [ σ ])) [ ν ] ≅⟨ trfill (Tm _) U[] _ ⟩
              tr (Tm _) U[] (tr (Tm _) U[] (u [ σ ]) [ ν ]) ≅∎)
    in ap El p
  [][]TV {A = Π A B} {σ} {ν} i =
    let p : A [ σ ∘ ν ]TV ≡ A [ σ ]TV [ ν ]TV
        p = [][]TV
        q : tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ (σ ∘ ν) ↑ ⌜ A ⌝T ]TV)
            ≅[ TV _ ]
            tr (λ x → TV _ (_ , x)) ⌜[]TV⌝
               (tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV) [ ν ↑ ⌜ A [ σ ]TV ⌝T ]TV)
        q = tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ (σ ∘ ν) ↑ ⌜ A ⌝T ]TV)
              ≅⟨ trfill (λ x → TV _ (_ , x)) ⌜[]TV⌝ _ ⁻¹ ⟩
            B [ (σ ∘ ν) ↑ ⌜ A ⌝T ]TV
              ≅⟨ ap≅ (B [_]TV) ↑∘↑ ≅⁻¹ ⟩'
            B [ (σ ↑ ⌜ A ⌝T) ∘ (ν ↑ ⌜ A ⌝T [ σ ]T) ]TV
              ≅⟨ [][]TV ⟩
            B [ σ ↑ ⌜ A ⌝T ]TV [ ν ↑ ⌜ A ⌝T [ σ ]T ]TV
              ≅⟨ apd (_[ ν ↑ _ ]TV) (trfill (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV)) ⟩
            (tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ ⌜ A ⌝T ]TV) [ ν ↑ ⌜ A [ σ ]TV ⌝T ]TV)
              ≅⟨ trfill (λ x → TV _ (_ , x)) ⌜[]TV⌝ _ ⟩
            tr (λ x → TV _ (_ , x)) ⌜[]TV⌝
               (tr (λ x → TV _ (_ , x)) ⌜[]TV⌝ (B [ σ ↑ _ ]TV) [ ν ↑ _ ]TV) ≅∎
    in Π (p i) (≅-to-≡[] isSetCon q {P = ap (λ x → _ , ⌜ x ⌝T) p} i)



evalT : {Γ : Con} (A : Ty Γ) → TV (skeleton A) Γ
⌜evalT⌝ : {Γ : Con} {A : Ty Γ} → A ≡ ⌜ evalT A ⌝T

evalT U = U
evalT (El u) = El u
evalT (Π A B) = Π (evalT A) (tr (λ x → TV (skeleton B) (_ , x)) ⌜evalT⌝ (evalT B))
evalT (A [ σ ]T) = (evalT A) [ σ ]TV
evalT ([id]T {A = A} i) = [id]TV {A = evalT A} i
evalT ([][]T {A = A} {σ} {ν} i) = [][]TV {A = evalT A} {σ} {ν} i
evalT (U[] i) = U
evalT (El[] {u = u} {σ} i) = El (tr (Tm _) U[] (u [ σ ]))
evalT (Π[] {A = A} {B} {σ} i) =
  let T = skeleton B
      p : tr (λ x → TV T (_ , x)) ⌜[]TV⌝
             (tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B) [ σ ↑ ⌜ evalT A ⌝T ]TV)
          ≅[ TV T ] tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B [ σ ↑ A ]TV)
      p = tr (λ x → TV T (_ , x)) ⌜[]TV⌝
             (tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B) [ σ ↑ ⌜ evalT A ⌝T ]TV)
            ≅⟨ trfill (λ x → TV T (_ , x)) ⌜[]TV⌝ _ ⁻¹ ⟩
          tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B) [ σ ↑ ⌜ evalT A ⌝T ]TV
            ≅⟨ apd (_[ σ ↑ _ ]TV) (trfill (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B)) ⁻¹ ⟩
          evalT B [ σ ↑ A ]TV
            ≅⟨ trfill (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B [ σ ↑ A ]TV) ⟩
          tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B [ σ ↑ A ]TV) ≅∎
      q : evalT (Π A B [ σ ]T) ≡ evalT (Π (A [ σ ]T) (B [ σ ↑ A ]T))
      q = ap (Π (evalT A [ σ ]TV)) (≅-to-≡ isSetCon p)
  in {!q i!}
evalT (isSetTy p q i j) =
  isSetDependent2 {B = λ x → TV x _} isSetTSk isSetTV
                  (λ k → evalT (p k)) (λ k → evalT (q k)) i j

abstract
  ⌜evalT⌝ {A = U} = refl
  ⌜evalT⌝ {A = El u} = refl
  ⌜evalT⌝ {A = Π A B} =
    let T = skeleton B
        p : A ≡ ⌜ evalT A ⌝T
        p = ⌜evalT⌝
        q : B ≅[ Ty ] ⌜ tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B) ⌝T
        q = B           ≅⟨ ⌜evalT⌝ ⟩
            ⌜ evalT B ⌝T ≅⟨ apd ⌜_⌝T (trfill (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B)) ⟩
            ⌜ tr (λ x → TV T (_ , x)) ⌜evalT⌝ (evalT B) ⌝T ≅∎
    in λ i → Π (p i) (≅-to-≡[] isSetCon q {P = ap (_ ,_) p} i)
  ⌜evalT⌝ {A = A [ σ ]T} =
    A [ σ ]T            ≡⟨ ap (_[ σ ]T) ⌜evalT⌝ ⟩
    ⌜ evalT A ⌝T [ σ ]T  ≡⟨ ⌜[]TV⌝ ⟩
    ⌜ evalT A [ σ ]TV ⌝T ∎
  ⌜evalT⌝ {A = [id]T {A = A} i} j =
    let p = ⌜evalT⌝ {A = A [ id ]T}
        q = ⌜evalT⌝ {A = A}
        r = λ i → [id]T {A = A} i
        s = λ i → ⌜ evalT ([id]T {A = A} i) ⌝T
    in {!isSetFillSquare isSetTy p q r s i!}
  ⌜evalT⌝ {A = [][]T i} = {!!}
  ⌜evalT⌝ {A = U[] i} = {!!}
  ⌜evalT⌝ {A = El[] i} = {!!}
  ⌜evalT⌝ {A = Π[] i} = {!!}
  ⌜evalT⌝ {A = isSetTy p q i j} k =
    {!ouc (isSetPartial isSetTy
                      (λ j → ⌜evalT⌝ {A = p j} k)
                      (λ j → ⌜evalT⌝ {A = q j} k)
                      (λ {(k = i0) → λ i j →
                          isSetTy p q i j;
                          (k = i1) → λ i j →
                          ⌜ isSetTV (λ k → evalT (p k)) (λ k → evalT (q k)) i j ⌝T}))
        i j!}


  evalT⌜⌝ : {S : TSk} {Γ : Con} {A : TV S Γ} →
            evalT ⌜ A ⌝T ≡[ ap (λ x → TV x Γ) (skeleton⌜⌝T {A = A}) ]≡ A
  evalT⌜⌝ {A = U} = refl
  evalT⌜⌝ {A = El u} = refl
  evalT⌜⌝ {A = Π A B} i =
    let p : evalT ⌜ A ⌝T ≡[ ap (λ x → TV x _) (skeleton⌜⌝T {A = A}) ]≡ A
        p = evalT⌜⌝ {A = A}
        q : tr (λ x → TV (skeleton ⌜ B ⌝T) (_ , x)) ⌜evalT⌝ (evalT ⌜ B ⌝T)
            ≅[ (λ (x : TSk × Con) → TV (fst x) (snd x)) ] B
        q = tr (λ x → TV (skeleton ⌜ B ⌝T) (_ , x)) ⌜evalT⌝ (evalT ⌜ B ⌝T)
              ≅⟨ ap (λ x → _ ,, _ , x) (⌜evalT⌝ ⁻¹)
               ∣ trfill (λ x → TV (skeleton ⌜ B ⌝T) (_ , x)) ⌜evalT⌝ (evalT ⌜ B ⌝T) ⁻¹ ⟩
            evalT ⌜ B ⌝T ≅⟨ ap (_,, _) (skeleton⌜⌝T {A = B}) ∣ evalT⌜⌝ ⟩
            B           ≅∎
    in Π (p i) (≅-to-≡[] (isSet× isSetTSk isSetCon) q
                         {P = λ i → (skeleton⌜⌝T {A = B} i) ,, _ , ⌜ evalT⌜⌝ {A = A} i ⌝T} i)


  ⌜⌝T-injective : {S : TSk} {Γ : Con} {A B : TV S Γ} → ⌜ A ⌝T ≡ ⌜ B ⌝T → A ≡ B
  ⌜⌝T-injective {A = A} {B} p = ≅-to-≡ {B = λ x → TV x _} isSetTSk (
    A           ≅⟨ evalT⌜⌝ ⁻¹ ⟩
    evalT ⌜ A ⌝T ≅⟨ apd evalT p ⟩
    evalT ⌜ B ⌝T ≅⟨ evalT⌜⌝ ⟩
    B           ≅∎)
