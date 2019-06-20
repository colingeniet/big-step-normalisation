{-# OPTIONS --cubical #-}

module Syntax.Equivalence where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Library.Maybe
open import Library.Maybe.Sets
open import Syntax.Terms
open import Syntax.Lemmas
open import Syntax.Sets


{- This module defines three important lemmas:
   - For any equivalence of terms, the underlying types and contexts are equal.
   - One can extract the domain and codomain of a function type.
   - The congruence constructors for types can be made heterogeneous.

   While the relation between the three is not obvious, the dependencies are
   actually quite complicated, which is why everything is in the same module.
-}


-- Obtaining an equality of domains from an equivalence of substitutions is quite easy.
≋C₁ : {Γ Δ Θ Ψ : Con} {σ : Tms Γ Θ} {ν : Tms Δ Ψ} → σ ≋ ν → Γ ≡ Δ
≋C₁ refl≋ = refl
≋C₁ (p ≋⁻¹) = ≋C₁ p ⁻¹
≋C₁ (p ∙≋ q) = ≋C₁ p ∙ ≋C₁ q
≋C₁ (p ∘≋ q) = ≋C₁ q
≋C₁ (p ,≋ q) = ≋C₁ p
≋C₁ (π₁≋ p) = ≋C₁ p
≋C₁ id∘ = refl
≋C₁ ∘id = refl
≋C₁ ∘∘ = refl
≋C₁ εη = refl
≋C₁ π₁β = refl
≋C₁ πη = refl
≋C₁ ,∘ = refl

-- This allows to define the heterogeneous version of the substitution congruence
-- constructor, which is a crucial lemma.
_[_]≈d : {Γ Δ Θ Ψ : Con} {A : Ty Δ} {B : Ty Ψ} {σ : Tms Γ Δ} {ν : Tms Θ Ψ} →
         A ≅[ Ty ] B → σ ≋ ν → A [ σ ] ≅[ Ty ] B [ ν ]
_[_]≈d {Γ} {Δ} {Θ} {Ψ} {A} {B} {σ} {ν} p q =
  let P : Γ ≡ Θ
      P = ≋C₁ q
      Q : Δ ≡ Ψ
      Q = fst p
      σ' = (λ i → Tms (P i) (Q i)) * σ
      q' : σ' ≋ ν
      q' = σ' ≋⟨ (λ i → Tms (P i) (Q i)) *fill σ ⁻¹ ⟩'
           σ ≋⟨ q ⟩
           ν ≋∎
  in A [ σ ]  ≅⟨ (λ i → (snd p i) [ ((λ i → Tms (P i) (Q i)) *fill σ) i ]) ⟩
     B [ σ' ] ≅⟨ B [ q' ]≈T ⟩
     B [ ν ]  ≅∎


-- The previous lemma is usefull to obtain the codomain of function types.
domains : {Γ : Con} → Ty Γ → Maybe (Σ[ A ∈ Ty Γ ] Ty (Γ , A))
domains U = no
domains (El x) = no
domains (Π A B) = yes (A ,, B)
domains (A [ σ ]) = maybe-lift (λ {(A ,, B) → (A [ σ ]) ,, (B [ σ ↑ A ])}) (domains A)
domains ([id]T {A = A} i) =
  p i
  where p : domains (A [ id ]) ≡ domains A
        p with domains A
        ...  | no = refl
        ...  | yes (A ,, B) =
               let q : B [ id ↑ A ] ≅[ Ty ] B
                   q = B [ id ↑ A ] ≅⟨ refl≅ [ ↑id ]≈d ⟩'
                       B [ id ]     ≅⟨ [id]T ⟩
                       B            ≅∎
               in ap yes ([id]T ,,≡ ≅-to-≡[] isSetCon q)
domains ([][]T {A = A} {σ} {ν} i) = 
  p i
  where p : domains (A [ σ ∘ ν ]) ≡ domains (A [ σ ] [ ν ])
        p with domains A
        ...  | no = refl
        ...  | yes (A ,, B) =
               let q : B [ (σ ∘ ν) ↑ A ] ≅[ Ty ] B [ σ ↑ A ] [ ν ↑ (A [ σ ]) ]
                   q = B [ (σ ∘ ν) ↑ A ]               ≅⟨ refl≅ [ ↑∘↑ ≋⁻¹ ]≈d ⟩'
                       B [ (σ ↑ A) ∘ (ν ↑ (A [ σ ])) ] ≅⟨ [][]T ⟩
                       B [ σ ↑ A ] [ ν ↑ (A [ σ ]) ]   ≅∎
               in ap yes ([][]T ,,≡ ≅-to-≡[] isSetCon q)
domains (U[] i) = no
domains (El[] i) = no
domains (Π[] {A = A} {B} {σ} i) =
  yes (A [ σ ] ,, B [ σ ↑ A ])
domains (El≈ p i) = no
domains (_[_]≈T A {σ = σ} {ν} p i) =
  maybe-lift
    (λ {(A ,, B) →
        let P = A [ p ]≈T
            q : wk {A = A [ σ ]} ≋ wk {A = A [ ν ]}
            q = wk {A = A [ σ ]} ≋⟨ (λ i → wk {A = P i}) ⟩'
                wk {A = A [ ν ]} ≋∎
            r : tr (Tm _) ([][]T ⁻¹) (vz {A = A [ σ ]})
                ≈ tr (Tm _) ([][]T ⁻¹) (vz {A = A [ ν ]})
            r = tr (Tm _) ([][]T ⁻¹) vz ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⁻¹ ⟩'
                vz {A = A [ σ ]}        ≈⟨ (λ i → vz {A = P i}) ⟩'
                vz {A = A [ ν ]}        ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⟩'
                tr (Tm _) ([][]T ⁻¹) vz ≈∎
            s : σ ↑ A ≋ ν ↑ A
            s = (p ∘≋ q) ,≋ r
            Q : B [ σ ↑ A ] ≅[ Ty ] B [ ν ↑ A ]
            Q = refl≅ [ s ]≈d
        in P i ,, ≅-to-≡[] isSetCon Q {P = ap (_ ,_) P} i})
    (domains A)
domains (isSetTy p q i j) =
  isSetMaybe (isSetΣ isSetTy isSetTy)
             (λ k → domains (p k)) (λ k → domains (q k)) i j

{-
-- This allows to define the remaining underlying paths for equivalences.
≋C₂ : {Γ Δ Θ Ψ : Con} {σ : Tms Γ Θ} {ν : Tms Δ Ψ} → σ ≋ ν → Θ ≡ Ψ
≈C : {Γ Δ : Con} {A : Ty Γ} {B : Ty Δ} {u : Tm Γ A} {v : Tm Δ B} →
     u ≈ v → Γ ≡ Δ
≈T : {Γ Δ : Con} {A : Ty Γ} {B : Ty Δ} {u : Tm Γ A} {v : Tm Δ B} →
     (p : u ≈ v) → A ≅[ Ty ] B

≋C₂ refl≋ = refl
≋C₂ (p ≋⁻¹) = ≋C₂ p ⁻¹
≋C₂ (p ∙≋ q) = ≋C₂ p ∙ ≋C₂ q
≋C₂ (p ∘≋ q) = ≋C₂ p
≋C₂ (_,≋_ {Γ} {Δ} {Θ} {Ψ} {A} {B} {σ} {ν} {u} {v} p q) =
  let r : Γ ≡ Θ
      r = ≋C₁ p
      s : Δ ≡ Ψ
      s = ≋C₂ p
      t : A ≡[ ap Ty s ]≡ B
      t = {!≈T q!}
  in {!!}
≋C₂ (π₁≋ p) = yes-injective (ap (λ {● → no; (Γ , _) → yes Γ}) (≋C₂ p))
≋C₂ id∘ = refl
≋C₂ ∘id = refl
≋C₂ ∘∘ = refl
≋C₂ εη = refl
≋C₂ π₁β = refl
≋C₂ πη = refl
≋C₂ ,∘ = refl

≈C refl≈ = refl
≈C (p ≈⁻¹) = ≈C p ⁻¹
≈C (p ∙≈ q) = ≈C p ∙ ≈C q
≈C (_ [ p ]≈) = ≋C₁ p
≈C (π₂≈ p) = ≋C₁ p
≈C (lam≈ p) = yes-injective (ap (λ {● → no; (Γ , _) → yes Γ}) (≈C p))
≈C (app≈ {Γ} {Δ} {A} {B} {C} {D} {u} {v} p) =
  let q : Γ ≡ Δ
      q = ≈C p
      r : Π A B ≡[ ap Ty q ]≡ Π C D
      r = ≅-to-≡[] isSetCon (≈T p)
      s : A ≡[ ap Ty q ]≡ C
      s = apd fst (yes-injective-dependent (apd domains r))
  in λ i → q i , s i
≈C π₂β = refl
≈C β = refl
≈C η = refl
≈C lam[] = refl

≈T refl≈ = refl≅
≈T (p ≈⁻¹) = ≈T p ≅⁻¹
≈T (p ∙≈ q) = ≈T p ∙≅ ≈T q
≈T (p [ q ]≈) = (≈T p) [ q ]≈d
≈T (π₂≈ {Γ} {Δ} {Θ} {Ψ} {A} {B} {σ} {ν} p) =
  let q : A ≅[ Ty ] B
      q = {!!}                    
  in q [ π₁≋ p ]≈d
≈T (lam≈ p) = {!!}
≈T (app≈ p) = {!!}
≈T π₂β = ≡-to-≅ (_ [ π₁β ]≈T)
≈T β = refl≅
≈T η = refl≅
≈T lam[] = ≡-to-≅ Π[]


-- finally, the remaining dependent congruence constructor.
El≈d : {Γ Δ : Con} {u : Tm Γ U} {v : Tm Δ U} → u ≈ v → El u ≅[ Ty ] El v
El≈d {Γ} {Δ} {u} {v} p =
  let P : Γ ≡ Δ
      P = ≈C p
      u' = tr (λ Γ → Tm Γ U) P u
      p' : u' ≈ v
      p' = u' ≈⟨ trfill (λ Γ → Tm Γ U) P u ⁻¹ ⟩'
           u  ≈⟨ p ⟩
           v  ≈∎
  in El u  ≅⟨ apd El (trfill (λ Γ → Tm Γ U) P u) ⟩
     El u' ≅⟨ El≈ p' ⟩
     El v  ≅∎
-}

abstract
  -- Additional congruence for equivalences.
  _↑≋_ : {Γ Δ Θ Ψ : Con} {σ : Tms Γ Δ} {ν : Tms Θ Ψ} {A : Ty Δ} {B : Ty Ψ} →
         σ ≋ ν → A ≅[ Ty ] B → σ ↑ A ≋ ν ↑ B
  _↑≋_ {σ = σ} {ν} {A} {B} p q =
    let r : A [ σ ] ≅[ Ty ] B [ ν ]
        r = q [ p ]≈d
        s : wk {A = A [ σ ]} ≋ wk {A = B [ ν ]}
        s = wk {A = A [ σ ]} ≋⟨ apd (λ A → wk {A = A}) (snd r) ⟩'
            wk {A = B [ ν ]} ≋∎
        t : tr (Tm _) ([][]T ⁻¹) (vz {A = A [ σ ]}) ≈ tr (Tm _) ([][]T ⁻¹) (vz {A = B [ ν ]})
        t = tr (Tm _) ([][]T ⁻¹) (vz {A = A [ σ ]}) ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⁻¹ ⟩'
            vz {A = A [ σ ]}                        ≈⟨ apd (λ A → vz {A = A}) (snd r) ⟩'
            vz {A = B [ ν ]}                        ≈⟨ trfill (Tm _) ([][]T ⁻¹) vz ⟩'
            tr (Tm _) ([][]T ⁻¹) (vz {A = B [ ν ]}) ≈∎
    in (p ∘≋ s) ,≋ t
