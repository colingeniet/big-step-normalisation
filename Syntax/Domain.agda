{-# OPTIONS --safe --cubical #-}

module Syntax.Domain where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Library.Pairs.Sets
open import Library.Maybe
open import Library.Maybe.Sets
open import Syntax.Terms
open import Syntax.Lemmas

-- Get the domain and codomain of a function type.
-- Since types have path constructors, this is not completly obvious.
domains : {Γ : Con} → Ty Γ → Maybe (Σ[ A ∈ Ty Γ ] Ty (Γ , A))
domains U = no
domains (El x) = no
domains (Π A B) = yes (A ,, B)
domains (A [ σ ]T) = maybe-lift (λ {(A ,, B) → (A [ σ ]T) ,, (B [ σ ↑ A ]T)}) (domains A)
domains ([id]T {A = A} i) =
  p i
  where p : domains (A [ id ]T) ≡ domains A
        p with domains A
        ...  | no = refl
        ...  | yes (A ,, B) =
               let q : B [ id ↑ A ]T ≅[ Ty ] B
                   q = B [ id ↑ A ]T ≅⟨ ap≅ (B [_]T) ↑id ⟩'
                       B [ id ]T     ≅⟨ [id]T ⟩
                       B             ≅∎
               in ap yes ([id]T ,,≡ ≅-to-≡[] isSetCon q)
domains ([][]T {A = A} {σ} {ν} i) = 
  p i
  where p : domains (A [ σ ∘ ν ]T) ≡ domains (A [ σ ]T [ ν ]T)
        p with domains A
        ...  | no = refl
        ...  | yes (A ,, B) =
               let q : B [ (σ ∘ ν) ↑ A ]T ≅[ Ty ] B [ σ ↑ A ]T [ ν ↑ (A [ σ ]T) ]T
                   q = B [ (σ ∘ ν) ↑ A ]T                ≅⟨ ap≅ (B [_]T) ↑∘↑ ≅⁻¹ ⟩'
                       B [ (σ ↑ A) ∘ (ν ↑ (A [ σ ]T)) ]T ≅⟨ [][]T ⟩
                       B [ σ ↑ A ]T [ ν ↑ (A [ σ ]T) ]T  ≅∎
               in ap yes ([][]T ,,≡ ≅-to-≡[] isSetCon q)
domains (U[] i) = no
domains (El[] i) = no
domains (Π[] {A = A} {B} {σ} i) =
  yes (A [ σ ]T ,, B [ σ ↑ A ]T)
domains (isSetTy p q i j) =
  isSetMaybe (isSetΣ isSetTy isSetTy)
             (λ k → domains (p k)) (λ k → domains (q k)) i j
