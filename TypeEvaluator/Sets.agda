{-# OPTIONS --cubical #-}

module TypeEvaluator.Sets where

open import Library.Equality
open import Library.Sets
open import Library.Negation
open import Library.NotEqual
open import Library.Pairs
open import Syntax.Terms
open import TypeEvaluator.TypeValue
open import TypeEvaluator.Skeleton


abstract
  isSetTV : {S : TSk} {Γ : Con} → isSet (TV S Γ)

  isSetTV{U} = PropisSet (λ {U U → refl})
  isSetTV {El} {Γ} {El u} {El v} p q =
    let p' : El u ≡ El v
        p' i = El (index (p i))
        q' : El u ≡ El v
        q' i = El (index (q i))
    in p  ≡⟨ (λ j i → Elindex (p i) (1- j)) ⟩
       p' ≡⟨ (λ i j → El (isSetTm (ap index p) (ap index q) i j)) ⟩
       q' ≡⟨ (λ j i → Elindex (q i) j) ⟩
       q  ∎
    where index : TV El Γ → Tm Γ U
          index (El u) = u
          Elindex : (A : TV El Γ) → El (index A) ≡ A
          Elindex (El _) = refl
  isSetTV {Π S T} {Γ} {Π A B} {Π C D} p q =
    let p1 = ap domain p
        p2 = apd codomain p
        q1 = ap domain q
        q2 = apd codomain q
        p' : Π A B ≡ Π C D
        p' i = Π (p1 i) (p2 i)
        q' : Π A B ≡ Π C D
        q' i = Π (q1 i) (q2 i)
        p1≡q1 : p1 ≡ q1
        p1≡q1 = isSetTV p1 q1
        p2' = tr (λ x → B ≡[ (λ i → TV T (Γ , ⌜ x i ⌝T)) ]≡ D) p1≡q1 p2
        p2≡q2 : p2 ≡[ ap (λ x → B ≡[ (λ i → TV T (Γ , ⌜ x i ⌝T)) ]≡ D) p1≡q1 ]≡ q2
        p2≡q2 = trfill (λ x → B ≡[ (λ i → TV T (Γ , ⌜ x i ⌝T)) ]≡ D) p1≡q1 p2
                d∙ isSetDependent {B = TV T} isSetTV p2' q2
        p'≡q' : p' ≡ q'
        p'≡q' i j = Π (p1≡q1 i j) (p2≡q2 i j)
    in p  ≡⟨ (λ j i → domains≡ (p i) (1- j)) ⟩
       p' ≡⟨ p'≡q' ⟩
       q' ≡⟨ (λ j i → domains≡ (q i) j) ⟩
       q  ∎
    where domain : TV (Π S T) Γ → TV S Γ
          domain (Π A B) = A
          codomain : (A : TV (Π S T) Γ) → TV T (Γ , ⌜ domain A ⌝T)
          codomain (Π A B) = B
          domains≡ : (A : TV (Π S T) Γ) → Π (domain A) (codomain A) ≡ A
          domains≡ (Π A B) = refl
