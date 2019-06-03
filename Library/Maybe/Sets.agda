{-# OPTIONS --cubical --safe #-}

module Library.Maybe.Sets where

open import Agda.Primitive
open import Library.Equality
open import Library.Sets
open import Library.Maybe
open import Library.Negation
open import Library.NotEqual

isSetMaybe : ∀ {l} {A : Set l} → isSet A → isSet (Maybe A)
isSetMaybe {A = A} HA {no} {no} p q =
  p             ≡⟨ (λ j i → no≡ (p i) (λ k → p (i ∧ k)) (1- j)) ⟩
  refl {x = no} ≡⟨ (λ j i → no≡ (q i) (λ k → q (i ∧ k)) j) ⟩
  q             ∎
  where no≡ : (z : Maybe A) → no ≡ z → no ≡ z
        no≡ no _ = refl
        no≡ (yes _) p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊥; no → ⊤}) p))
isSetMaybe HA {no} {yes _} p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊥; no → ⊤}) p))
isSetMaybe HA {yes _} {no} p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊤; no → ⊥}) p))
isSetMaybe {A = A} HA {yes x} {yes y} p q =
  let p' : x ≡ y
      p' k = yes-elim (p k) (λ l → p (k ∧ l))
      q' : x ≡ y
      q' k = yes-elim (q k) (λ l → q (k ∧ l))
      p≡yesp' : p ≡ ap yes p'
      p≡yesp' l k = yes-elim≡ (p k) (λ l → p (k ∧ l)) l
      q≡yesq' : q ≡ ap yes q'
      q≡yesq' l k = yes-elim≡ (q k) (λ l → q (k ∧ l)) l
  in p         ≡⟨ p≡yesp' ⟩
     ap yes p' ≡⟨ (λ i j → yes (HA p' q' i j)) ⟩
     ap yes q' ≡⟨ q≡yesq' ⁻¹ ⟩
     q         ∎
  where yes-elim : (z : Maybe A) → yes x ≡ z → A
        yes-elim (yes z) _ = z
        yes-elim no p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊤; no → ⊥}) p))
        yes-elim≡ : (z : Maybe A) (p : yes x ≡ z) → z ≡ yes (yes-elim z p)
        yes-elim≡ (yes z) _ = refl
        yes-elim≡ no p = ⊥-elim (⊤≢⊥ (ap (λ {(yes _) → ⊤; no → ⊥}) p))
