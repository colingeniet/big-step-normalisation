{-# OPTIONS --safe --cubical #-}

module Library.Pairs.Sets where

open import Agda.Primitive
open import Library.Pairs
open import Library.Equality
open import Library.Sets


isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl

isProp⊤l : ∀ {l} → isProp (⊤l {l})
isProp⊤l _ _ = refl


isProp× : ∀ {l m} {A : Set l} {B : Set m} →
          isProp A → isProp B → isProp (A × B)
isProp× HA HB (x ,, y) (z ,, w) i = HA x z i ,, HB y w i

isPropΣ : ∀ {l m} {A : Set l} {B : A → Set m} →
          isProp A → ({a : A} → isProp (B a)) →
          isProp (Σ A B)
isPropΣ {B = B} HA HB (x ,, y) (z ,, w) i =
  let x≡z = HA x z in
  x≡z i ,, isPropDependent {B = B} HB x≡z y w i


isSet× : ∀ {l m} {A : Set l} {B : Set m} →
         isSet A → isSet B → isSet (A × B)
isSet× HA HB p q i j =
  let p1 = λ k → fst (p k)
      p2 = λ k → snd (p k)
      q1 = λ k → fst (q k)
      q2 = λ k → snd (q k)
  in
  HA p1 q1 i j ,, HB p2 q2 i j

isSetΣ : ∀ {l m} {A : Set l} {B : A → Set m} →
         isSet A → ({a : A} → isSet (B a)) →
         isSet (Σ A B)
isSetΣ {B = B} HA HB p q i j =
  let p1 = λ k → fst (p k)
      p2 = λ k → snd (p k)
      q1 = λ k → fst (q k)
      q2 = λ k → snd (q k)
  in
  HA p1 q1 i j ,,
  isSetDependent2 {B = B} HA HB
                  p2 q2 i j
