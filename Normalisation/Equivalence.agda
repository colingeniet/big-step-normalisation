{-# OPTIONS --cubical #-}

module Normalisation.Equivalence where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Syntax.Terms
open import Normalisation.TermLike
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Sets
open import Normalisation.Evaluator
open import Normalisation.Eval


infix 10 _~q_ _~qs_ _~_ _~e_

_~q_ : {Γ : Con} {A : Ty} (u v : Val Γ A) → Set
_~q_ {Γ} {A} u v = {Δ : Con} {n m : Nf (Γ ++ Δ) A} →
                   q (u ++V Δ) ⇒ n → q (v ++V Δ) ⇒ m → n ≡ m

_~qs_ : {Γ : Con} {A : Ty} (u v : Ne Val Γ A) → Set
_~qs_ {Γ} {A} u v = {Δ : Con} {n m : Ne Nf (Γ ++ Δ) A} →
                    qs (u ++NV Δ) ⇒ n → qs (v ++NV Δ) ⇒ m → n ≡ m


isProp~q : {Γ : Con} {A : Ty} {u v : Val Γ A} → isProp (u ~q v)
isProp~q x y i qn qm = isSetNf (x qn qm) (y qn qm) i


_~_ : {Γ : Con} {A : Ty} (u v : Val Γ A) → Set
_~_ {A = o} = _~q_
_~_ {Γ} {A ⟶ B} f g =
  {Δ : Con} {u v : Val (Γ ++ Δ) A} → u ~ v → ((f ++V Δ) $$ u) ~ ((g ++V Δ) $$ v)


isProp~ : {Γ : Con} {A : Ty} {u v : Val Γ A} → isProp (u ~ v)
isProp~ {A = o} = isProp~q
isProp~ {Γ} {A ⟶ B} x y i {Δ} u~v = isProp~ {Γ ++ Δ} {B} (x u~v) (y u~v) i

{-
_+~_ : {Γ : Con} {B : Ty} {u v : Val Γ B} → u ~ v → (A : Ty) → u +V A ~ v +V A
_+~_ {B = o} {u} {v} u~v A {Δ} {n} {m} qn qm = ?
-}
