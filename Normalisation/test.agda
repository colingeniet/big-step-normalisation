{-# OPTIONS --cubical #-}

module Normalisation.test where

open import Syntax.Terms
open import Syntax.Weakening
open import Normalisation.Variables
open import Normalisation.TermLike
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Weakening

NE = list Nf

_+NE_ : {Γ Δ Θ : Con} → NE Δ Θ → Wk Γ Δ → NE Γ Θ
ε +NE σ = ε
(ρ , n) +NE σ = ρ +NE σ , n +N σ


nenf : {Γ : Con} {A : Ty} → Ne Nf Γ A → Nf Γ A
nenf {A = o} n = neu n
nenf {A = A ⟶ B} n = lam (nenf (app (n +NN (drop A idw))
                                    (nenf (var z))))

idNE : {Γ : Con} → NE Γ Γ
idNE {●} = ε
idNE {Γ , A} = idNE +NE (drop A idw) , nenf (var z)


_-_ : (Γ : Con) {A : Ty} → Var Γ A → Con
(Γ , A) - z = Γ
(Γ , A) - (s x) = (Γ - x) , A


_[_/_]N : {Γ : Con} {A B : Ty} → Nf Γ B → Nf Γ A → (x : Var Γ A) → Nf (Γ - x) B
_[_/_]NN : {Γ : Con} {A B : Ty} → Ne Nf Γ B → Nf Γ A → (x : Var Γ A) → Nf (Γ - x) B
_$$N_ : {Γ : Con} {A B : Ty} → Nf Γ (A ⟶ B) → Nf Γ A → Nf Γ B

(lam n) [ m / x ]N = lam (n [ m +N (drop _ idw) / s x ]N)
(neu n) [ m / x ]N = n [ m / x ]NN
(app f n) [ m / x ]NN = (f [ m / x ]NN) $$N (n [ m / x ]N)

(lam n) $$N m = n [ m +N (drop _ idw) / z ]N
