{-# OPTIONS --cubical --safe #-}

module NormalForm.Presheaf where

open import Library.Equality
open import Syntax.Types
open import Weakening.Presheaf
open import Weakening.Presheaf.List
open import Weakening.Variable
open import Syntax.Terms.Presheaf
open import NormalForm.NormalForm
open import NormalForm.Weakening
open import NormalForm.Sets


Nf' : Ty → Pshw
(Nf' A) $o Γ = Nf Γ A
isSetapply (Nf' A) = isSetNf
n +⟨ Nf' A ⟩ σ = n +N σ
+id (Nf' A) = +Nid
+∘ (Nf' A) {x = n} {σ} {ν} = +N∘ {n = n} {σ} {ν}

embNf : {A : Ty} → Natw (Nf' A) (Tm' A)
act embNf _ n = ⌜ n ⌝N
nat embNf {x = n} = ⌜⌝+N {n = n}


NN' : Ty → Pshw
(NN' A) $o Γ = NN Γ A
isSetapply (NN' A) = isSetNN
n +⟨ NN' A ⟩ σ = n +NN σ
+id (NN' A) = +NNid
+∘ (NN' A) {x = n} {σ} {ν} = +NN∘ {n = n} {σ} {ν}

embNN : {A : Ty} → Natw (NN' A) (Tm' A)
act embNN _ n = ⌜ n ⌝NN
nat embNN {x = n} = ⌜⌝+NN {n = n}


Nfs' : Con → Pshw
Nfs' = listp Nf'

embNfs : {Γ : Con} → Natw (Nfs' Γ) (Tms' Γ)
embNfs = mapnt embNf

NNs' : Con → Pshw
NNs' = listp NN'

embNNs : {Γ : Con} → Natw (NNs' Γ) (Tms' Γ)
embNNs = mapnt embNN
