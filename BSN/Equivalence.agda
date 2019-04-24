{-# OPTIONS --cubical #-}

module Normalisation.Equivalence where

open import Library.Equality
open import Library.Sets
open import Library.Pairs
open import Syntax.Types.Sets
open import Syntax.Terms
open import Syntax.Terms.Lemmas
open import Normalisation.Variables
open import Normalisation.Variables.Weakening
open import Normalisation.TermLike
open import Normalisation.Values
open import Normalisation.Values.Weakening
open import Normalisation.Values.Lemmas
open import Normalisation.NormalForms
open import Normalisation.NormalForms.Sets
open import Normalisation.Evaluator
open import Normalisation.Eval


infix 10 _~q_ _~qs_ _~_

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


_+~_ : {Γ : Con} {B : Ty} {u v : Val Γ B} → u ~ v → (A : Ty) → u +V A ~ v +V A
_+~_ {B = o} {u} {v} u~v A {Δ} {n} {m} qn qm =
  let u≡u' = V+-++ {Δ = Δ} {B = A} {u = u}
      n' = tr (λ Γ → Nf Γ o) (,++ {Δ = Δ}) n
      n≡n' = trfill (λ Γ → Nf Γ o) (,++ {Δ = Δ}) n
      qn' = (λ i → q (u≡u' i) ⇒ (n≡n' i)) * qn
      v≡v' = V+-++ {Δ = Δ} {B = A} {u = v}
      m' = tr (λ Γ → Nf Γ o) (,++ {Δ = Δ}) m
      m≡m' = trfill (λ Γ → Nf Γ o) (,++ {Δ = Δ}) m
      qm' = (λ i → q (v≡v' i) ⇒ (m≡m' i)) * qm
      n≅m : n ≅⟨ (λ Γ → Nf Γ o) ⟩ m
      n≅m = ≡[]-to-≅ n≡n'
            ∙≅ ≡-to-≅ (u~v qn' qm')
            ∙≅ (≡[]-to-≅ m≡m' ≅⁻¹)
  in ≅-to-≡ isSetCon n≅m
_+~_ {B = B ⟶ C} {f} {g} f~g A {Δ} {u} {v} u~v =
  let f≡f' = V+-++ {Δ = Δ} {B = A} {u = f}
      u' = tr (λ Γ → Val Γ B) (,++ {Δ = Δ}) u
      u≡u' = trfill (λ Γ → Val Γ B) (,++ {Δ = Δ}) u
      g≡g' = V+-++ {Δ = Δ} {B = A} {u = g}
      v' = tr (λ Γ → Val Γ B) (,++ {Δ = Δ}) v
      v≡v' = trfill (λ Γ → Val Γ B) (,++ {Δ = Δ}) v
      u'~v' = (λ i → u≡u' i ~ v≡v' i) * u~v
      fu'~gv' = f~g u'~v'
  in ((λ i → (f≡f' i) $$ (u≡u' i) ~ (g≡g' i) $$ (v≡v' i)) ⁻¹) * fu'~gv'

_++~_ : {Γ : Con} {B : Ty} {u v : Val Γ B} →
        u ~ v → (Δ : Con) → u ++V Δ ~ v ++V Δ
p ++~ ● = p
_++~_ {u = u} {v} u~v (Δ , A) = _+~_ {u = u ++V Δ} {v ++V Δ}
                                     (_++~_ {u = u} {v} u~v Δ) A



~→~q : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → u ~q v
~qs→~ : {Γ : Con} {A : Ty} {u v : Ne Val Γ A} → u ~qs v → neu u ~ neu v

refl~var : {Γ : Con} {A : Ty} {x : Var Γ A} → neu (var x) ~ neu (var x)
refl~var {Γ} {A} {x} = ~qs→~ {u = var x} λ {Δ} {n} {m} qn qm →
  let qn = tr (λ x → qs x ⇒ n) (++var {Δ = Δ} {x = x}) qn
      qm = tr (λ x → qs x ⇒ m) (++var {Δ = Δ} {x = x}) qm
      match : {n : Ne Nf (Γ ++ Δ) A} → qs (var (x ++v Δ)) ⇒ n → n ≡ var (x ++v Δ)
      match = λ {qsvar → refl}
  in match qn ∙ match qm ⁻¹


~→~q {A = o} p = p
~→~q {Γ} {A ⟶ B} {u} {v} u~v = {!!}

~qs→~ {Γ} {o} {u} {v} u~v {Δ} {n} {m} qn qm =
  let qn = tr (λ x → q x ⇒ n) (++VNV {Δ = Δ} {v = u}) qn
      qm = tr (λ x → q x ⇒ m) (++VNV {Δ = Δ} {v = v}) qm  
  in {!!}
