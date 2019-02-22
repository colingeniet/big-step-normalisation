{-# OPTIONS --without-K --allow-unsolved-meta #-}

{-
  Soundness theorem: equivalent terms normalise to the same normal form.

  The proof follows the same general scheme as the proof of termination,
  only the strong computability unary predicate is replaced by a binary
  relation on values.
-}

module Normalisation.Soundness where

open import Library.Equality
open import Library.Pairs
open import Syntax.Terms
open import Syntax.Equivalence
open import Syntax.Lemmas
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Termination
open import Normalisation.Determinism


{-
  Equivalence of values is defined similarly to strong computability:
  it is in some sense a stronger requirement than equality of images by quote,
  which will allow the induction to go through.
-}

infix 15 _~_
_~_ : {Γ : Con} {A : Ty} → Val Γ A → Val Γ A → Set
-- A the base type, equivalence is equality of quote.
_~_ {A = o} u v = (q u) ≡ (q v)
-- For function types, equivalence must be preserved by application.
_~_ {Γ = Γ} {A = A ⟶ B} f g =
  {Δ : Con} {u v : Val (Γ ++ Δ) A} → u ~ v →
  ((f ++V Δ) $$ u) ~ ((g ++V Δ) $$ v)


-- Equivalence is stable by weakening.
_+~_ : {Γ : Con} {B : Ty} {u v : Val Γ B} → u ~ v → (A : Ty) →
       (u +V A) ~ (v +V A)

_+~_ {B = o} {u} {v} qu≡qv A =
  qwk' {v = u}
  ∙ ap (λ x → x +N A) qu≡qv
  ∙ qwk' {v = v} ⁻¹
  where qwk' : {Γ : Con} {A B : Ty} {v : Val Γ B} → q (v +V A) ≡ (q v) +N A
        qwk' {A = A} {v} = q-deterministic q-is-q (qwk q-is-q A)

_+~_ {B = B ⟶ C} {f} {g} f~g A {Δ} {u} {v} u~v =
  let u' = tr (λ Γ → Val Γ B) ,++ u in
  let u≡u' = trfill (λ Γ → Val Γ B) ,++ u in
  let v' = tr (λ Γ → Val Γ B) ,++ v in
  let v≡v' = trfill (λ Γ → Val Γ B) ,++ v in
  {!!}


_++~_ : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → (Δ : Con) →
        (u ++V Δ) ~ (v ++V Δ)
p ++~ ● = p
p ++~ (Δ , A) = (p ++~ Δ) +~ A


-- Equivalence is symmetric and transitive (reflexivity is not obvious).
infix 8 _~⁻¹
_~⁻¹ : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → v ~ u
_~⁻¹ {A = o} = _⁻¹
_~⁻¹ {A = A ⟶ B} pf pu = pf (pu ~⁻¹) ~⁻¹

infixr 6 _∙~_
_∙~_ : {Γ : Con} {A : Ty} {u v w : Val Γ A} → u ~ v → v ~ w → u ~ w
_∙~_ {A = o} = _∙_
_∙~_ {A = A ⟶ B} p1 p2 pu =
  -- Reflexivity holds for a value in relation with anything using symmetry
  -- and transitivity (induction hypothesis). This is just what we need here.
  p1 pu ∙~ p2 (pu ~⁻¹ ∙~ pu)


{-
  Main lemma:
  Equivalence implies equality of quotes, and the converse holds for 
  neutral values.
-}
~q : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → (q u) ≡ (q v)
q~ : {Γ : Con} {A : Ty} {u v : Ne Val Γ A} → (qs u) ≡ (qs v) → vneu u ~ vneu v

-- The converse allows to prove reflexivity on variables.
refl~var : {Γ : Con} {A : Ty} {x : Var Γ A} → vneu (var x) ~ vneu (var x)
refl~var {x = x} = q~ refl


~q {A = o} p = p
-- The main direction is simple by applying the functions to vz, using the
-- previous lemma.
~q {Γ = Γ} {A = A ⟶ B} {u = f} {v = g} p =
  q⟶≡ {f = f} ∙ ap nlam (~q (p refl~var)) ∙ q⟶≡ {f = g} ⁻¹

q~ {A = o} p = qo≡ ∙ ap nneu p ∙ qo≡ ⁻¹
-- For functions, since we consider neutral values, application and quote
-- are simple. The only problem is to deal with the various weakenings and
-- transports.
q~ {A = A ⟶ B} {u = f} {v = g} qf≡qg {Δ = Δ} {u = u} {v = v} u~v =
  let fu≡ = ap (λ f → f $$ u) (++VNV {Δ = Δ} {v = f}) in
  let gv≡ = ap (λ g → g $$ v) (++VNV {Δ = Δ} {v = g}) in
  let qu≡qv = ~q u~v in
  ((ap (λ u → u ~ _) fu≡ ⁻¹)
  ∙ (ap (λ u → _ ~ u) gv≡ ⁻¹))
  * q~ (ap (λ n → app n _)
           (qswks' f Δ
           ∙ ap (λ n → n ++NN Δ) qf≡qg
           ∙ qswks' g Δ ⁻¹)
       ∙ ap (λ n → app _ n) qu≡qv)
  where qswks' : {Γ : Con} {A : Ty} (u : Ne Val Γ A) (Δ : Con) →
                 qs (u ++NV Δ) ≡ (qs u) ++NN Δ
        qswks' u Δ = qs-deterministic qs-is-qs (qswks qs-is-qs Δ)



-- Extension of equivalence to environments.
_~E_ : {Γ Δ : Con} → Env Γ Δ → Env Γ Δ → Set
_~E_ {Δ = ●} _ _ = ⊤
_~E_ {Δ = Δ , A} (σ , u) (ν , v) = σ ~E ν  ∧  u ~ v

-- Symmetry.
infix 8 _~E⁻¹
_~E⁻¹ : {Γ Δ : Con} {σ ν : Env Γ Δ} → σ ~E ν → ν ~E σ
_~E⁻¹ {Δ = ●} tt = tt
_~E⁻¹ {Δ = Δ , A} {_ , _} {_ , _} (p ,, q) = p ~E⁻¹ ,, q ~⁻¹

-- Transitivity.
infixr 6 _∙~E_
_∙~E_ : {Γ Δ : Con} {σ ν ρ : Env Γ Δ} → σ ~E ν → ν ~E ρ → σ ~E ρ
_∙~E_ {Δ = ●} tt tt = tt
_∙~E_ {Δ = Δ , A} {_ , _} {_ , _} {_ , _} (p1 ,, q1) (p2 ,, q2) =
  p1 ∙~E p2 ,, q1 ∙~ q2


-- Projections.
π₁~E : {Γ Δ : Con} {A : Ty} {σ ν : Env Γ (Δ , A)} →
       σ ~E ν → (π₁list σ) ~E (π₁list ν)
π₁~E {σ = _ , _} {ν = _ , _} = fst

π₂~E : {Γ Δ : Con} {A : Ty} {σ ν : Env Γ (Δ , A)} →
       σ ~E ν → (π₂list σ) ~ (π₂list ν)
π₂~E {σ = _ , _} {ν = _ , _} = snd

-- Weakenings.
_+~E_ : {Γ Δ : Con} {σ ν : Env Γ Δ} → σ ~E ν →
        (A : Ty) → (σ +E A) ~E (ν +E A)
_+~E_ {Δ = ●} tt A = tt
_+~E_ {Δ = _ , _} {_ , _} {_ , _} (σ~ν ,, u~v) A = σ~ν +~E A ,, u~v +~ A

_++~E_ : {Γ Δ : Con} {σ ν : Env Γ Δ} → σ ~E ν →
         (Δ : Con) → (σ ++E Δ) ~E (ν ++E Δ)
p ++~E ● = p
p ++~E (Δ , A) = (p ++~E Δ) +~E A

-- Reflexivity holds for the identity environment.
refl~id : {Γ : Con} → (idenv {Γ}) ~E idenv
refl~id {●} = tt
refl~id {Γ , A} = refl~id +~E A ,, refl~var


{-
  Lemma:
  Evaluation of a term in equivalent environments gives equivalent results.
-}
eval≡~ : {Γ Δ : Con} {A : Ty} (u : Tm Δ A) {ρ δ : Env Γ Δ} → ρ ~E δ →
         eval u ρ ~ eval u δ

evals≡~ : {Γ Δ Θ : Con} (σ : Tms Δ Θ) {ρ δ : Env Γ Δ} → ρ ~E δ →
          evals σ ρ ~E evals σ δ

eval≡~ (u [ σ ]) ρ~δ =
  (ap (λ x → x ~ _) (eval[]≡ {u = u} {σ = σ}) ⁻¹
  ∙ ap (λ x → _ ~ x) (eval[]≡ {u = u} {σ = σ}) ⁻¹)

  * eval≡~ u (evals≡~ σ ρ~δ)
eval≡~ (π₂ σ) ρ~δ = π₂~E (evals≡~ σ ρ~δ)
eval≡~ {A = A ⟶ B} (lam u) ρ~δ {Δ = Θ} {v} {w} v~w =
  (ap (λ u → u $$ v ~ _) ([]++V {Θ = Θ})
  ∙ ap (λ u → _ ~ u $$ w) ([]++V {Θ = Θ}))
  * eval≡~ u (ρ~δ ++~E Θ ,, v~w)
eval≡~ (app f) {ρ = ρ} {δ = δ} ρ~δ =
  (ap (λ x → x ~ _) (evalapp≡ {f = f} {ρ = ρ}) ⁻¹
  ∙ ap (λ x → _ ~ x) (evalapp≡ {f = f} {ρ = δ}) ⁻¹)
  * eval≡~ f (π₁~E ρ~δ) (π₂~E ρ~δ)

evals≡~ id ρ~δ = ρ~δ
evals≡~ (σ ∘ ν) ρ~δ =
  (ap (λ x → x ~E _) (evals∘≡ {σ = σ} {ν = ν}) ⁻¹
  ∙ ap (λ x → _ ~E x) (evals∘≡ {σ = σ} {ν = ν}) ⁻¹)
  * evals≡~ σ (evals≡~ ν ρ~δ)
evals≡~ ε _ = tt
evals≡~ (σ , u) ρ~δ = evals≡~ σ ρ~δ ,, eval≡~ u ρ~δ
evals≡~ (π₁ σ) ρ~δ = π₁~E (evals≡~ σ ρ~δ)


{-
  Main theorem :
  βησ-equivalent terms in equivalent environments evaluate to equivalent values.
-}
eval≈~ : {Γ Δ : Con} {A : Ty} {u v : Tm Δ A} {ρ δ : Env Γ Δ} →
         u ≈ v → ρ ~E δ → eval u ρ ~ eval v δ

evals≋~ : {Γ Δ Θ : Con} {σ ν : Tms Δ Θ} {ρ δ : Env Γ Δ} →
          σ ≋ ν → ρ ~E δ → evals σ ρ ~E evals ν δ

eval≈~ (refl≈ {u = u}) ρ~δ = eval≡~ u ρ~δ
eval≈~ (p ≈⁻¹) ρ~δ = eval≈~ p (ρ~δ ~E⁻¹) ~⁻¹
eval≈~ (p ∙≈ q) ρ~δ = eval≈~ p ρ~δ ∙~ eval≈~ q (ρ~δ ~E⁻¹ ∙~E ρ~δ)

eval≈~ (_[_]≈ {u = u} {v} {σ} {ν} p q) ρ~δ =
  (ap (λ x → x ~ _) (eval[]≡ {u = u} {σ = σ}) ⁻¹
  ∙ ap (λ x → _ ~ x) (eval[]≡ {u = v} {σ = ν}) ⁻¹)
  * eval≈~ p (evals≋~ q ρ~δ)
eval≈~ (π₂≈ p) ρ~δ = π₂~E (evals≋~ p ρ~δ)
eval≈~ (lam≈ p) ρ~δ {Δ} {u} {v} u~v = 
  (ap (λ f → f $$ u ~ _) ([]++V {Θ = Δ})
  ∙ ap (λ f → _ ~ f $$ v) ([]++V {Θ = Δ}))
  * eval≈~ p (ρ~δ ++~E Δ ,, u~v)
eval≈~ {ρ = ρ} {δ} (app≈ {u = u} {v} p) ρ~δ =
  (ap (λ x → x ~ _) (evalapp≡ {f = u} {ρ = ρ}) ⁻¹
  ∙ ap (λ x → _ ~ x) (evalapp≡ {f = v} {ρ = δ}) ⁻¹)
  * eval≈~ p (π₁~E ρ~δ) (π₂~E ρ~δ)

eval≈~ (π₂β {u = u}) ρ~δ = eval≡~ u ρ~δ
eval≈~ {ρ = ρ} (β {u = u}) ρ~δ =
  tr (λ u → u ~ _)
     (ap (λ ρ → eval u ρ) πηlist ⁻¹
     ∙ evalapp≡ {f = lam u} {ρ = ρ} ⁻¹)
     (eval≡~ u ρ~δ)
eval≈~ {ρ = ρ} {δ} (η {f = f}) ρ~δ {Δ} {u} {v} u~v =
  tr (λ x → x ~ _)
     (ap (λ x → x $$ u) (evalwks' f ρ Δ) ⁻¹
     ∙ evalapp≡ {f = f} {ρ = ρ ++E Δ , u} ⁻¹
     ∙ ap (λ x → x $$ u) ([]++V {Θ = Δ}))
     (eval≡~ f ρ~δ u~v)
  where evalwks' : {Γ Δ : Con} {A : Ty} (u : Tm Δ A) (ρ : Env Γ Δ) (Θ : Con) →
                   eval u (ρ ++E Θ) ≡ (eval u ρ) ++V Θ
        evalwks' u ρ Θ = eval-deterministic (eval-is-eval {u = u} {ρ = ρ ++E Θ})
                                            (evalwks eval-is-eval Θ)

eval≈~ {ρ = ρ} {δ} (lam[] {A = A} {u = u} {σ = σ}) ρ~δ {Δ} {v} {w} v~w =
  (ap (λ x → eval u (x , v) ~ _)
      (evalswks' σ ρ Δ)
  ∙ ap (λ x → x $$ v ~ _)
       ([]++V {Θ = Δ})
  ∙ ap (λ x → (x ++V Δ) $$ v ~ eval u (evals σ (δ ++E Δ) , w))
       (eval[]≡ {u = lam u} {σ = σ}) ⁻¹
  ∙ ap (λ x → _ ~ eval u (x , _))
       (evals∘≡ {σ = σ} {ν = wk}) ⁻¹
  ∙ ap (λ x → _ ~ x)
       (eval[]≡ {u = u} {σ = σ ↑ A}) ⁻¹
  ∙ ap (λ x → _ ~ x $$ w)
       ([]++V {Θ = Δ}))
  * eval≡~ u (evals≡~ σ (ρ~δ ++~E Δ) ,, v~w)
  where evalswks' : {Γ Δ Θ : Con} (σ : Tms Δ Θ) (ρ : Env Γ Δ) (Θ : Con) →
                   evals σ (ρ ++E Θ) ≡ (evals σ ρ) ++E Θ
        evalswks' σ ρ Θ =
          evals-deterministic (evals-is-evals {σ = σ} {ρ = ρ ++E Θ})
                              (evalswks evals-is-evals Θ)


evals≋~ (refl≋ {σ = σ}) ρ~δ = evals≡~ σ ρ~δ
evals≋~ (p ≋⁻¹) ρ~δ = evals≋~ p (ρ~δ ~E⁻¹) ~E⁻¹
evals≋~ (p ∙≋ q) ρ~δ = evals≋~ p ρ~δ ∙~E evals≋~ q (ρ~δ ~E⁻¹ ∙~E ρ~δ)

evals≋~ (_∘≋_ {σ₁ = σ₁} {σ₂} {ν₁} {ν₂} p q) ρ~δ =
  (ap (λ x → x ~E _) (evals∘≡ {σ = σ₁} {ν = ν₁}) ⁻¹
  ∙ ap (λ x → _ ~E x) (evals∘≡ {σ = σ₂} {ν = ν₂}) ⁻¹)
  * evals≋~ p (evals≋~ q ρ~δ)
evals≋~ (p ,≋ q) ρ~δ = evals≋~ p ρ~δ ,, eval≈~ q ρ~δ
evals≋~ (π₁≋ p) ρ~δ = π₁~E (evals≋~ p ρ~δ)

evals≋~ (id∘ {σ = σ}) ρ~δ = evals≡~ σ ρ~δ
evals≋~ (∘id {σ = σ}) ρ~δ = evals≡~ σ ρ~δ
evals≋~ (∘∘ {σ = σ} {ν} {α}) ρ~δ =
  (ap (λ x → x ~E _) (evals∘≡ {σ = σ ∘ ν} {ν = α}
                     ∙ evals∘≡ {σ = σ} {ν = ν}) ⁻¹
  ∙ ap (λ x → _ ~E x) (evals∘≡ {σ = σ} {ν = ν ∘ α}
                     ∙ ap (λ x → evals σ x) (evals∘≡ {σ = ν} {ν = α})) ⁻¹)
  * evals≡~ σ (evals≡~ ν (evals≡~ α ρ~δ))
evals≋~ εη ρ~δ = tt
evals≋~ (π₁β {σ = σ}) ρ~δ = evals≡~ σ ρ~δ
evals≋~ {ρ = ρ} (πη {σ = σ}) ρ~δ =
  tr (λ x → x ~E _)
     (πηlist {ρ = evals σ ρ} ⁻¹)
     (evals≡~ σ ρ~δ)
evals≋~ (,∘ {σ = σ} {ν = ν} {u = u}) ρ~δ =
  (ap (λ x → x ~E _) (evals∘≡ {σ = σ} {ν = ν} ⁻¹)
  ∙ ap (λ x → _ ~E x) (evals∘≡ {σ = σ} {ν = ν} ⁻¹))
  * evals≡~ σ (evals≡~ ν ρ~δ) ,,
  (ap (λ x → x ~ _) (eval[]≡ {u = u} {σ = ν} ⁻¹)
  ∙ ap (λ x → _ ~ x) (eval[]≡ {u = u} {σ = ν} ⁻¹))
  * eval≡~ u (evals≡~ ν ρ~δ)



-- Soundness of normalisation follows easily.
soundness : {Γ : Con} {A : Ty} {u v : Tm Γ A} → u ≈ v → nf u ≡ nf v
soundness {u = u} {v} p = ~q (eval≈~ p refl~id)
