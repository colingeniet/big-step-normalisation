module Normalisation.Soundness where

open import Equality
open import Syntax
open import Syntax.Equivalence
open import Normalisation.NormalForms
open import Normalisation.Evaluator
open import Normalisation.Termination
open import Normalisation.Determinism

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)


-- Equality of images by quote.
-- It would be possible to use the functions q and qs (instead of the relations),
-- but those are actually more annoying to work with.
_q≡_ : {Γ : Con} {A : Ty} → Val Γ A → Val Γ A → Set
_q≡_ {Γ = Γ} {A = A} u v = Σ (Nf Γ A) λ n →
                           Σ (q u ⇒ n) λ _ →
                             q v ⇒ n

_qs≡_ : {Γ : Con} {A : Ty} → Ne Val Γ A → Ne Val Γ A → Set
_qs≡_ {Γ = Γ} {A = A} u v = Σ (Ne Nf Γ A) λ n →
                            Σ (qs u ⇒ n) λ _ →
                              qs v ⇒ n


-- Equivalence of values is defined similarely to strong computability.
infix 15 _~_
_~_ : {Γ : Con} {A : Ty} → Val Γ A → Val Γ A → Set
-- A the base type, it is equality of quote.
_~_ {Γ = Γ} {A = o} u v = u q≡ v
-- For function types, equivalence must be preserved by application.
_~_ {Γ = Γ} {A = A ⟶ B} f g =
  {Δ : Con} {u v : Val (Γ ++ Δ) A} → u ~ v →
  Σ (Val (Γ ++ Δ) B) λ fu →
  Σ (Val (Γ ++ Δ) B) λ gv →
  Σ ((f ++V Δ) $ u ⇒ fu) λ _ →
  Σ ((g ++V Δ) $ v ⇒ gv) λ _ →
    fu ~ gv


-- Equivalence is stable by weakening.
postulate
  _+~_ : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → (B : Ty) → (u +V B) ~ (v +V B)

_++~_ : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → (Δ : Con) → (u ++V Δ) ~ (v ++V Δ)
p ++~ ● = p
p ++~ (Δ , A) = (p ++~ Δ) +~ A


-- Equivalence is symmetric and transitive (it is not obvious that it is reflexive).
infix 8 _~⁻¹
_~⁻¹ : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → v ~ u
_~⁻¹ {A = o} (n ,, qu ,, qv) = (n ,, qv ,, qu)
_~⁻¹ {A = A ⟶ B} pf pu =
  let fu ,, gv ,, $fu ,, $gv ,, fu~gv = pf (pu ~⁻¹) in
  gv ,, fu ,, $gv ,, $fu ,, fu~gv ~⁻¹

infixr 6 _∙~_
_∙~_ : {Γ : Con} {A : Ty} {u v w : Val Γ A} → u ~ v → v ~ w → u ~ w
_∙~_ {A = o} (n ,, qu ,, qv) (n' ,, qv' ,, qw) =
  let qu = tr (λ n → q _ ⇒ n) (q-deterministic qv qv') qu in
  n' ,, qu ,, qw 
_∙~_ {A = A ⟶ B} p1 p2 pu =
  let fu ,, gv ,, $fu ,, $gv ,, fu~gv = p1 pu in
  -- Reflexivity can be proved for a value in relation with anything using symmetry
  -- and transitivity (induction hypothesis). This is exactly what is needed here.
  let reflv = (pu ~⁻¹) ∙~ pu in
  let gv' ,, hw ,, $gv' ,, $hw ,, gv~hw = p2 reflv in
  let fu~gv = tr (λ u → _ ~ u) ($-deterministic $gv $gv') fu~gv in
  fu ,, hw ,, $fu ,, $hw ,, fu~gv ∙~ gv~hw


-- Equivalence implies equality of quotes, and the reciprocal holds for neutral values.
~q : {Γ : Con} {A : Ty} {u v : Val Γ A} → u ~ v → u q≡ v
q~ : {Γ : Con} {A : Ty} {u v : Ne Val Γ A} → u qs≡ v → vneu u ~ vneu v

-- The reciprocal allows to prove reflexivity on variables.
refl~var : {Γ : Con} {A : Ty} {x : Var Γ A} → vneu (var x) ~ vneu (var x)
refl~var {x = x} = q~ (var x ,, qsvar ,, qsvar)

~q {A = o} p = p
~q {Γ = Γ} {A = A ⟶ B} pf =
  let fz ,, gz ,, $fz ,, $gz ,, fz~gz = pf (refl~var {Γ = Γ , A} {x = z}) in
  let n ,, qfz ,, qgz = ~q fz~gz in
  nlam n ,, q⟶ $fz qfz ,, q⟶ $gz qgz

q~ {A = o} (n ,, qsu ,, qsv) = nneu n ,, qo qsu ,, qo qsv
q~ {A = A ⟶ B} {u = f} {v = g} (ne ,, qsf ,, qsg) {Δ = Δ} {u = u} {v = v} u~v =
  let fu = app (f ++NV Δ) u in
  let gv = app (g ++NV Δ) v in
  let $fu = tr (λ x → (x $ u ⇒ vneu fu))
               (vneu++V {u = f} ⁻¹)
               ($app (f ++NV Δ) u) in
  let $gv = tr (λ x → (x $ v ⇒ vneu gv))
               (vneu++V {u = g} ⁻¹)
               ($app (g ++NV Δ) v) in
  let (n ,, qu ,, qv) = ~q u~v in
  let ne+ = ne ++NN Δ in
  let qsf+ = qswks qsf Δ in
  let qsg+ = qswks qsg Δ in
  vneu fu ,, vneu gv ,, $fu ,, $gv ,,
  q~ (app ne+ n ,, qsapp qsf+ qu ,, qsapp qsg+ qv)
  where vneu++V : ∀ {Γ Δ : Con} {A : Ty} {u : Ne Val Γ A} →
                    (vneu u) ++V Δ ≡ vneu (u ++NV Δ)
        vneu++V {Δ = ●} = refl
        vneu++V {Δ = Δ , B} = ap (λ x → x +V B) (vneu++V {Δ = Δ})


-- Extension of equivalence to environments.
_~E_ : {Γ Δ : Con} → Env Γ Δ → Env Γ Δ → Set
_~E_ {Δ = ●} _ _ = ⊤
_~E_ {Δ = Δ , A} (σ , u) (ν , v) = Σ (σ ~E ν) λ _ → u ~ v

π₁~E : {Γ Δ : Con} {A : Ty} {σ ν : Env Γ (Δ , A)} → σ ~E ν → (π₁list σ) ~E (π₁list ν)
π₁~E {σ = _ , _} {ν = _ , _} = fst

π₂~E : {Γ Δ : Con} {A : Ty} {σ ν : Env Γ (Δ , A)} → σ ~E ν → (π₂list σ) ~ (π₂list ν)
π₂~E {σ = _ , _} {ν = _ , _} = snd


_+~E_ : {Γ Δ : Con} {σ ν : Env Γ Δ} → σ ~E ν → (A : Ty) → (σ +E A) ~E (ν +E A)
_+~E_ {Δ = ●} tt A = tt
_+~E_ {Δ = Δ , B} {σ = σ , u} {ν = ν , v} (σ~ν ,, u~v) A = σ~ν +~E A ,, u~v +~ A

_++~E_ : {Γ Δ : Con} {σ ν : Env Γ Δ} → σ ~E ν → (Δ : Con) → (σ ++E Δ) ~E (ν ++E Δ)
p ++~E ● = p
p ++~E (Δ , A) = (p ++~E Δ) +~E A

refl~id : {Γ : Con} → (idenv {Γ}) ~E idenv
refl~id {●} = tt
refl~id {Γ , A} = refl~id +~E A ,, refl~var


-- Evaluation of a term in equivalent environments gives equivalent results.
-- This is the reflexivity case of the next theorem.
eval≡~ : {Γ Δ : Con} {A : Ty} (u : Tm Δ A) {ρ δ : Env Γ Δ} → ρ ~E δ →
         Σ (Val Γ A) λ uρ →
         Σ (Val Γ A) λ uδ →
         Σ (eval u > ρ ⇒ uρ) λ _ →
         Σ (eval u > δ ⇒ uδ) λ _ →
           uρ ~ uδ

evals≡~ : {Γ Δ Θ : Con} (σ : Tms Δ Θ) {ρ δ : Env Γ Δ} → ρ ~E δ →
          Σ (Env Γ Θ) λ σρ →
          Σ (Env Γ Θ) λ σδ →
          Σ (evals σ > ρ ⇒ σρ) λ _ →
          Σ (evals σ > δ ⇒ σδ) λ _ →
            σρ ~E σδ

eval≡~ (u [ σ ]) ρ~δ =
  let σρ ,, σδ ,, evalsσρ ,, evalsσδ ,, σρ~σδ = evals≡~ σ ρ~δ in
  let uρ ,, uδ ,, evaluρ ,, evaluδ ,, uρ~uδ = eval≡~ u σρ~σδ in
  uρ ,, uδ ,, eval[] evalsσρ evaluρ ,, eval[] evalsσδ evaluδ ,, uρ~uδ
eval≡~ (π₂ σ) ρ~δ =
  let σρ ,, σδ ,, evalsσρ ,, evalsσδ ,, σρ~σδ = evals≡~ σ ρ~δ in
  π₂list σρ ,, π₂list σδ ,, evalπ₂ evalsσρ ,, evalπ₂ evalsσδ ,, π₂~E σρ~σδ
eval≡~ {Γ} {Δ} {A ⟶ B} (lam u) {ρ} {δ} ρ~δ =
  vlam u ρ ,, vlam u δ ,, evallam u ρ ,, evallam u δ ,,
  λ {Δ = Θ} {u = v} {v = w} v~w →
  let uρv ,, uδw ,, evaluρv ,, evaluδw ,, uρv~uδw = eval≡~ u (ρ~δ ++~E Θ ,, v~w) in
  let evallamuρv = tr (λ u → u $ v ⇒ uρv) ([]++V {Θ = Θ}) ($lam evaluρv) in
  let evallamuδw = tr (λ u → u $ w ⇒ uδw) ([]++V {Θ = Θ}) ($lam evaluδw) in
  uρv ,, uδw ,, evallamuρv ,, evallamuδw ,, uρv~uδw
eval≡~ (app f) ρ~δ =
  let fρ ,, fδ ,, evalfρ ,, evalfδ ,, fρ~fδ = eval≡~ f (π₁~E ρ~δ) in
  let fρ ,, fδ ,, $fρ ,, $fδ ,, fρ~fδ = fρ~fδ (π₂~E ρ~δ) in
  fρ ,, fδ ,, evalapp evalfρ $fρ ,, evalapp evalfδ $fδ ,, fρ~fδ

evals≡~ id {ρ = ρ} {δ = δ} ρ~δ =
  ρ ,, δ ,, evalsid ,, evalsid ,, ρ~δ
evals≡~ (σ ∘ ν) ρ~δ =
  let νρ ,, νδ ,, evalsνρ ,, evalsνδ ,, νρ~νδ = evals≡~ ν ρ~δ in
  let σρ ,, σδ ,, evalsσρ ,, evalsσδ ,, σρ~σδ = evals≡~ σ νρ~νδ in
  σρ ,, σδ ,, evals∘ evalsνρ evalsσρ ,, evals∘ evalsνδ evalsσδ ,, σρ~σδ
evals≡~ ε _ =
  ε ,, ε ,, evalsε ,, evalsε ,, tt
evals≡~ (σ , u) ρ~δ =
  let σρ ,, σδ ,, evalsσρ ,, evalsσδ ,, σρ~σδ = evals≡~ σ ρ~δ in
  let uρ ,, uδ ,, evaluρ ,, evaluδ ,, uρ~uδ = eval≡~ u ρ~δ in
  σρ , uρ ,, σδ , uδ ,, evals, evalsσρ evaluρ ,, evals, evalsσδ evaluδ ,, (σρ~σδ ,, uρ~uδ)
evals≡~ (π₁ σ) ρ~δ =
  let σρ ,, σδ ,, evalsσρ ,, evalsσδ ,, σρ~σδ = evals≡~ σ ρ~δ in
  π₁list σρ ,, π₁list σδ ,, evalsπ₁ evalsσρ ,, evalsπ₁ evalsσδ ,, π₁~E σρ~σδ
