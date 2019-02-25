{-# OPTIONS --safe --cubical #-}

module Library.Equality where

{-
  Equality reasoning, definitions and basic lemmas.
-}

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path public
  renaming (_≡_ to Path)
open import Agda.Builtin.Cubical.Id public
  renaming (primIdPath to IdPath;
            primIdFace to IdFace;
            primIdJ to J;
            primIdElim to IdElim)


infix 4 _≡_
_≡_ = Id

-- Reflexivity
refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl = conid i1 _

-- Symmetry
infix 8 _⁻¹
_⁻¹ : ∀ {l} {A : Set l} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A = A} {x} = J (λ y p → y ≡ x) refl

refl⁻¹ : ∀ {l} {A : Set l} {x : A} → refl {x = x} ⁻¹ ≡ refl
refl⁻¹ = refl

⁻¹⁻¹ : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ⁻¹ ⁻¹ ≡ p
⁻¹⁻¹ = J (λ y p → p ⁻¹ ⁻¹ ≡ p) refl _

-- Transitivity
infixr 6 _∙_
_∙_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {A = A} {x} p q = J (λ y p → {z : A} → y ≡ z → x ≡ z)
                        (J (λ z q → x ≡ z) refl)
                        p q

refl∙ : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → refl ∙ p ≡ p
refl∙ = J (λ y p → refl ∙ p ≡ p) refl _

∙refl : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ∙ refl ≡ p
∙refl = J (λ y p → p ∙ refl ≡ p) refl _

∙∙ : ∀ {l} {A : Set l} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
       (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙∙ {A = A} {p = p} {q} {r} =
  J (λ y p → {z w : A} (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r))
    (λ q r → J (λ z q → {w : A} (r : z ≡ w) → (refl ∙ q) ∙ r ≡ refl ∙ (q ∙ r))
               (λ r → J (λ w r → (refl ∙ refl) ∙ r ≡ refl ∙ (refl ∙ r))
                        refl
                        r)
               q r)
    p q r

-∙⁻¹- : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ∙ p ⁻¹ ≡ refl
-∙⁻¹- {p = p} = J (λ y p → p ∙ p ⁻¹ ≡ refl) refl p

-⁻¹∙- : ∀ {l} {A : Set l} {x y : A} {p : x ≡ y} → p ⁻¹ ∙ p ≡ refl
-⁻¹∙- {p = p} = J (λ y p → p ⁻¹ ∙ p ≡ refl) refl p

∙⁻¹ : ∀ {l} {A : Set l} {x y z : A} {p : x ≡ y} {q : y ≡ z} →
        (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
∙⁻¹ {A = A} {p = p} {q} = J (λ y p → {z : A} (q : y ≡ z) → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹)
                            (λ q → J (λ z q → (refl ∙ q) ⁻¹ ≡ q ⁻¹ ∙ refl ⁻¹) refl q)
                            p q


-- Congruence
ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f {x = x} = J (λ y p → f x ≡ f y) refl

-- Transport
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → A ≡ B → A → B
_*_ {A = A} = J (λ B P → A → B) (λ x → x)

-- Transport through a dependent family
tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P p x = (ap P p) * x

-- Function extensionality.
ext : ∀ {l m} {A : Set l} {B : A → Set m} (f g : (x : A) → B x) →
        (p : (x : A) → f x ≡ g x) → f ≡ g
ext f g p = conid i0 (λ i x → IdPath (p x) i)

-- Dependent paths
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
_≡[_]≡_ {l} {A} x P y = J (λ B P → A → B → Set l) _≡_ P x y

-- Congruence for dependent functions.
apd : ∀ {l m} {A : Set l} {B : A → Set m} (f : (x : A) → B x)
        {x y : A} (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd {B = B} f {x} = J (λ y p → f x ≡[ ap B p ]≡ f y) refl


-- Filling of transport
_*fill_ : ∀ {l} {A B : Set l} (p : A ≡ B) (x : A) →
            x ≡[ p ]≡ p * x
_*fill_ {A = A} = J (λ B p → (x : A) → x ≡[ p ]≡ p * x) (λ x → refl)

trfill : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A}
           (p : x ≡ y) (px : P x) → px ≡[ ap P p ]≡ tr P p px
trfill P p x = (ap P p) *fill x

-- Transport with a dependent path.
trd : ∀ {l m n} {A : Set l} {B : A → Set m} (P : {x : A} → B x → Set n)
        {a b : A} {p : a ≡ b} {x : B a} {y : B b} →
        x ≡[ ap B p ]≡ y → P x → P y
trd {B = B} P {a = a} {p = p} q px =
  J (λ b p → {x : B a} {y : B b} → x ≡[ ap B p ]≡ y → P x → P y)
    (λ {x} → J (λ y q → P x → P y) (λ x → x))
    p q px



isProp : ∀ {l} → Set l → Set l
isProp A = (x y : A) → x ≡ y

isSet : ∀ {l} → Set l → Set l
isSet A = {x y : A} → isProp (x ≡ y)

PropisSet : ∀ {l} {A : Set l} → isProp A → isSet A
PropisSet {A = A} isprop {x = x} p q =
  g⁻¹g p ∙ g⁻¹g q ⁻¹
  where g : (y : A) → x ≡ y
        g = isprop x
        g⁻¹g : {y z : A} (p : y ≡ z) → p ≡ (g y) ⁻¹ ∙ g z
        g⁻¹g {y} = J (λ z p → p ≡ (g y) ⁻¹ ∙ g z) (-⁻¹∙- {p = isprop x y} ⁻¹)

isPropisProp : ∀ {l} {A : Set l} → isProp (isProp A)
isPropisProp P Q = ext P Q λ x →
                   ext (P x) (Q x) λ y →
                   PropisSet P (P x y) (Q x y)

isPropisSet : ∀ {l} {A : Set l} → isProp (isSet A)
-- Function extensionality with implicit arguments is annoying.
isPropisSet P Q = conid i0 λ i {x} {y} p q →
                             IdPath (PropisSet P (P p q) (Q p q)) i
