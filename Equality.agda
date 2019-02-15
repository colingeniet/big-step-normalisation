open import Agda.Primitive
open import Agda.Builtin.Equality public

infix 8 _⁻¹
_⁻¹ : ∀ {l} {A : Set l} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infixr 6 _∙_
_∙_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

ap : ∀ {l m} {A : Set l} {B : Set m} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
ap f refl = refl

-- Equality through equality of types.
infix 5 _≡[_]≡_
_≡[_]≡_ : ∀ {l} {A B : Set l} → A → A ≡ B → B → Set l
x ≡[ refl ]≡ y = x ≡ y

apd : ∀ {l m} {A : Set l} {B : A → Set m} (f : (x : A) → B x)
        {x y : A} (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd f refl = refl

-- Transport.
infixr 20 _*_
_*_ : ∀ {l} {A B : Set l} → A ≡ B → A → B
refl * x = x

tr : ∀ {l m} {A : Set l} (P : A → Set m) {x y : A} →
       x ≡ y → P x → P y
tr P p x = (ap P p) * x
