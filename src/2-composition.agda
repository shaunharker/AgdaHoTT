{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality

infixl 50 _∘_
_∘_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  {C : B → Set ℓ₃}   →
  ((b : B) → C b)    →
  (g : A → B)        →
  (a : A)            →
  C (g a)

(f ∘ g) x = f ( g x )

ass[∘] :
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}   →
  {A : Set ℓ₁}            →
  {B : Set ℓ₂}            →
  {C : Set ℓ₃}            →
  {D : Set ℓ₄}            →
  (f : C → D)             →
  (g : B → C)             →
  (h : A → B)             →
  (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

ass[∘] = λ f g h → refl

≡∘ :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  {C : Set ℓ₃}       →
  {f g : B → C}      →
  (f ≡ g)            →
  (h : A → B)        →
  (f ∘ h ≡ g ∘ h)

≡∘ refl h = refl

∘≡ :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  {C : Set ℓ₃}       →
  {f g : A → B}      →
  (h : B → C)        →
  (f ≡ g)            →
  (h ∘ f ≡ h ∘ g)

∘≡ h refl = refl
