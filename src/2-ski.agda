{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality

infixl 50 _∘'_
_∘'_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}                     →
  {A : Set ℓ₁}                           →
  {B : A → Set ℓ₂}                       →
  {C : (a : A) → B a → Set ℓ₃}           →
  (f : Π A λ a → Π (B a) λ b → C a b)    →
  (g : Π A B)                            →
  (a : A)                                →
  C a (g a)

(f ∘' g) x = f x (g x)

S = _∘'_

K : {ℓ₁ ℓ₂ ℓ₃ : Level} →
    {A : Set ℓ₁}       →
    {B : Set ℓ₂}       →
    (x : A)            →
    (y : B)            →
    A

K x y = x

I :
  {ℓ : Level} →
  {X : Set ℓ} →
  (X → X)

I x = x

modus·ponens : {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  (x : A)            →
  (y : A → B)        →
  B

modus·ponens x y = y x
