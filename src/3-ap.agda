{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition

ap : -- applicative
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  {x y : A}       →
  (f : A → B)     →
  (x ≡ y)         →
  f x ≡ f y

ap f refl = refl

-- Lemma·2·2·2·1 :
ap[•] :
  {ℓ₁ ℓ₂ : Level}                  →
  {A : Set ℓ₁}                     →
  {B : Set ℓ₂}                     →
  {x y z : A}                      →
  (f : A → B)                      →
  (p : x ≡ y)                      →
  (q : y ≡ z)                      →
  ap f (p • q) ≡ (ap f p) • (ap f q)

ap[•] f refl refl = refl

--Lemma·2·2·2·2 :
ap[sym] :
  {ℓ₁ ℓ₂ : Level}           →
  {A : Set ℓ₁}              →
  {B : Set ℓ₂}              →
  {x y : A}                 →
  (f : A → B)               →
  (p : x ≡ y)               →
  ap f (sym p) ≡ sym (ap f p)

ap[sym] f refl = refl

--Lemma·2·2·2·3 :
ap[∘] :
  {ℓ₁ ℓ₂ ℓ₃ : Level}         →
  {A : Set ℓ₁}               →
  {B : Set ℓ₂}               →
  {C : Set ℓ₃}               →
  {x y : A}                  →
  (g : B → C)                →
  (f : A → B)                →
  (p : x ≡ y)                →
  ap (g ∘ f) p ≡ ap g (ap f p)

ap[∘] f g refl = refl

--Lemma·2·2·2·4 :
ap[id] :
  {ℓ : Level}    →
  {A : Set ℓ}    →
  {x y : A}      →
  (p : x ≡ y)    →
  ap id p ≡ p

ap[id] refl = refl
