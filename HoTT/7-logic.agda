{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 6-equivalence

data ∅ : Set where

data 𝟙 : Set where
  0₁ : 𝟙

data 𝟚 : Set where
  0₂ : 𝟚
  1₂ : 𝟚

not :
  {ℓ : Level} →
  (A : Set ℓ) →
  Set ℓ

not A = A → ∅

_or_ :
  {ℓ : Level} →
  (A B : Set ℓ) →
  Set ℓ

_or_ {ℓ} A B = Σ 𝟚 P where
  P : 𝟚 → Set ℓ
  P 0₂ = A
  P 1₂ = B

_and_ :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  Set ℓ

_and_ {ℓ} A B = Π 𝟚 P where
  P : 𝟚 → Set ℓ
  P 0₂ = A
  P 1₂ = B

-- https://math.stackexchange.com/questions/120187/do-de-morgans-laws-hold-in-propositional-intuitionistic-logic

demorgan·1·1 :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  ((not A) and (not B)) →
  not (A or B)

demorgan·1·1 A B ¬A∧¬B =
  λ { [ 0₂ , y ] → ¬A∧¬B 0₂ y
    ; [ 1₂ , y ] → ¬A∧¬B 1₂ y }

demorgan·1·2 :
 {ℓ : Level} →
 (A : Set ℓ) →
 (B : Set ℓ) →
 not (A or B) →
 ((not A) and (not B))

demorgan·1·2 A B ¬[A∨B] =
  λ { 0₂ → λ z → ¬[A∨B] [ 0₂ , z ]
    ; 1₂ → λ z → ¬[A∨B] [ 1₂ , z ] }

demorgan·2·1 :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  ((not A) or (not B)) →
  not (A and B)

demorgan·2·1 A B [ 0₂ , ¬A ] A∧B = ¬A (A∧B 0₂)
demorgan·2·1 A B [ 1₂ , ¬B ] A∧B = ¬B (A∧B 1₂)

[¬A∨B]→[A→B] :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  ((not A) or B) →
  (A → B)

[¬A∨B]→[A→B] A B [ 0₂ , notA ] = (λ ()) ∘ notA
[¬A∨B]→[A→B] A B [ 1₂ , b ] = λ a → b

[A→B]→¬[A∧¬B] :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  (A → B) →
  not (A and not B)

[A→B]→¬[A∧¬B] A B f = λ z → z 1₂ (f (z 0₂))

¬[A∧¬B]→[A→¬¬B] :
  {ℓ : Level} →
  (A : Set ℓ) →
  (B : Set ℓ) →
  not (A and not B) →
  A → not (not B)

¬[A∧¬B]→[A→¬¬B] A B ¬[A∧¬B] a ¬B = ¬[A∧¬B] λ { 0₂ → a ; 1₂ → ¬B }

Theorem·2·8·1 :
  (x y : 𝟙)      →
  (x ≡ y) ≃ 𝟙

Theorem·2·8·1 0₁ 0₁ =
  ≃[ (λ _ → 0₁)
   , (λ _ → refl)
   , (λ _ → refl)
   , (λ { 0₁ → refl })
   , (λ { refl → refl }) ]
