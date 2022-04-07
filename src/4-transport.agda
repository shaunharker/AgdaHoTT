{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap

transport : --Lemma·2·3·1
  {ℓ₁ ℓ₂ : Level}         →
  {A : Set ℓ₁}            →
  {x y : A}               →
  (P : A → Set ℓ₂)        →
  (p : x ≡ y)             →

  (P x → P y)

transport _ refl = id

path·lift : --Lemma·2·3·2
  {ℓ₁ ℓ₂ : Level}         →
  {A : Set ℓ₁}            →
  {x y : A}               →
  (P : A → Set ℓ₂)        →
  (p : x ≡ y)             →
  (u : P x)               →
  [ x , u ] ≡ [ y , (transport P p) u ]

path·lift _ refl u = refl

apd : --Lemma·2·3·4
  {ℓ₁ ℓ₂ : Level}         →
  {A : Set ℓ₁}            →
  {x y : A}               →
  {P : A → Set ℓ₂}        →
  (f : Π A P)             →
  (p : x ≡ y)             →
  (transport P p) (f x) ≡ f y

apd f refl = refl

transportconst : --Lemma·2·3·5
  {ℓ₁ ℓ₂ : Level}                →
  {A : Set ℓ₁}                   →
  {B : Set ℓ₂}                   →
  {x y : A}                      →
  let
    P : A → Set ℓ₂
    P = λ a → B
  in
  (p : x ≡ y)                    →
  (b : B)                        →
  transport P p b ≡ b

transportconst refl b = refl

Function·2·3·6 :
  {ℓ₁ ℓ₂ : Level}            →
  {A : Set ℓ₁}               →
  {B : Set ℓ₂}               →
  {f : A → B}                →
  {x y : A}                  →
  {p : x ≡ y}                →
  f x ≡ f y                  →
  transport _ p (f x) ≡ f y

Function·2·3·6 {f = f} {x} {y} {p} fx≡fy =
  transportconst p (f x) • fx≡fy

Function·2·3·7 :
  {ℓ₁ ℓ₂ : Level}            →
  {A : Set ℓ₁}               →
  {B : Set ℓ₂}               →
  {f : A → B}                →
  {x y : A}                  →
  {p : x ≡ y}                →
  transport _ p (f x) ≡ f y  →
  f x ≡ f y

Function·2·3·7 {f = f} {x} {y} {p} tpfx≡fy =
  sym(transportconst p (f x)) • tpfx≡fy

Lemma·2·3·8 :
  {ℓ₁ ℓ₂ : Level}   →
  {A : Set ℓ₁}      →
  {B : Set ℓ₂}      →
  (f : A → B)       →
  {x y : A}         →
  (p : x ≡ y)       →

  apd f p ≡ transportconst p (f x) • ap f p

Lemma·2·3·8 f refl = refl

-- This Lemma gets used in the univalence section 2.10

Lemma·2·3·9 :
  {ℓ₁ ℓ₂ : Level}          →
  {A : Set ℓ₁}             →
  (P : A → Set ℓ₂)         →
  {x y z : A}              →
  (p : x ≡ y)              →
  (q : y ≡ z)              →
  (u : P x)                →

  transport P q (transport P p u) ≡ transport P (p • q) u

Lemma·2·3·9 P refl refl u = refl

Lemma·2·3·10 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}       →
  {A : Set ℓ₁}             →
  {B : Set ℓ₂}             →
  (P : B → Set ℓ₃)         →
  (f : A → B)              →
  {x y : A}                →
  (p : x ≡ y)              →
  (u : P (f x))            →

  transport (P ∘ f) p u ≡ transport P (ap f p) u

Lemma·2·3·10 P f refl u = refl

Lemma·2·3·11 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}        →
  {A : Set ℓ₁}              →
  (P : A → Set ℓ₂)          →
  (Q : A → Set ℓ₃)          →
  (f : (x : A) → P x → Q x) →
  {x y : A}                 →
  (p : x ≡ y)               →
  (u : P x)                 →

  transport Q p (f x u) ≡ f y (transport P p u)

Lemma·2·3·11 P Q f refl u = refl
