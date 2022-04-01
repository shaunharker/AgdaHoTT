{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 2-ski
open import 3-ap
open import 4-homotopy
open import 4-transport
open import 5-qip
open import 6-equivalence
open import 7-dependentpairs
open import 8-dependentfuncs

-- Lemma 2.10.1

elim[Set≡Set] :
  {ℓ : Level}   →
  {A B : Set ℓ} →
  (A ≡ B)       →
  (A ≃ B)

elim[Set≡Set] refl = QIP·to·≃
  QIP[ id
     , id
     , refl[∼]
     , refl[∼] ]

-- Axiom 2.10.3

postulate
  intr[Set≡Set] :
    {ℓ : Level}   →
    {A B : Set ℓ} →
    (A ≃ B)       →
    (A ≡ B)

postulate
  comp[Set≡Set] :
    {ℓ : Level}   →
    {A B : Set ℓ} →
    elim[Set≡Set] ∘ intr[Set≡Set] ∼ id' (A ≃ B)

postulate
  uniq[Set≡Set] :
    {ℓ : Level}   →
    {A B : Set ℓ} →
    intr[Set≡Set] ∘ elim[Set≡Set] ∼ id' (A ≡ B)

UnivalenceAxiom :
  {ℓ : Level}   →
  {A B : Set ℓ} →
  (A ≃ B) ≃ (A ≡ B)

UnivalenceAxiom = QIP·to·≃
  QIP[ intr[Set≡Set]
     , elim[Set≡Set]
     , uniq[Set≡Set]
     , comp[Set≡Set] ]

--shorthand

ua :
  {ℓ : Level}   →
  {A B : Set ℓ} →
  (A ≃ B)       →
  (A ≡ B)

ua {A = A} {B = B} = intr[Set≡Set] {A = A} {B = B}

--idtoeqv = elim[Set≡Set]

comp·refl[Set] :
  {ℓ : Level} →
  {A : Set ℓ} →
  refl' A ≡ ua refl[≃]

comp·refl[Set] {A = A} =
  sym (uniq[Set≡Set] refl) • ap ua refl

comp·•[Set]·1 :
  {ℓ : Level}     →
  {A B C : Set ℓ} →
  (p : A ≡ B)     →
  (q : B ≡ C)     →
  elim[Set≡Set] q ∘[≃] elim[Set≡Set] p ≡ elim[Set≡Set] (p • q)

comp·•[Set]·1 refl refl = refl

comp·•[Set]·2 :
  {ℓ : Level}     →
  {A B C : Set ℓ} →
  (f : A ≃ B)     →
  (g : B ≃ C)     →
  ua f • ua g ≡ ua (g ∘[≃] f)

comp·•[Set]·2 {A = A} {B = B} {C = C} f g =
  sym (
    ap ua (ap (λ x → g ∘[≃] x)
              (sym (comp[Set≡Set] f))
           •
           ap (λ x → x ∘[≃] elim[Set≡Set] (ua f))
              (sym (comp[Set≡Set] g))
           •
           comp·•[Set]·1 (ua f) (ua g))
    •
    uniq[Set≡Set] (ua f • ua g))

comp·sym[Set]·elim :
  {ℓ : Level}     →
  {A B : Set ℓ}   →
  (p : A ≡ B)     →
  elim[Set≡Set] (sym p) ≡ sym[≃] (elim[Set≡Set] p)

comp·sym[Set]·elim refl = refl

comp·sym[Set]·intr :
  {ℓ : Level}     →
  {A B : Set ℓ}   →
  (f : A ≃ B)     →
  ua (sym[≃] f) ≡ sym (ua f)

comp·sym[Set]·intr f =
  ap (ua ∘ sym[≃]) (sym (comp[Set≡Set] f)) •
  sym (ap ua (comp·sym[Set]·elim (ua f)))  •
  uniq[Set≡Set] (sym (ua f))

Lemma·2·10·5 :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : A → Set ℓ₂} →
  {x y : A} →
  (p : x ≡ y) →
  (u : B x) →
  transport B p u ≡ _≃_.f (elim[Set≡Set] (ap B p)) u

Lemma·2·10·5 refl u = refl
