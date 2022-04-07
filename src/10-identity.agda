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
open import 9-universes

Theorem·2·11·1·V1 :
  {ℓ : Level} →
  {A B : Set ℓ} →
  (eqv : A ≃ B) →
  (x y : A) →
  let
    f = _≃_.f eqv
  in
  Σ ((x ≡ y) ≃ (f x ≡ f y))
    (λ { ≃[ f' , _ , _ , _ , _ ] → f' ≡ ap f})

Theorem·2·11·1·V1 {A = A} {B = B} eqv x y =
   [ QIP·to·≃ QIP[ F , G , α' , β' ] , refl ]
   where
   qip = ≃·to·QIP eqv
   f = QIP.f qip
   g = QIP.g qip
   α = QIP.α qip
   β = QIP.β qip

   F : {x y : A} → (p : x ≡ y) → f x ≡ f y
   F = ap f

   G : {x y : A} → (q : f x ≡ f y) → x ≡ y
   G {x = x} {y = y} q = sym (β x) • ap g q • (β y)

   α' : F ∘ G ∼ id
   α' q = [1] ([A] • [B] • [C])
     where
     [1] : {ℓ : Level} → {A : Set ℓ} → {p q r s : A} → {x : p ≡ q} → {a b : q ≡ r} → {y : r ≡ s } → x • a • y ≡ x • b • y → a ≡ b
     [1] {x = refl} {a = refl} {b = b} {y = refl} p = p • sym (lu b • (ru (refl • b)))

     [2] : {ℓ : Level} → {A : Set ℓ} → {p q r s : A} → {x : q ≡ p} → {z : q ≡ r} → {y : r ≡ s} → x • (sym x • z • y) • sym y ≡ z
     [2] {x = refl} {z = refl} {y = refl} = refl

     [A] : α (f x) • F ( G q ) • sym (α (f y)) ≡ F (ap g (F (G q)))
     [A] = sym (ap[∼id] _ α) • ap[∘] _ _ _

     [B] : F (ap g (F (G q))) ≡ F (ap g q)
     [B] = ap (ap f) (sym (ap[∘] _ _ _) • ap[∼id] _ β • [2])

     [C] : F (ap g q) ≡ α (f x) • q • sym (α (f y))
     [C] = sym (ap[∘] _ _ _) • ap[∼id] _ α

   β' : G ∘ F ∼ id
   β' refl = ass • (sym (β x) •≡ sym (lu (β x))) • li (β x)

Theorem·2·11·1·V2 :
  {ℓ : Level} →
  {A B : Set ℓ} →
  (f : A → B) →
  isequiv f →
  (x y : A) →
  isequiv (ap {x = x} {y = y} f)

Theorem·2·11·1·V2 {A = A} {B = B} f [ eqv , refl ] x y = Theorem·2·11·1·V1 eqv x y

Id :
  {ℓ : Level} →
  (A : Set ℓ) →
  Set ℓ

Id A = Σ (A × A) λ { [ a₁ , a₂ ] → a₁ ≡ a₂}

Refl :
  {ℓ : Level} →
  {A : Set ℓ} →
  A → Id A

Refl a = [ [ a , a ] , refl ]

Ap :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →
  Id A → Id B

Ap f [ [ x , x ] , refl ] = Refl (f x)

Ap[id] :
  {ℓ : Level} →
  {A : Set ℓ} →
  (p : Id A) →
  Ap id p ≡ p

Ap[id] [ [ x , x ] , refl ] = refl

Ap[id'] :
  {ℓ : Level} →
  (A : Set ℓ) →
  Ap (id' A) ≡ id' (Id A)

Ap[id'] A = intr[Π≡Π] Ap[id]

Ap[∘] :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  {C : Set ℓ₃}    →
  (f : A → B)     →
  (g : B → C)     →
  Ap (g ∘ f) ∼ (Ap g) ∘ (Ap f)

Ap[∘] f g = λ { [ [ x , x ] , refl ] → refl }

Ap[∼] :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  {f g : A → B} →
  f ∼ g →
  Ap f ∼ Ap g

Ap[∼] H [ [ x , x ] , refl ] = ap Refl (H x)

Theorem·2·11·1 :
  {ℓ : Level} →
  {A B : Set ℓ} →
  (f : A → B) →
  isequiv f →
  isequiv (Ap f)

Theorem·2·11·1 f [ eqv , refl ] =
  [ QIP·to·≃ QIP[ Ap f
                , Ap g
                , sym[∼] (Ap[∘] g f) •[∼] (Ap[∼] α) •[∼] Ap[id]
                , sym[∼] (Ap[∘] f g) •[∼] (Ap[∼] β) •[∼] Ap[id] ]
  , refl ]
  where
  qip = ≃·to·QIP eqv
  -- f = QIP.f qip
  g = QIP.g qip
  α = QIP.α qip
  β = QIP.β qip

-- Suppose

Idea·2·11·1 :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {C : Set ℓ₁} →
  {A : C → Set ℓ₂} →
  {B : C → Set ℓ₃} →
  (f : Π C (λ c → A c → B c)) →
  (Σ C (λ c → A c)) → (Σ C (λ c → B c))

Idea·2·11·1 f [ c , a ] = [ c , f c a ]

-- Idea·2·11·2 :
--   {ℓ₁ ℓ₂ ℓ₃ : Level} →
--   {C : Set ℓ₁} →
--   {A : C → Set ℓ₂} →
--   {B : C → Set ℓ₃} →
--   (f : Π C (λ c → A c → B c)) →
--   let
--     F : (Σ C (λ c → A c)) → (Σ C (λ c → B c))
--     F = λ { [ c , a ] → [ c , f c a ] }
--   in
--   isequiv F →
--   Π C (λ c → isequiv (f c))
--
-- Idea·2·11·2 {C = C} {A = A} {B = B} f [ eqv , refl ] c = {!  qip  !}
--   where
--     qip = ≃·to·QIP eqv
--     F = QIP.f qip
--     G = QIP.g qip
--     α = QIP.α qip
--     β = QIP.β qip
--     G·fst : Π (B c) λ b → Σ.fst (G [ c , b ]) ≡ c
--     G·fst b = ap Σ.fst (α [ c , b ] )
--     fc : A c → B c
--     fc = λ a → Σ.snd (F [ c , a ])
--     gc : B c → A c
--     gc = λ b → transport A (G·fst b) (Σ.snd (G [ c , b ]))
--     αc : fc ∘ gc ∼ id
--     αc = λ b → {! ap Σ.snd (α [ c , b ])  !} -- almost completely worthless error messages.
--     βc : gc ∘ fc ∼ id
--     βc = {!   !}
