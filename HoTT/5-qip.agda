{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap
open import 4-homotopy
open import 4-transport

-- Definition·2·4·6: quasi-inverse pair
record QIP
  {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁)
  (B : Set ℓ₂)
    : Set (ℓ₁ ⊔ ℓ₂)
  where
  constructor QIP[_,_,_,_]
  field
    f : A → B
    g : B → A
    α : f ∘ g ∼ id
    β : g ∘ f ∼ id

qinv :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →

  Set (ℓ₁ ⊔ ℓ₂)

qinv f = Σ (QIP _ _) λ qip → f ≡ QIP.f qip

-- Example·2·4·7
refl[QIP] :
  {ℓ : Level} →
  {A : Set ℓ} →

  qinv (id' A)

refl[QIP] = [ QIP[ id
                 , id
                 , refl[∼]
                 , refl[∼] ]
            , refl ]

sym[QIP] :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  QIP A B         →

  QIP B A

sym[QIP] QIP[ f , g , α , β ] =
  QIP[ g , f , β , α ]

•[QIP] :
  {ℓ₁ ℓ₂ ℓ₃ : Level}   →
  {A : Set ℓ₁}         →
  {B : Set ℓ₂}         →
  {C : Set ℓ₃}         →
  QIP A B              →
  QIP B C              →
  QIP A C

•[QIP] QIP[ f  , g  , α  , β ]
       QIP[ f' , g' , α' , β' ] =
  QIP[ f' ∘ f
     , g  ∘ g'
     , (f' ∘∼ α  ∼∘ g') •[∼] α'
     , (g  ∘∼ β' ∼∘ f ) •[∼] β ]

Example·2·4·8·1 :
  {ℓ : Level}               →
  {A : Set ℓ}               →
  {x y : A}                 →
  (p : x ≡ y)               →
  {z : A}                   →
  let
    f : (y ≡ z) → (x ≡ z)
    f = λ q → p • q
  in
  qinv f

Example·2·4·8·1 refl =
  [ QIP[ _•_ refl
       , id
       , (λ w → sym (lu w))
       , (λ w → sym (lu w)) ]
       , refl ]

Example·2·4·8·2 :
  {ℓ : Level}               →
  {A : Set ℓ}               →
  {x y : A}                 →
  (p : x ≡ y)               →
  {z : A}                   →
  let
    f : (z ≡ x) → (z ≡ y)
    f = λ q → q • p
  in
  qinv f

Example·2·4·8·2 refl =
  [ QIP[ (λ u → u • refl)
       , id
       , (λ u → sym (ru u))
       , (λ u → sym (ru u)) ]
       , refl ]

Example·2·4·8·3 :
  {ℓ : Level}                    →
  {A : Set ℓ}                    →
  {x y : A}                      →
  (p : x ≡ y)                    →
  (P : A → Set ℓ)                →
  let
    f : P x → P y
    f = λ z → transport P p z
  in
  qinv f

Example·2·4·8·3 refl P =
  [ QIP[ id
       , id
       , refl[∼]
       , refl[∼] ]
  , refl ]
