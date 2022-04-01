{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 4-homotopy
open import 5-qip

-- Equivalences

infixl 10 _≃_
record _≃_
  {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁)
  (B : Set ℓ₂)
    : Set (ℓ₁ ⊔ ℓ₂)
 where
 constructor ≃[_,_,_,_,_]
 field
   f : A → B
   g : B → A
   h : B → A
   α : f ∘ g ∼ id
   β : h ∘ f ∼ id

QIP·to·≃ :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : Set ℓ₂}                      →
  (qip : QIP A B)                   →
  A ≃ B

QIP·to·≃ QIP[ f , g , α , β ] =
  ≃[ f , g , g , α , β ]

≃·to·QIP :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : Set ℓ₂}                      →
  (eqv : A ≃ B)                     →
  QIP A B

≃·to·QIP ≃[ f , g , h , α , β ] =
  QIP[ f , h , γ , β ]
  where
  γ : f ∘ h ∼ id
  γ = sym[∼] (f ∘∼ ((sym[∼] (β ∼∘ g)) •[∼] (h ∘∼ α))) •[∼] α

isequiv : --2·4·10
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →
  Set (ℓ₁ ⊔ ℓ₂)

isequiv f = Σ (_ ≃ _) λ eqv → _≃_.f eqv ≡ f

qinv·to·isequiv :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : Set ℓ₂}                      →
  (qip : QIP A B)                   →
  Σ (A ≃ B) (λ eqv → (QIP.f qip ≡ _≃_.f eqv))

qinv·to·isequiv qip = [ QIP·to·≃ qip , refl ]

isequiv·to·qinv :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : Set ℓ₂}                      →
  (eqv : A ≃ B)                     →
  Σ (QIP A B) (λ qip → (_≃_.f eqv ≡ QIP.f qip))

isequiv·to·qinv eqv = [ ≃·to·QIP eqv , refl ]

refl[≃] : --Lemma·2·4·12·1
  {ℓ : Level}            →
  {A : Set ℓ}            →
  A ≃ A

refl[≃] = ≃[ id , id , id , refl[∼] , refl[∼] ]

refl[≃]' : --Lemma·2·4·12·1
  {ℓ : Level}            →
  (A : Set ℓ)            →
  A ≃ A
refl[≃]' _ = refl[≃]

sym[≃] : --Lemma·2·4·12·2
  {ℓ₁ ℓ₂ : Level}       →
  {A : Set ℓ₁}          →
  {B : Set ℓ₂}          →
  A ≃ B                 →
  B ≃ A

sym[≃] eqv = QIP·to·≃ ( sym[QIP] ( ≃·to·QIP eqv ) )

infixl 50 _∘[≃]_
_∘[≃]_ : -- Lemma·2·4·12·3
  {ℓ₁ ℓ₂ ℓ₃ : Level}   →
  {A : Set ℓ₁}         →
  {B : Set ℓ₂}         →
  {C : Set ℓ₃}         →
  B ≃ C                →
  A ≃ B                →
  A ≃ C

≃[ f' , g' , h' , α' , β' ] ∘[≃] ≃[ f  , g  , h  , α  , β ] =
  ≃[ f' ∘ f
   , g  ∘ g'
   , h  ∘ h'
   , (f' ∘∼ α  ∼∘ g') •[∼] α'
   , (h  ∘∼ β' ∼∘ f ) •[∼] β ]
