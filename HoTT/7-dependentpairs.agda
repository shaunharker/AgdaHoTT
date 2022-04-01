{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap
open import 4-homotopy
open import 4-transport
open import 5-qip
open import 6-equivalence

uniq[×] :
  {ℓ₁ ℓ₂ : Level}           →
  {A : Set ℓ₁}              →
  {B : Set ℓ₂}              →
  (x : A × B)               →

  x ≡ [ Σ.fst x , Σ.snd x ]

uniq[×] [ a , b ] = refl


apr₁ :
  {ℓ₁ ℓ₂ : Level}  →
  {A : Set ℓ₁}     →
  {B : A → Set ℓ₂} →
  {x y : Σ A B}    →
  x ≡ y            →

  Σ.fst x ≡ Σ.fst y

apr₁ = ap Σ.fst

-- apr₂ and hence apr₁×apr₂ fail due to dependent structure

elim[Σ≡Σ] :
  {ℓ₁ ℓ₂ : Level }                        →
  {A : Set ℓ₁ }                           →
  {P : A → Set ℓ₂}                        →
  {x y : Σ A P}                           →
  let
    x₁ = Σ.fst x ; x₂ = Σ.snd x
    y₁ = Σ.fst y ; y₂ = Σ.snd y
  in
  (x ≡ y)                                 →

  Σ (x₁ ≡ y₁) (λ p → transport P p x₂ ≡ y₂)

elim[Σ≡Σ] refl = [ refl , refl ]

intr[Σ≡Σ] :
  {ℓ₁ ℓ₂ : Level}                             →
  {A : Set ℓ₁}                                →
  {P : A → Set ℓ₂}                            →
  {x y : Σ A P}                               →
  let
    x₁ = Σ.fst x ; x₂ = Σ.snd x
    y₁ = Σ.fst y ; y₂ = Σ.snd y
  in
  Σ (x₁ ≡ y₁) (λ p → transport P p x₂ ≡ y₂)   →

  x ≡ y

intr[Σ≡Σ] [ refl , refl ] = refl

comp[Σ] :
  {ℓ₁ ℓ₂ : Level}                          →
  {A : Set ℓ₁}                             →
  {P : A → Set ℓ₂}                         →
  {x y : Σ A P}                            →

  elim[Σ≡Σ] {x = x} {y = y} ∘ intr[Σ≡Σ] ∼ id

comp[Σ] [ refl , refl ] = refl

uniq[Σ] :
  {ℓ₁ ℓ₂ : Level}                    →
  {A : Set ℓ₁}                       →
  {P : A → Set ℓ₂}                   →
  {x y : Σ A P}                      →

  intr[Σ≡Σ] ∘ elim[Σ≡Σ] ∼ id' ( x ≡ y )

uniq[Σ] refl = refl

--Corollary·2·7·3 gives what appears to be
--   a different uniqueness principle.

Theorem·2·7·2 :
  { ℓ₁ ℓ₂ : Level }                     →
  { A : Set ℓ₁ }                        →
  { P : A → Set ℓ₂}                     →
  (x y : Σ A P)                         →
  let
    x₁ = Σ.fst x ; x₂ = Σ.snd x
    y₁ = Σ.fst y ; y₂ = Σ.snd y
  in

  (x ≡ y) ≃ Σ (x₁ ≡ y₁) λ p →
              transport P p x₂ ≡ y₂

Theorem·2·7·2 _ _ =
  QIP·to·≃ QIP[ elim[Σ≡Σ] , intr[Σ≡Σ]
              , comp[Σ]   , uniq[Σ]    ]

discussion·prior·to·2·7·4 :
  { ℓ₁ ℓ₂ : Level }                →
  { A : Set ℓ₁    }                →
  ( P : A → Set ℓ₂)                →
  {x₁ y₁ : A      }                →
  (p     : x₁ ≡ y₁)                →
  (x₂    : P x₁   )                →

  path·lift P p x₂ ≡ intr[Σ≡Σ] [ p , refl ]

discussion·prior·to·2·7·4 P refl x₂ = refl

Theorem·2·7·4 :
  { ℓ₁ ℓ₂ ℓ₃ : Level }                          →
  ( X : Set ℓ₁ )                                →
  ( Y : X → Set ℓ₂)                             →
  ( Z : Σ X Y → Set ℓ₃ )                        →
  {a₁ b₁ : X      }                             →
  (a₂    : Y a₁   )                             →
  (a₃    : Z [ a₁ , a₂ ])                       →
  (p     : a₁ ≡ b₁)                             →

  let
    YZ = λ x → Σ (Y x) (λ y → Z [ x , y ])
    b₂ = transport Y p a₂
    b₃ = transport Z (path·lift Y p a₂) a₃
  in
  transport YZ p [ a₂ , a₃ ] ≡ [ b₂ , b₃ ]


Theorem·2·7·4 X Y Z a₂ a₃ refl  = refl

Theorem·2·7·4·Book :
  { ℓ₁ ℓ₂ ℓ₃ : Level }                          →
  ( X : Set ℓ₁ )                                →
  ( Y : X → Set ℓ₂)                             →
  ( Z : Σ X Y → Set ℓ₃ )                        →
  {a₁ b₁ : X      }                             →
  (a₂    : Y a₁   )                             →
  (a₃    : Z [ a₁ , a₂ ])                       →
  (p     : a₁ ≡ b₁)                             →

  let
    YZ = λ x → Σ (Y x) (λ y → Z [ x , y ])
    b₂ = transport Y p a₂
    b₃ = transport Z (intr[Σ≡Σ] [ p , refl ]) a₃
  in
  transport YZ p [ a₂ , a₃ ] ≡ [ b₂ , b₃ ]


Theorem·2·7·4·Book X Y Z a₂ a₃ refl  = refl

intr[×≡×] :
  {ℓ₁ ℓ₂ : Level}           →
  {A : Set ℓ₁}              →
  {B : Set ℓ₂}              →
  {x y : A × B}             →
  (Σ.fst x ≡ Σ.fst y) × (Σ.snd x ≡ Σ.snd y) →
  x ≡ y

intr[×≡×] {x = x} {y = x} [ refl , refl ] = uniq[×] x
