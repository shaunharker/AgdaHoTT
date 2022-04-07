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

elim[Π≡Π] :
  {ℓ₁ ℓ₂ : Level}        →
  {A : Set ℓ₁}           →
  {B : A → Set ℓ₂}       →
  {f g : Π A B}          →
  f ≡ g                  →
  f ∼ g

elim[Π≡Π] refl = refl[∼]

postulate
  intr[Π≡Π] :
    {ℓ₁ ℓ₂ : Level}       →
    {A : Set ℓ₁}          →
    {B : A → Set ℓ₂}      →
    {f g : Π A B}         →
    f ∼ g                 →
    f ≡ g

postulate
  weakuniq[Π≡Π] :
    {ℓ₁ ℓ₂ : Level}                   →
    {A : Set ℓ₁}                      →
    {B : A → Set ℓ₂}                  →
    {f : Π A B}                       →
    (intr[Π≡Π] ∘ elim[Π≡Π]) ∼ id' (f ≡ f)

uniq[Π] :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : A → Set ℓ₂}                  →
  {f g : Π A B}                     →
  intr[Π≡Π] ∘ elim[Π≡Π] ∼ id' (f ≡ g)

uniq[Π] {f = f} {g = f} refl = weakuniq[Π≡Π] refl

postulate
  elim[Π≡Π]·is·epic :
    {ℓ₁ ℓ₂ ℓ₃ : Level}                →
    {A : Set ℓ₁}                      →
    {B : A → Set ℓ₂}                  →
    {f g : Π A B}                     →
    {C : Set ℓ₃}                      →
    {F G : (f ∼ g) → C}               →
    (F ∘ elim[Π≡Π] ≡ G ∘ elim[Π≡Π])   →
    F ≡ G

comp[Π] :
  {ℓ₁ ℓ₂ : Level}                   →
  {A : Set ℓ₁}                      →
  {B : A → Set ℓ₂}                  →
  {f g : Π A B}                     →
  elim[Π≡Π] ∘ intr[Π≡Π] ∼ id' (f ∼ g)

comp[Π] = elim[Π≡Π] (elim[Π≡Π]·is·epic (intr[Π≡Π] (elim[Π≡Π]
  (ass[∘] elim[Π≡Π] intr[Π≡Π] elim[Π≡Π]) •[∼] (elim[Π≡Π] ∘∼ uniq[Π]))))

∼≃≡ :
  {ℓ₁ ℓ₂ : Level}   →
  {A : Set ℓ₁}      →
  {B : A → Set ℓ₂}  →
  {f g : Π A B}     →
  (f ∼ g) ≃ (f ≡ g)

∼≃≡ =
  QIP·to·≃
  QIP[ intr[Π≡Π]
     , elim[Π≡Π]
     , uniq[Π]
     , comp[Π] ]

comp·refl[Π] :
  {ℓ₁ ℓ₂ : Level}              →
  {A : Set ℓ₁}                 →
  {B : A → Set ℓ₂}             →
  {f : Π A B}                  →
  intr[Π≡Π] refl[∼] ≡ refl' f

comp·refl[Π] = uniq[Π] refl

comp·sym[Π] :
  {ℓ₁ ℓ₂ : Level}              →
  {A : Set ℓ₁}                 →
  {B : A → Set ℓ₂}             →
  {f g : Π A B}                →
  (α : f ≡ g)                  →
  intr[Π≡Π] (sym[∼] (elim[Π≡Π] α)) ≡ sym α

comp·sym[Π] refl = uniq[Π] refl

comp·•[Π] :
  {ℓ₁ ℓ₂ : Level}              →
  {A : Set ℓ₁}                 →
  {B : A → Set ℓ₂}             →
  {f g h : Π A B}              →
  (α : f ≡ g)                  →
  (β : g ≡ h)                  →
  intr[Π≡Π] (elim[Π≡Π] α •[∼] elim[Π≡Π] β) ≡ α • β

comp·•[Π] refl refl = uniq[Π] refl

comp·transport[→] :
  {ℓ₁ ℓ₂ ℓ₃ : Level}                 →
  {X : Set ℓ₁}                       →
  {A : X → Set ℓ₂}                   →
  {B : X → Set ℓ₃}                   →
  {x₁ x₂ : X}                        →
  (p : x₁ ≡ x₂)                      →
  (f : A x₁ → B x₁)                  →
  let
    A→B = λ x → (A x → B x)
    g = λ a → f (transport A (sym p) a)
  in
  transport A→B p f ≡ λ a → transport B p (g a)

comp·transport[→] refl _ = intr[Π≡Π] refl[∼]

comp·transport[Π] :
  {ℓ₁ ℓ₂ ℓ₃ : Level}                  →
  {X : Set ℓ₁}                        →
  {A : X → Set ℓ₂}                    →
  {B : (x : X) → A x → Set ℓ₃}      →
  {x₁ x₂ : X}                         →
  (p : x₁ ≡ x₂)                       →
  (f : Π (A x₁) λ a → B x₁ a)         →
  (a : A x₂)                          →
  let
    P = λ x → Π (A x) (B x)
    Q = λ {[ w₁ , w₂ ] → B w₁ w₂}
    q = sym (intr[Σ≡Σ] [ sym p , refl ])
    g = λ a → f (transport A (sym p) a)
  in
  transport P p f a ≡ transport Q q (g a)

comp·transport[Π] refl f a = refl

Lemma·2·9·6 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}                  →
  {X : Set ℓ₁}                        →
  {A : X → Set ℓ₂}                    →
  {B : X → Set ℓ₃}                    →
  {x₁ x₂ : X}                         →
  (p : x₁ ≡ x₂)                       →
  (f : A x₁ → B x₁)                   →
  (g : A x₂ → B x₂)                   →
  let
    Aᵀ : A x₁ → A x₂
    Aᵀ = transport A p
    Bᵀ : B x₁ → B x₂
    Bᵀ = transport B p
    A→B = λ x → (A x → B x)
    A→Bᵀ : A→B x₁ → A→B x₂
    A→Bᵀ = transport A→B p
  in
  (A→Bᵀ f ≡ g) ≃ (Bᵀ ∘ f ≡ g ∘ Aᵀ)

Lemma·2·9·6 {A = A} {B = B} {x₁ = x₁} {x₂ = x₂} refl f g =
  ≃[ id , id , id , refl[∼] , refl[∼] ]

Lemma·2·9·7 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}                →
  {X : Set ℓ₁}                      →
  {A : X → Set ℓ₂}                  →
  {B : (Σ X A) → Set ℓ₃}            →
  {x₁ x₂ : X}                       →
  (p : x₁ ≡ x₂)                     →
  (f : (a : A x₁) → B [ x₁ , a ] )  →
  (g : (a : A x₂) → B [ x₂ , a ] )  →
  let
    Aᵀ : A x₁ → A x₂
    Aᵀ = transport A p
    Bᵀ : (a : A x₁) → B [ x₁ , a ] → B [ x₂ , Aᵀ a ]
    Bᵀ = λ a → transport B (path·lift A p a)
    ΠAB : (x : X) → Set (ℓ₂ ⊔ ℓ₃)
    ΠAB = λ x → (a : A x) → B [ x , a ]
    ΠABᵀ : ΠAB x₁ → ΠAB x₂
    ΠABᵀ = transport ΠAB p
  in
  (ΠABᵀ f ≡ g) ≃ (Bᵀ ∘' f ∼ g ∘ Aᵀ)

Lemma·2·9·7 refl f g =
  QIP·to·≃
  QIP[ elim[Π≡Π] , intr[Π≡Π] , comp[Π] , uniq[Π] ]

sym∘sym≡id :
  {ℓ : Level}   →
  {A : Set ℓ}   →
  {x y : A}     →
  sym ∘ sym ≡ id' (x ≡ y)

sym∘sym≡id = intr[Π≡Π] λ { refl  → refl }

ΠΠ≃Σ→ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}               →
  (X : Set ℓ₁)                     →
  (Y : X → Set ℓ₂)                 →
  ((x : X) → Y x → Set ℓ₃) ≃ ((Σ X Y) → Set ℓ₃)

ΠΠ≃Σ→ X Y = QIP·to·≃
  QIP[ (λ f → λ { [ x , y ] → f x y})
     , (λ f → λ { x y → f [ x , y ]})
     , refl[∼]
     , refl[∼] ]
