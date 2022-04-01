{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap

-- homotopy section 2.4

infixl 10 _∼_
_∼_ :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {P : A → Set ℓ₂} →
  (f g : Π A P) →
  Set (ℓ₁ ⊔ ℓ₂)

_∼_ {A = A} {P = P} f g = (x : A) → f x ≡ g x

elim[∼] :
  {ℓ₁ ℓ₂ : Level}    →
  {A : Set ℓ₁}       →
  {P : A → Set ℓ₂}   →
  {f g : Π A P}      →
  (f ∼ g)            →
  (x : A)            →
  f x ≡ g x

elim[∼] H = H

refl[∼] : --Lemma·2·4·2·1
  {ℓ₁ ℓ₂ : Level}       →
  {A : Set ℓ₁}          →
  {P : A → Set ℓ₂}      →
  {f : Π A P}           →
  f ∼ f

refl[∼] = λ _ → refl

sym[∼] : -- Lemma·2·4·2·2
  {ℓ₁ ℓ₂ : Level}       →
  {A : Set ℓ₁}          →
  {P : A → Set ℓ₂}      →
  {f g : Π A P}         →
  f ∼ g                 →
  g ∼ f

sym[∼] H =
  λ a → sym (H a)

infixl 50 _•[∼]_
_•[∼]_ : -- Lemma·2·4·2·3
  {ℓ₁ ℓ₂ : Level}      →
  {A : Set ℓ₁}         →
  {P : A → Set ℓ₂}     →
  {f g h : Π A P}      →
  f ∼ g                →
  g ∼ h                →
  f ∼ h

_•[∼]_ α β =
  λ a → (α a) • (β a)

infixl 40 _∘∼_
_∘∼_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  {C : Set ℓ₃}       →
  {f g : A → B}      →
  (h : B → C)        →
  f ∼ g              →
  h ∘ f ∼ h ∘ g

h ∘∼ H =
  λ x → ap h (H x)

infixl 40 _∼∘_
_∼∘_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁}       →
  {B : Set ℓ₂}       →
  {C : Set ℓ₃}       →
  {f g : A → B}      →
  f ∼ g              →
  (h : C → A)        →
  f ∘ h ∼ g ∘ h

H ∼∘ h =
  λ x → H (h x)

-- lemma 2.4.3 again
ap[∼] :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  {x y : A}       →
  (p : x ≡ y)     →
  {F G : A → B}   →
  (H : F ∼ G)     →
  ap F p ≡ H x • ap G p • sym (H y)

ap[∼] {x = x} refl H =  sym (ri (H x)) • (ru (H x) ≡• sym (H x))

ap[∼id] :
  {ℓ : Level}    →
  {A : Set ℓ}    →
  {x y : A}      →
  (p : x ≡ y)    →
  {F : A → A}    →
  (H : F ∼ id)   →
  ap F p ≡ H x • p • sym (H y)

ap[∼id] {x = x} refl H = sym (ri (H x)) • (ru (H x) ≡• sym (H x))

Lemma·2·4·3 :
  {ℓ₁ ℓ₂ : Level}                       →
  {A : Set ℓ₁}                          →
  {B : Set ℓ₂}                          →
  {f g : A → B}                         →
  (H   : f ∼ g)                         →
  {x y : A}                             →
  (p   : x ≡ y)                         →
  (H x) • (ap g p) ≡ (ap f p) • (H y)

Lemma·2·4·3 H {x} {x} refl =
  sym (ru (H x)) • lu (H x)

Corollary·2·4·4 :
  {ℓ : Level}          →
  {A : Set ℓ}          →
  (x : A)              →
  {f : A → A}          →
  (H : f ∼ id)         →
  H (f x) ≡ ap f (H x)

Corollary·2·4·4 x {f} H =
  cancel
    (H x)
  from·the·right·of
    (ap (λ z → (H (f x)) • z) (apid (H x))
     • Lemma·2·4·3 H (H x))
  where
  apid :
    {ℓ : Level}    →
    {A   : Set ℓ}  →
    {x y : A    }  →
    (p   : x ≡ y)  →
    p ≡ ap id p

  apid refl = refl

  cancel_from·the·right·of_ :
    {ℓ : Level}             →
    {A     : Set ℓ}         →
    {x y z : A    }         →
    (r     : y ≡ z)         →
    {p q   : x ≡ y}         →
    p • r ≡ q • r           →
    p ≡ q

  cancel_from·the·right·of_ refl s =
    (ru _) • s • sym (ru _)
