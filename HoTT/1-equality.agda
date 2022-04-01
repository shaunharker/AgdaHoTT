{-# OPTIONS --without-K #-}
-- Module 1
open import Agda.Primitive

Π :
  {ℓ₁ ℓ₂ : Level}  →
  (A : Set ℓ₁)     →
  (B : A → Set ℓ₂) →
  Set (ℓ₁ ⊔ ℓ₂)

Π A B = (x : A) → B x

record Σ
  {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁)
  (B : A → Set ℓ₂) :
  Set (ℓ₁ ⊔ ℓ₂)
  where
  constructor
    [_,_]
  field
    fst : A
    snd : B fst

infixl 50 _×_
_×_ :
  {ℓ₁ ℓ₂ : Level} →
  (A : Set ℓ₁)    →
  (B : Set ℓ₂)    →
  Set (ℓ₁ ⊔ ℓ₂)

A × B = Σ A λ a → B

infixl 10 _≡_
data _≡_
  {ℓ : Level}
  {A : Set ℓ} :
  (x y : A) → Set ℓ
  where
  refl : {z : A} → z ≡ z

refl' :
  {ℓ : Level} →
  {A : Set ℓ} →
  (x : A)     →
  x ≡ x

refl' x = refl

id :
  {ℓ : Level} →
  {X : Set ℓ} →
  (X → X)

id x = x

id' : --identity
  {ℓ : Level}    →
  (X : Set ℓ)    →
  (X → X)

id' X x = x

sym :
  {ℓ : Level} →
  {A : Set ℓ} →
  {x y : A}   →
  x ≡ y       →
  y ≡ x

sym refl = refl

infixl 50 _•_
_•_ :
  {ℓ : Level}      →
  {A : Set ℓ}      →
  {x y z : A}      →
  x ≡ y            →
  y ≡ z            →
  x ≡ z

refl • refl = refl

infixl 30 _≡•_
_≡•_ :
  {ℓ : Level}      →
  {A : Set ℓ}      →
  {x y z : A}      →
  {p q : x ≡ y}    →
  (s : p ≡ q)      →
  (r : y ≡ z)      →
  p • r ≡ q • r

refl ≡• refl = refl

infixl 30 _•≡_
_•≡_ :
  {ℓ : Level}      →
  {A : Set ℓ}      →
  {x y z : A}      →
  {p q : y ≡ z}    →
  (r : x ≡ y)      →
  (s : p ≡ q)      →
  r • p ≡ r • q

refl •≡ refl = refl

ass : --associativity
  {ℓ : Level}             →
  {A : Set ℓ}             →
  {x y z w : A}           →
  {p : x ≡ y}             →
  {q : y ≡ z}             →
  {r : z ≡ w}             →
  (p • q) • r ≡ p • (q • r)

ass {p = refl} {q = refl} {r = refl} = refl

ru : -- right unit
  {ℓ : Level}    →
  {A : Set ℓ}    →
  {x y : A}      →
  (p : x ≡ y)    →
  p ≡ p • refl

ru refl = refl

lu : -- left unit
  {ℓ : Level}   →
  {A : Set ℓ}   →
  {x y : A}     →
  (p : x ≡ y)   →
  p ≡ refl • p

lu refl = refl

ri : --right inverse
  {ℓ : Level}      →
  {A : Set ℓ}      →
  {x y : A}        →
  (p : x ≡ y)      →
  p • sym p ≡ refl

ri refl = refl

li : --left inverse
  {ℓ : Level}      →
  {A : Set ℓ}      →
  {x y : A}        →
  (p : x ≡ y)      →
  sym p • p ≡ refl

li refl = refl

ii : --inv of inv
  {ℓ : Level}   →
  {A : Set ℓ}   →
  {x y : A}     →
  (p : x ≡ y)   →
  p ≡ sym (sym p)

ii refl = refl
