{-# OPTIONS --without-K --exact-split --safe #-}
open import Agda.Primitive
infixl 10 _≡_
infixl 50 _+_
infixl 60 _·_
infixl 50 _•_

data _≡_ {ℓ : Level} {A : Set ℓ} : (x y : A) → Set ℓ where
  refl : {z : A} → z ≡ z

ap : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → {x y : A} →
  (f : A → B) → (x ≡ y) → f x ≡ f y
ap f refl = refl

sym : {ℓ : Level} → {A : Set ℓ} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_•_ : {ℓ : Level} → {A : Set ℓ} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl • refl = refl

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

_+_ : (m n : Nat) → Nat
_+_ zero n = n
_+_ (suc m) n = suc ( m + n )

addition·left·identity : (m : Nat) → zero + m ≡ m
addition·left·identity = λ _ → refl

addition·right·identity : (m : Nat) → m + zero ≡ m
addition·right·identity zero = refl
addition·right·identity (suc m) = ap suc (addition·right·identity m)

addition·is·associative : (m n k : Nat) → m + (n + k) ≡ (m + n) + k
addition·is·associative zero n k = refl
addition·is·associative (suc m) n k = ap suc (addition·is·associative m n k)

addition·is·commutative : (m n : Nat) → (m + n ≡ n + m)
addition·is·commutative zero zero = refl
addition·is·commutative (suc m) zero = ap suc (addition·is·commutative m zero)
addition·is·commutative zero (suc n) = ap suc (sym (addition·right·identity n))
addition·is·commutative (suc m) (suc n) = (addition·fact (suc m) n) •
  ap suc (addition·is·commutative (suc m) n) where
    addition·fact : (a b : Nat) → a + suc b ≡ suc (a + b)
    addition·fact zero _ = refl
    addition·fact (suc a) b = ap suc (addition·fact a b)

_·_ : (m n : Nat) → Nat
_·_ zero n = zero
_·_ (suc m) n = n + (m · n)

multiplication·left·zero : (m : Nat) → zero · m ≡ zero
multiplication·left·zero m = refl

multiplication·right·zero : (m : Nat) → m · zero ≡ zero
multiplication·right·zero zero = refl
multiplication·right·zero (suc m) = multiplication·right·zero m

rearrange : (a b c d : Nat) → (a + b) + (c + d) ≡ (a + c) + (b + d)
rearrange zero b c d = (addition·is·associative b c d) • (ap (λ x → x + d)
  (addition·is·commutative b c)) • (sym (addition·is·associative c b d))
rearrange (suc a) b c d = ap suc (rearrange a b c d)

one : Nat
one = suc zero

multiplication·left·one : (m : Nat) → one · m ≡ m
multiplication·left·one zero = multiplication·right·zero one
multiplication·left·one (suc m) = ap suc (addition·right·identity m)

multiplication·right·one : (m : Nat) → m · one ≡ m
multiplication·right·one zero = multiplication·right·zero one
multiplication·right·one (suc m) = (ap (λ x → one + x)
  (multiplication·right·one m)) • (ap suc (addition·left·identity m))

multiplication·is·left·distributive : (m n k : Nat) →
  m · (n + k) ≡ m · n + m · k
multiplication·is·left·distributive zero n k = refl
multiplication·is·left·distributive (suc m) n k = ap (λ x → (n + k) + x)
  (multiplication·is·left·distributive m n k) • (rearrange n k (m · n) (m · k))

multiplication·is·right·distributive : (m n k : Nat) →
  (m + n) · k ≡ m · k + n · k
multiplication·is·right·distributive zero n k = refl
multiplication·is·right·distributive (suc m) n k = (ap (λ x → k + x)
  (multiplication·is·right·distributive m n k)) •
  (addition·is·associative k (m · k) (n · k))

multiplication·is·associative : (m n k : Nat) → m · (n · k) ≡ (m · n) · k
multiplication·is·associative zero n k = refl
multiplication·is·associative (suc m) n k = (ap (λ x → n · k + x)
  (multiplication·is·associative m n k)) •
  (sym (multiplication·is·right·distributive n (m · n) k))

multiplication·is·commutative : (m n : Nat) → m · n ≡ n · m
multiplication·is·commutative zero n = sym (multiplication·right·zero n)
multiplication·is·commutative (suc m) n = (ap (λ x → n + x)
  (multiplication·is·commutative m n)) • (sym (multiplication·fact n m)) where
    multiplication·fact : (a b : Nat) → a · (suc b) ≡ a + a · b
    multiplication·fact zero b = refl
    multiplication·fact (suc a) b = ap suc ((ap (λ x → b + x)
      (multiplication·fact a b)) • (addition·is·associative b a (a · b) ) •
      (ap (λ x → x + a · b) (addition·is·commutative b a)) •
      (sym (addition·is·associative a b (a · b))))
