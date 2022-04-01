{-# OPTIONS --without-K #-}
open import Agda.Primitive
infixl 10 _≡_
infixl 50 _•_

data _≡_ {ℓ : Level} {A : Set ℓ} : (x y : A) → Set ℓ where refl : {z : A} → z ≡ z

Ω[_,_] : {ℓ : Level} → (A : Set ℓ) → (a : A) → Set ℓ
Ω[ A , a ] = a ≡ a

Ω²[_,_] : {ℓ : Level} → (A : Set ℓ) → (a : A) → Set ℓ
Ω²[ A , a ] = Ω[ Ω[ A , a ] , refl ]

_•_ : {ℓ : Level} → {A : Set ℓ} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl • refl = refl

Eckmann·Hilton : {ℓ : Level} → (A : Set ℓ) → (a : A) → (α β : Ω²[ A , a ]) → α • β ≡ β • α
Eckmann·Hilton A a α β = α•β≡α⋆β • α⋆β≡α⋆'β • α⋆'β≡β•α where
  sym : {ℓ : Level} → {A : Set ℓ} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
  ru : {ℓ : Level} → {A : Set ℓ} → {x y : A} → (p : x ≡ y) → p ≡ p • refl
  ru refl = refl
  lu : {ℓ : Level} → {A : Set ℓ} → {x y : A} → (p : x ≡ y) → p ≡ refl • p
  lu refl = refl
  ap : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
  ap f refl = refl
  _•₁_ : {ℓ : Level} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → (p • r ≡ q • r)
  α •₁ refl = sym(ru _) • α • (ru _)
  _•₂_ : {ℓ : Level} → {A : Set ℓ} → {a b c : A} → {r s : b ≡ c} → (q : a ≡ b) → (β : r ≡ s) → (q • r ≡ q • s)
  refl •₂ β = sym(lu _) • β • (lu _)
  _⋆_ : {ℓ : Level} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → (p • r ≡ q • s)
  α ⋆ β = (α •₁ _) • (_ •₂ β)
  _⋆'_ : {ℓ : Level} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → (p • r ≡ q • s)
  α ⋆' β = (_ •₂ β) • (α •₁ _)
  α•β≡α⋆β : α • β ≡ α ⋆ β
  α•β≡α⋆β = ap (λ x → α • x) (lu β • ru (refl • β)) • ap (λ x → x • (refl • β • refl)) (lu α • ru (refl • α))
  α⋆β≡α⋆'β : α ⋆ β ≡ α ⋆' β
  α⋆β≡α⋆'β = ⋆≡⋆' α β where
    ⋆≡⋆' : {ℓ : Level} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → (α ⋆ β ≡ α ⋆' β)
    ⋆≡⋆' {p = refl} {q = refl} {r = refl} {s = refl} refl refl = refl
  α⋆'β≡β•α : α ⋆' β ≡ β • α
  α⋆'β≡β•α = sym ((ap (λ x → β • x) (lu α • ru (refl • α))) • (ap (λ x → x • (refl • α • refl)) (lu β • ru (refl • β))))
