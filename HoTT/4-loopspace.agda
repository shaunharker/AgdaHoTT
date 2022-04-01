{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap

-- Eckmann-Hilton Argument

-- Loop space

Ω[_,_] :
  {ℓ : Level} →
  (A : Set ℓ) →
  (a : A)     →
  Set ℓ

Ω[ A , a ] = a ≡ a

Ω²[_,_] :
  {ℓ : Level} →
  (A : Set ℓ) →
  (a : A)     →
  Set ℓ

Ω²[ A , a ] = Ω[ Ω[ A , a ] , refl ]

Theorem·2·1·6 : --Eckmann-Hilton
  --                    Argument
  {ℓ : Level}                  →
  (A : Set ℓ)                  →
  (a : A)                      →
  (α β : Ω²[ A , a ])          →
  α • β ≡ β • α

Theorem·2·1·6 A a α β =
  α•β≡α⋆β • α⋆β≡α⋆'β • α⋆'β≡β•α
  where
  _•₁_ :
    {ℓ : Level}   →
    {A : Set ℓ}   →
    {a b c : A}   →
    {p q : a ≡ b} →
    (α : p ≡ q)   →
    (r : b ≡ c)   →
    (p • r ≡ q • r)

  α •₁ refl = sym(ru _) • α • (ru _)

  _•₂_ :
    {ℓ : Level}   →
    {A : Set ℓ}   →
    {a b c : A}   →
    {r s : b ≡ c} →
    (q : a ≡ b)   →
    (β : r ≡ s)   →
    (q • r ≡ q • s)

  refl •₂ β = sym(lu _) • β • (lu _)

  _⋆_ :
    {ℓ : Level}   →
    {A : Set ℓ}   →
    {a b c : A}   →
    {p q : a ≡ b} →
    {r s : b ≡ c} →
    (α : p ≡ q)   →
    (β : r ≡ s)   →
    (p • r ≡ q • s)

  α ⋆ β = (α •₁ _) • (_ •₂ β)

  _⋆'_ :
    {ℓ : Level}   →
    {A : Set ℓ}   →
    {a b c : A}   →
    {p q : a ≡ b} →
    {r s : b ≡ c} →
    (α : p ≡ q)   →
    (β : r ≡ s)   →
    (p • r ≡ q • s)

  α ⋆' β = (_ •₂ β) • (α •₁ _)

  α•β≡α⋆β : α • β ≡ α ⋆ β

  α•β≡α⋆β =
    ap (λ x → α • x )
       (lu β • ru (refl • β))
    •
    ap (λ x → x • (refl • β • refl))
       (lu α • ru (refl • α))

  α⋆β≡α⋆'β : α ⋆ β ≡ α ⋆' β

  α⋆β≡α⋆'β = ⋆≡⋆' α β where
    ⋆≡⋆' :
      {ℓ : Level}    →
      {A : Set ℓ}    →
      {a b c : A}    →
      {p q : a ≡ b}  →
      {r s : b ≡ c}  →
      (α : p ≡ q)    →
      (β : r ≡ s)    →
      (α ⋆ β ≡ α ⋆' β)

    ⋆≡⋆' {p = refl} {q = refl}
         {r = refl} {s = refl}
         refl refl = refl

  α⋆'β≡β•α : α ⋆' β ≡ β • α

  α⋆'β≡β•α =
    sym ((ap (λ x → β • x )
             (lu α • ru (refl • α)))
         •
         (ap (λ x → x • (refl • α • refl))
             (lu β • ru (refl • β))))
