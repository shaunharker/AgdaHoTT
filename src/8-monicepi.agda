{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import 1-equality
open import 2-composition
open import 3-ap
open import 4-homotopy
open import 5-qip
open import 6-equivalence

data Bool : Set where
  true  : Bool
  false : Bool

isContr :
  {ℓ : Level} →
  (X : Set ℓ) →
  Set ℓ

isContr X = Σ X λ x → Π X λ y → x ≡ y

isProp :
  {ℓ : Level} →
  (X : Set ℓ) →
  Set ℓ

isProp X = (x y : X) → isContr (x ≡ y)

isSet :
  {ℓ : Level} →
  (X : Set ℓ) →
  Set ℓ

isSet X = (x y : X) → isProp (x ≡ y)

-- monic and injective

is·monic :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →
  Set (ℓ₁ ⊔ ℓ₂)

is·monic {A = A} {B = B} f =
  (g h : B → A)   →
  (f ∘ g ∼ f ∘ h) →
  g ∼ h

monic·theorem :
  {ℓ₁ ℓ₂ ℓ₃ : Level}  →
  {A : Set ℓ₁}        →
  {B : Set ℓ₂}        →
  {C : Set ℓ₃}        →
  (f : A → B)         →
  (is·monic f)        →
  (g h : C → A)       →
  ((f ∘ g) ∼ (f ∘ h)) →
  g ∼ h

monic·theorem f imf g h fg∼fh = -- auto-deduced!
    λ c → imf (λ _ → g c)
              (λ _ → h c)
              (λ _ → fg∼fh c)
              ((f ∘ h) c)

is·injective :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  (f : A → B) →
  Set (ℓ₁ ⊔ ℓ₂)

is·injective {A = A} {B = B} f =
  (x y : A) →
  f x ≡ f y →
  (x ≡ y)

-- is·injective f ≃ is·monic f ?
-- I have everything but the last homotopy.

is·injective·to·is·monic :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  (f : A → B) →
  is·injective f → is·monic f

is·injective·to·is·monic f iif =
  λ g h f∘g∼f∘h z → iif (g z) (h z) (f∘g∼f∘h z)

is·monic·to·is·injective :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  (f : A → B) →
  is·monic f → is·injective f

is·monic·to·is·injective f imf =
  λ x y fx≡fy →
    imf (λ _ → x) (λ _ → y) (λ _ → fx≡fy) (f x) -- (or f y)

monic·injective·homotopy·1 :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  (f : A → B) →
  is·monic·to·is·injective f ∘ is·injective·to·is·monic f ∼ id

monic·injective·homotopy·1 f = λ _ → refl

-- monic·injective·homotopy·2 :
--   {ℓ₁ ℓ₂ : Level} →
--   {A : Set ℓ₁} →
--   {B : Set ℓ₂} →
--   (f : A → B) →
--   is·injective·to·is·monic f ∘ is·monic·to·is·injective f ∼ id
--
-- monic·injective·homotopy·2 f = {!   !}

-- epic and surjective

is·epic :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →
  Set (ℓ₁ ⊔ ℓ₂)

is·epic {A = A} {B = B} f =
  (g h : B → A) →
  (g ∘ f ∼ h ∘ f) →
  g ∼ h

is·surjective :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁}    →
  {B : Set ℓ₂}    →
  (f : A → B)     →
  Set (ℓ₁ ⊔ ℓ₂)

is·surjective {A = A} {B = B} f =
  (b : B) → Σ A λ a → f a ≡ b

surjective·theorem :
  {ℓ₁ ℓ₂ ℓ₃ : Level}  →
  {A : Set ℓ₁}        →
  {B : Set ℓ₂}        →
  {C : Set ℓ₃}        →
  (f : A → B)         →
  (is·surjective f)   →
  (g h : B → C)       →
  (g ∘ f ∼ h ∘ f)     →
  g ∼ h

surjective·theorem f isf g h gf∼hf b =
  gb≡gfa • gfa≡hfa • hfa≡hb
  where
  a       = Σ.fst (isf b)
  fa≡b    = Σ.snd (isf b)
  gb≡gfa  = sym (ap g fa≡b)
  gfa≡hfa = gf∼hf a
  hfa≡hb  = ap h fa≡b



is·surjective·to·is·epic :
  {ℓ₁ ℓ₂ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  (f : A → B) →
  is·surjective f → is·epic f

is·surjective·to·is·epic = surjective·theorem

-- is·epic·to·is·surjective :
--   {ℓ₁ ℓ₂ : Level} →
--   {A : Set ℓ₁} →
--   {B : Set ℓ₂} →
--   (f : A → B) →
--   is·epic f → is·surjective f

-- is·epic·to·is·surjective f = {!   !}
-- -- undoable? i seem unable to formalize the following:
-- -- https://mathoverflow.net/questions/178778/in-the-category-of-sets-epimorphisms-are-surjective-constructive-proof
--
-- epic·theorem :
--   {ℓ₁ ℓ₂ ℓ₃ : Level}  →
--   {A : Set ℓ₁}        →
--   {B : Set ℓ₂}        →
--   {C : Set ℓ₃}        →
--   (f : A → B)         →
--   (is·epic f)         →
--   (g h : B → C)       →
--   (g ∘ f ∼ h ∘ f) →
--   g ∼ h
--
-- epic·theorem = {!   !}


-- is·epic+·to·surjective {A = A} {B = B} h ief b =
--   {!   !}
--   where
--   f : B → Set _
--   f b' = Σ A (λ a → h a ≡ b)
--   g : B → Set _
--   g b' = Σ A (λ a → (h a ≡ b) × (b' ≡ b))
--   f∘h∼g∘h : f ∘ h ∼ g ∘ h
--   f∘h∼g∘h = λ a → {!   !}
--   f∼g : f ∼ g
--   f∼g = ief f g f∘h∼g∘h

-- Andrej Bauer gives the following.
--    im h = {b ∈ B | ∃ a ∈ A . h a ≡ b }
--    f g : B → 2ᴮ
--    f b = {b} ∩ im h
--    g b = {b}
--    ∀ (a ∈ A) . f (h a) ≡ {h a}
--    ∀ (a ∈ A) . g (h a) ≡ {h a}
--    f∼g
--    ∀ y ∈ B . f y ≡ g y
--    ∀ y ∈ B . {y} ∩ im(h) ≡ {y}
--    ∀ y ∈ B . y ∈ im(h)
-- The last line is surjectivity.
-- There are a number of things here I do not
-- know how to formalize constructively.
--    -- im h = {b ∈ B | ∃ a ∈ A . h a ≡ b }
--    im h = Σ B λ b → Σ A λ a → h a ≡ b
--    -- f g : B → 2ᴮ
--    f g : B → Σ B (Set _)
--    -- f b = {b} ∩ im h
--    -- g b = {b}
--    f b' = Σ B λ b → (b' ≡ b) × (Σ A λ a → h a ≡ b)
--    g b' = Σ B λ b → (b' ≡ b)
--    -- ∀ (a ∈ A) . f (h a) ≡ {h a}
--    (a : A) → f (h a) ≡ Σ B λ b → (h a ≡ b)
--    -- ∀ (a ∈ A) . g (h a) ≡ {h a}
--    (a : A) → g (h a) ≡ Σ B λ b → (h a ≡ b)
--    f ∼ g
--    -- ∀ y ∈ B . f y ≡ g y
--    (b : B) → f b ≡ g b
--    (b' : B) → (Σ B λ b → (b' ≡ b × Σ A λ a → h a ≡ b)) ≡
--               (Σ B λ b → (b' ≡ b))
--    ... can I get this far?
--    ∀ y ∈ B . {y} ∩ im(h) ≡ {y}
--    ∀ y ∈ B . y ∈ im(h)
-- is·surjective {A = A} {B = B} f =
--   (b : B) → Σ A λ a → f a ≡ b

-- full strength epi
is·epic+ :
  {ℓ₁ ℓ₂ : Level}     →
  {A : Set ℓ₁}        →
  {B : Set ℓ₂}        →
  (f : A → B)         →
  Set (lsuc (ℓ₁ ⊔ ℓ₂))

is·epic+ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {A = A} {B = B} f =
  (C : Set (ℓ₁ ⊔ ℓ₂))      →
  (g h : B → C)            →
  (g ∘ f ∼ h ∘ f)          →
  g ∼ h

-- is·epic+·to·surjective :
--   {ℓ₁ ℓ₂ : Level}  →
--   {A : Set ℓ₁}     →
--   {B : Set ℓ₂}     →
--   (f : A → B)      →
--   (is·epic+ f)     →
--   is·surjective f
--
-- is·epic+·to·surjective {A = A} {B = B} h ief b =
--   {!   !}
--   where
--   im = Σ B λ b → Σ A λ a → h a ≡ b
--   f : B → Σ B (Set _)
--   f b' = Σ B λ b → (b' ≡ b) × (Σ A λ a → h a ≡ b)
--   g : B → Σ B (B → Set _)
--   g b' = Σ B λ b → (b' ≡ b)
--   -- ∀ (a ∈ A) . f (h a) ≡ {h a}
--   [1] = (a : A) → f (h a) ≡ Σ B λ b → (h a ≡ b)
--   -- ∀ (a ∈ A) . g (h a) ≡ {h a}
--   [2] = (a : A) → g (h a) ≡ Σ B λ b → (h a ≡ b)
--   [3] = f ∼ g
--   [4] = (b' : B) → (Σ B λ b → (b' ≡ b × Σ A λ a → h a ≡ b)) ≡ (Σ B λ b → (b' ≡ b))
--   -- ... can I get this far?
--   -- ∀ y ∈ B . {y} ∩ im(h) ≡ {y}
--   -- ∀ y ∈ B . y ∈ im(h)
--   -- is·surjective {A = A} {B = B} f =
--   -- (b : B) → Σ A λ a → f a ≡ b

--- part 2

epi·monic·1 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}       →
  {A : Set ℓ₁}             →
  {B : Set ℓ₂}             →
  {C : Set ℓ₃}             →
  (f : B → A)              →
  (g : A → B)              →
  (u v : C → A)            →
  (f ∘ g ∼ id)             →
  (g ∘ u ∼ g ∘ v)          →
  u ∼ v

epi·monic·1 {A = A} {B = B} {C = C} f g u v fg∼id gu∼gv =
  λ x → g·monic (u x) (v x) (gu∼gv x)
  where
  g·monic : (a₁ a₂ : A) → g a₁ ≡ g a₂ → a₁ ≡ a₂
  g·monic a₁ a₂ ga₁≡ga₂ =
    (sym (fg∼id a₁)) • (ap f ga₁≡ga₂) • (fg∼id a₂)

epi·monic·2 :
  {ℓ₁ ℓ₂ ℓ₃ : Level}       →
  {A : Set ℓ₁}             →
  {B : Set ℓ₂}             →
  {C : Set ℓ₃}             →
  (f : B → A)              →
  (g : A → B)              →
  (u v : A → C)            →
  (f ∘ g ∼ id)             →
  (u ∘ f ∼ v ∘ f)          →
  u ∼ v

epi·monic·2 {A = A} {B = B} {C = C} f g u v fg∼id uf∼vf a =
  (ap u (sym fb≡a)) • (uf∼vf b) • (ap v fb≡a)
  where
  f·epi : (a : A) → Σ B (λ b → f b ≡ a)
  f·epi a = [ g a , fg∼id a ]
  b = Σ.fst (f·epi a)
  fb≡a = Σ.snd (f·epi a)
