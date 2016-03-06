module BasicSystem.DelayMonad where

open import BasicSystem.Utils

--
-- Coinductive delay monad.
--

mutual

  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

module Bind where
  infixl 1 _>>=_

  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

--
-- Termination/Convergence. Makes sense only for Delay A ∞.
--

infix 4 _⇓_

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a


-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A}
  (f : A → B) (⇓a : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

⇓bind : ∀ {A B} (f : A → Delay ∞ B)
  {a? : Delay ∞ A} {a : A} (⇓a : a? ⇓ a)
  {fa : B} (⇓fa : (a? >>= f) ⇓ fa) → f a ⇓ fa
⇓bind f now⇓ ⇓fa = ⇓fa
⇓bind f (later⇓ ⇓a) (later⇓ ⇓fa) = ⇓bind f ⇓a ⇓fa

⇓bind2 : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C} (⇓fab : (a? >>= (λ a → b? >>= f a)) ⇓ fab) → f a b ⇓ fab
⇓bind2 f now⇓ now⇓ ⇓fab = ⇓fab
⇓bind2 f now⇓ (later⇓ ⇓b) (later⇓ ⇓fab) = ⇓bind2 f now⇓ ⇓b ⇓fab
⇓bind2 f (later⇓ ⇓a) ⇓b (later⇓ ⇓fab) = ⇓bind2 f ⇓a ⇓b ⇓fab

bind⇓ : ∀ {A B} (f : A → Delay ∞ B)
  {a? a} (⇓a : a? ⇓ a) {fa} (⇓fa : f a ⇓ fa) →
  (a? >>= f) ⇓ fa
bind⇓ f now⇓ ⇓fa = ⇓fa
bind⇓ f (later⇓ ⇓a) ⇓fa = later⇓ (bind⇓ f ⇓a ⇓fa)

bind2⇓ : ∀ {A B C} (f : A → B → Delay ∞ C)
  {a? a} (⇓a : a? ⇓ a) {b? b} (⇓b : b? ⇓ b)
  {fab : C}  (⇓fab : f a b ⇓ fab) →
  (a? >>= (λ a → b? >>= f a)) ⇓ fab
bind2⇓ f now⇓ now⇓ ⇓fab = ⇓fab
bind2⇓ f now⇓ (later⇓ ⇓b) ⇓fab = later⇓ (bind2⇓ f now⇓ ⇓b ⇓fab)
bind2⇓ f (later⇓ ⇓a) ⇓b ⇓fab = later⇓ (bind2⇓ f ⇓a ⇓b ⇓fab)


--
-- Determinism: a? ⇓ a₁ → a? ⇓ a₂ → a₁ ≡ a₁
-- 

⇓-det : ∀ {A} {a? : Delay ∞ A}
  {a₁} (⇓a₁ : a? ⇓ a₁) {a₂} (⇓a₂ : a? ⇓ a₂) → 
  a₁ ≡ a₂
⇓-det now⇓ now⇓ = refl
⇓-det (later⇓ ⇓a₁) (later⇓ ⇓a₂) = ⇓-det ⇓a₁ ⇓a₂
