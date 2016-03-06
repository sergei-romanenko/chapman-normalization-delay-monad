module BasicSystem.Examples where

open import BasicSystem.Utils
open import BasicSystem.DelayMonad
open import BasicSystem.Syntax
open import BasicSystem.Normalizer
open import BasicSystem.StrongComp

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Convertibility.
--

III≈I : III ≈ I
III≈I = begin
  S ∙ K ∙ K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈cong∙ ≈refl ≈S ⟩
  (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K)))
    ≈⟨ ≈cong∙ ≈refl ≈K ⟩
  (S ∙ K ∙ K) ∙ (S ∙ K ∙ K)
    ≈⟨ ≈S ⟩
  K ∙ (S ∙ K ∙ K) ∙ (K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈K ⟩
  S ∙ K ∙ K
  ∎
  where open ≈-Reasoning

III≈I′ : III ≈ I
III≈I′ = begin
  (S ∙ K ∙ K) ∙ ((S ∙ K ∙ K) ∙ (S ∙ K ∙ K))
    ≈⟨ ≈S ⟩
  (K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K))) ∙ (K ∙ (S ∙ K ∙ K ∙ (S ∙ K ∙ K)))
    ≈⟨ ≈K ⟩
  (S ∙ K ∙ K) ∙ (S ∙ K ∙ K)
    ≈⟨ ≈S ⟩
  (K ∙ (S ∙ K ∙ K)) ∙ (K ∙ (S ∙ K ∙ K))
    ≈⟨ ≈K ⟩
  S ∙ K ∙ K
  ∎
  where open ≈-Reasoning


--
-- Normalization with the delay monad.
--

⟦III⟧ : ⟦ III ⟧ ≡
  later (∞S K0 K0 (S2 K0 K0) ∞>>= (λ w → later (∞S K0 K0 w)))
⟦III⟧ = refl

⟦III⟧⇓ : ⟦ III ⟧ ⇓ S2 K0 K0
⟦III⟧⇓ = later⇓ (later⇓ now⇓)

norm?-III⇓ : norm? III ⇓ (S ∙ K ∙ K)
norm?-III⇓ = later⇓ (later⇓ now⇓)

--
-- Total (terminating) normalization.
--

all-sc-III : all-sc III ≡
  S2 K0 K0 ,
  (λ w r → w , r ,
       later⇓ now⇓ ,
       ≈trans ≈S (≈trans (≈cong∙ ≈refl ≈refl) (≈trans ≈K ≈refl))) ,
  later⇓ (later⇓ now⇓)

all-sc-III = refl

nf-III : nf III ≡ S2 K0 K0
nf-III = refl

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl
