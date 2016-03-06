module BasicSystem.StabilityAndCompleteness where

open import BasicSystem.Utils
open import BasicSystem.DelayMonad
open import BasicSystem.Syntax
open import BasicSystem.Normalizer
open import BasicSystem.StrongComp


--
-- Stability: nf ⌜ n ⌝ ≡ n .
--

stable : ∀ {α} (u : Nf α) → nf ⌜ u ⌝ ≡ u

stable K0 = refl
stable (K1 u)
  rewrite stable u
  = refl
stable S0 = refl
stable (S1 u)
  rewrite stable u
  = refl
stable (S2 u v) = begin
  nf (S ∙ ⌜ u ⌝ ∙ ⌜ v ⌝)
    ≡⟨⟩
  S2 (nf ⌜ u ⌝) (nf ⌜ v ⌝)
    ≡⟨ cong₂ S2 (stable u) (stable v) ⟩
  S2 u v
  ∎
  where open ≡-Reasoning


--
-- Completeness: x ≈ norm x
-- (Terms are convertible to their normal forms.)
--

complete : ∀ {α} (x : Tm α) → x ≈ norm x

complete K = ≈refl
complete S = ≈refl
complete (x ∙ y)
  with all-sc x | inspect all-sc x | all-sc y | inspect all-sc y
... | u , p , ⇓u | ≡[ all-sc-x≡ ] | v , q , ⇓v | ≡[ all-sc-y≡ ]
  with all-sc (x ∙ y) | p v q
... | w , pq , ⇓w | w′ , pq′ , ⇓w′ , ≈w′
  rewrite ⇓-det ⇓w′ (⇓bind2 _⟨∙⟩_ ⇓u ⇓v ⇓w)
  = begin
  x ∙ y
    ≈⟨ ≈cong∙ (complete x) (complete y) ⟩
  norm x ∙ norm y
    ≡⟨ cong₂ _∙_ (cong (⌜_⌝ ∘ proj₁) all-sc-x≡)
                 (cong (⌜_⌝ ∘ proj₁) all-sc-y≡) ⟩
  ⌜ u ⌝ ∙ ⌜ v ⌝
    ≈⟨ ≈w′ ⟩
  ⌜ w ⌝
  ∎
  where open ≈-Reasoning

