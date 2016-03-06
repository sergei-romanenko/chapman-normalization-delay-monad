module BasicSystem.Soundness where

open import BasicSystem.Utils
open import BasicSystem.DelayMonad
open import BasicSystem.Syntax
open import BasicSystem.Normalizer
open import BasicSystem.StrongComp


--
-- Soundness: the normal forms of two convertible terms are equal
--     x₁ ≈ x₂ → nf x₁ ≡ nf x₂
--

sound : ∀ {α} {x y : Tm α} → x ≈ y → nf x ≡ nf y

sound ≈refl = refl
sound (≈sym y≈x) =
  sym $ sound y≈x
sound (≈trans x≈y y≈z) =
  trans (sound x≈y) (sound y≈z)
sound ≈K = refl
sound ≈S = refl
sound (≈cong∙ {α} {β} {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂)
  with sound x₁≈x₂ | sound y₁≈y₂
... | u₁≡u₂ | v₁≡v₂
  with all-sc x₁ | all-sc x₂ | all-sc y₁ | all-sc y₂
... | u₁ , p₁ , ⇓u₁ | u₂ , p₂ , ⇓u₂ | v₁ , q₁ , ⇓v₁ | v₂ , q₂ , ⇓v₂
  with p₁ v₁ q₁ | p₂ v₂ q₂
... | w₁ , r₁ , ⇓w₁ , ≈w₁ | w₂ , r₂ , ⇓w₂ , ≈w₂
  rewrite u₁≡u₂ | v₁≡v₂
  = ⇓-det ⇓w₁ ⇓w₂
